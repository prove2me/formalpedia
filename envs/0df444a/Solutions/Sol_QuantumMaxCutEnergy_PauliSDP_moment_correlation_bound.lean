-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.moment_correlation_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T18:51:02.377892+00:00
-- url     : https://prove2.me/submissions/c3e88b13-d508-4f77-8d3a-a438f37844dc

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib

open scoped BigOperators

namespace QuantumMaxCutEnergy.PauliSDP

/-! ### Table evaluations -/

private lemma localPhase_zero_left (b : Label) : localPhase 0 b = 1 := by
  fin_cases b <;> rfl

private lemma localPhase_zero_right (a : Label) : localPhase a 0 = 1 := by
  fin_cases a <;> rfl

private lemma localPhase_self (a : Label) : localPhase a a = 1 := by
  fin_cases a <;> rfl

private lemma localProduct_zero_left (b : Label) : localProduct 0 b = b := by
  fin_cases b <;> rfl

private lemma localProduct_self (a : Label) : localProduct a a = 0 := by
  fin_cases a <;> rfl

private lemma localPhase_12 : localPhase 1 2 = Complex.I := rfl
private lemma localPhase_13 : localPhase 1 3 = -Complex.I := rfl
private lemma localPhase_23 : localPhase 2 3 = Complex.I := rfl
private lemma localProduct_12 : localProduct 1 2 = 3 := rfl
private lemma localProduct_13 : localProduct 1 3 = 2 := rfl
private lemma localProduct_23 : localProduct 2 3 = 1 := rfl

private lemma prod_two_point {n : ℕ} {v : ℂ} {i j : Fin n} (hij : i ≠ j) :
    ∏ t : Fin n, (if t = i ∨ t = j then v else 1) = v * v := by
  classical
  have hF : Finset.univ.filter (fun t : Fin n => t = i ∨ t = j) = {i, j} := by
    ext t
    simp
  have hrest : ∏ t ∈ Finset.univ.filter (fun t : Fin n => ¬ (t = i ∨ t = j)),
      (if t = i ∨ t = j then v else 1) = 1 := by
    refine Finset.prod_eq_one (fun t ht => ?_)
    exact if_neg (Finset.mem_filter.mp ht).2
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ)
    (fun t : Fin n => t = i ∨ t = j), hF, Finset.prod_pair hij, hrest]
  simp

private lemma wordPhase_twoBody {n : ℕ} (a b : Label) (ha : a ≠ 0) (hb : b ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    wordPhase (fun t => if t = i ∨ t = j then a else 0)
      (fun t => if t = i ∨ t = j then b else 0) = localPhase a b * localPhase a b := by
  unfold wordPhase
  have hp : ∀ t : Fin n,
      localPhase (if t = i ∨ t = j then a else 0) (if t = i ∨ t = j then b else 0) =
        (if t = i ∨ t = j then localPhase a b else 1) := by
    intro t
    by_cases h : t = i ∨ t = j
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h, localPhase_zero_left]
  simp only [hp]
  exact prod_two_point hij (v := localPhase a b)

/-! ### The correlation bound -/

theorem moment_correlation_bound {n k : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (hL : Feasible k L)
    (i j : Fin n) (hij : i ≠ j) :
    L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) ≤ 1 := by
  classical
  set w1 : Word n := (fun t => if t = i ∨ t = j then 1 else 0) with hw1
  set w2 : Word n := (fun t => if t = i ∨ t = j then 2 else 0) with hw2
  set w3 : Word n := (fun t => if t = i ∨ t = j then 3 else 0) with hw3
  set w0 : Word n := identityWord n with hw0
  -- support bounds
  have hsub : ∀ w ∈ ({w1, w2, w3} : Finset (Word n)), support w ⊆ {i, j} := by
    intro w hw t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rw [hw1] at ht
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      by_contra hc
      exact ht (if_neg (by simpa using hc))
    · rw [hw2] at ht
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      by_contra hc
      exact ht (if_neg (by simpa using hc))
    · rw [hw3] at ht
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      by_contra hc
      exact ht (if_neg (by simpa using hc))
  have hcard2 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
    have h := Finset.card_insert_le i ({j} : Finset (Fin n))
    simpa using h
  have hs2 : ∀ w ∈ ({w1, w2, w3} : Finset (Word n)), (support w).card ≤ k := by
    intro w hw
    have h1 : (support w).card ≤ ({i, j} : Finset (Fin n)).card :=
      Finset.card_le_card (hsub w hw)
    omega
  have hs0 : (support w0).card ≤ k := by
    rw [hw0]
    simp [support, identityWord]
  let e : Fin 4 → Index n k :=
    ![⟨w0, hs0⟩, ⟨w1, hs2 w1 (by simp)⟩, ⟨w2, hs2 w2 (by simp)⟩, ⟨w3, hs2 w3 (by simp)⟩]
  have h4 : ((realGram k L).submatrix e e).PosSemidef := hL.2.submatrix e
  -- Gram entries
  have g00 : ((realGram k L).submatrix e e) 0 0 = 1 := by
    show (wordPhase w0 w0).re * L (wordProduct w0 w0) = 1
    have hp : wordPhase w0 w0 = 1 := by
      unfold wordPhase
      refine Finset.prod_eq_one (fun t _ => ?_)
      rw [hw0, identityWord, localPhase_zero_left]
    have hpr : wordProduct w0 w0 = identityWord n := by
      funext t
      simp only [hw0, wordProduct, identityWord, localProduct_zero_left]
    rw [hp, hpr, hL.1]
    norm_num
  have g01 : ((realGram k L).submatrix e e) 0 1 = L w1 := by
    show (wordPhase w0 w1).re * L (wordProduct w0 w1) = L w1
    have hp : wordPhase w0 w1 = 1 := by
      unfold wordPhase
      refine Finset.prod_eq_one (fun t _ => ?_)
      rw [hw0, identityWord, localPhase_zero_left]
    have hpr : wordProduct w0 w1 = w1 := by
      funext t
      simp only [hw0, wordProduct, identityWord, localProduct_zero_left]
    rw [hp, hpr]
    norm_num
  have g02 : ((realGram k L).submatrix e e) 0 2 = L w2 := by
    show (wordPhase w0 w2).re * L (wordProduct w0 w2) = L w2
    have hp : wordPhase w0 w2 = 1 := by
      unfold wordPhase
      refine Finset.prod_eq_one (fun t _ => ?_)
      rw [hw0, identityWord, localPhase_zero_left]
    have hpr : wordProduct w0 w2 = w2 := by
      funext t
      simp only [hw0, wordProduct, identityWord, localProduct_zero_left]
    rw [hp, hpr]
    norm_num
  have g03 : ((realGram k L).submatrix e e) 0 3 = L w3 := by
    show (wordPhase w0 w3).re * L (wordProduct w0 w3) = L w3
    have hp : wordPhase w0 w3 = 1 := by
      unfold wordPhase
      refine Finset.prod_eq_one (fun t _ => ?_)
      rw [hw0, identityWord, localPhase_zero_left]
    have hpr : wordProduct w0 w3 = w3 := by
      funext t
      simp only [hw0, wordProduct, identityWord, localProduct_zero_left]
    rw [hp, hpr]
    norm_num
  have g11 : ((realGram k L).submatrix e e) 1 1 = 1 := by
    show (wordPhase w1 w1).re * L (wordProduct w1 w1) = 1
    have hp : wordPhase w1 w1 = 1 := by
      unfold wordPhase
      refine Finset.prod_eq_one (fun t _ => ?_)
      rw [hw1, localPhase_self]
    have hpr : wordProduct w1 w1 = identityWord n := by
      funext t
      simp only [hw1, wordProduct, identityWord]
      by_cases h : t = i ∨ t = j
      · simp [h, localProduct_self]
      · simp [h, localProduct_zero_left]
    rw [hp, hpr, hL.1]
    norm_num
  have g12 : ((realGram k L).submatrix e e) 1 2 = -L w3 := by
    show (wordPhase w1 w2).re * L (wordProduct w1 w2) = -L w3
    have hp : wordPhase w1 w2 = -1 := by
      rw [hw1, hw2]
      rw [wordPhase_twoBody 1 2 (by decide) (by decide) i j hij, localPhase_12]
      norm_num [Complex.ext_iff]
    have hpr : wordProduct w1 w2 = w3 := by
      funext t
      simp only [hw1, hw2, hw3, wordProduct]
      by_cases h : t = i ∨ t = j
      · simp [h, localProduct_12]
      · simp [h, localProduct_zero_left]
    rw [hp, hpr]
    norm_num
  have g13 : ((realGram k L).submatrix e e) 1 3 = -L w2 := by
    show (wordPhase w1 w3).re * L (wordProduct w1 w3) = -L w2
    have hp : wordPhase w1 w3 = -1 := by
      rw [hw1, hw3]
      rw [wordPhase_twoBody 1 3 (by decide) (by decide) i j hij, localPhase_13]
      norm_num [Complex.ext_iff]
    have hpr : wordProduct w1 w3 = w2 := by
      funext t
      simp only [hw1, hw3, hw2, wordProduct]
      by_cases h : t = i ∨ t = j
      · simp [h, localProduct_13]
      · simp [h, localProduct_zero_left]
    rw [hp, hpr]
    norm_num
  have g22 : ((realGram k L).submatrix e e) 2 2 = 1 := by
    show (wordPhase w2 w2).re * L (wordProduct w2 w2) = 1
    have hp : wordPhase w2 w2 = 1 := by
      unfold wordPhase
      refine Finset.prod_eq_one (fun t _ => ?_)
      rw [hw2, localPhase_self]
    have hpr : wordProduct w2 w2 = identityWord n := by
      funext t
      simp only [hw2, wordProduct, identityWord]
      by_cases h : t = i ∨ t = j
      · simp [h, localProduct_self]
      · simp [h, localProduct_zero_left]
    rw [hp, hpr, hL.1]
    norm_num
  have g23 : ((realGram k L).submatrix e e) 2 3 = -L w1 := by
    show (wordPhase w2 w3).re * L (wordProduct w2 w3) = -L w1
    have hp : wordPhase w2 w3 = -1 := by
      rw [hw2, hw3]
      rw [wordPhase_twoBody 2 3 (by decide) (by decide) i j hij, localPhase_23]
      norm_num [Complex.ext_iff]
    have hpr : wordProduct w2 w3 = w1 := by
      funext t
      simp only [hw2, hw3, hw1, wordProduct]
      by_cases h : t = i ∨ t = j
      · simp [h, localProduct_23]
      · simp [h, localProduct_zero_left]
    rw [hp, hpr]
    norm_num
  have g33 : ((realGram k L).submatrix e e) 3 3 = 1 := by
    show (wordPhase w3 w3).re * L (wordProduct w3 w3) = 1
    have hp : wordPhase w3 w3 = 1 := by
      unfold wordPhase
      refine Finset.prod_eq_one (fun t _ => ?_)
      rw [hw3, localPhase_self]
    have hpr : wordProduct w3 w3 = identityWord n := by
      funext t
      simp only [hw3, wordProduct, identityWord]
      by_cases h : t = i ∨ t = j
      · simp [h, localProduct_self]
      · simp [h, localProduct_zero_left]
    rw [hp, hpr, hL.1]
    norm_num
  -- the quadratic form at the vector supported as (1,-1,-1,-1)
  set x : Fin 4 → ℝ := fun t => if t = 0 then 1 else -1 with hx
  have hquad := h4.dotProduct_mulVec_nonneg x
  have hx0 : x 0 = 1 := by simp [hx]
  have hx1 : x 1 = -1 := by
    simp only [hx]
    rw [if_neg (by decide)]
  have hx2 : x 2 = -1 := by
    simp only [hx]
    rw [if_neg (by decide)]
  have hx3 : x 3 = -1 := by
    simp only [hx]
    rw [if_neg (by decide)]
  have hs : ∀ a b : Fin 4, ((realGram k L).submatrix e e) a b =
      ((realGram k L).submatrix e e) b a := by
    intro a b
    have h := h4.isHermitian.apply a b
    simp only [star_trivial] at h
    first | exact h | exact h.symm
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    Pi.star_apply, star_trivial, hx0, hx1, hx2, hx3] at hquad
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2,
    g00, g01, g02, g03, g11, g12, g13, g22, g23, g33] at hquad
  linarith [hquad]

end QuantumMaxCutEnergy.PauliSDP

/-- **The level-2 correlation bound.** -/
theorem solution {n k : ℕ} (hk : 2 ≤ k)
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L)
    (i j : Fin n) (hij : i ≠ j) :
    L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) ≤ 1 :=
  QuantumMaxCutEnergy.PauliSDP.moment_correlation_bound hk L hL i j hij

#print axioms solution
