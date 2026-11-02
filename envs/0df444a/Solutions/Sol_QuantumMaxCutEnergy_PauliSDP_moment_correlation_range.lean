-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.moment_correlation_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T04:15:12.156954+00:00
-- url     : https://prove2.me/submissions/305ec187-5775-4d57-8825-eaf72841b756

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib

/-!
# The level-2 correlation range for a single edge

For a feasible level-`k` (`k ≥ 2`) Pauli-moment solution `L`, the three two-body
moments on one edge satisfy `-3 ≤ L(XX) + L(YY) + L(ZZ) ≤ 1`.  The upper bound is
`QuantumMaxCutEnergy.PauliSDP.moment_correlation_bound`; the lower bound is new
here and is what pins the campaign per-edge quantities

  `c_e = (1 - ΣL)/2 ∈ [0, 2]`,  `s_e = -(ΣL)/3 ∈ [-1/3, 1]`,

the exact domains of the cubic scalar certificates (`lp24_strict_scalar`,
`gss25_strict_scalar`).  All four bounds come from the same 4×4 principal block of
the moment Gram with rows `{1, XX, YY, ZZ}`: the quadratic forms at
`(1,-1,-1,-1)` give `ΣL ≤ 1`, and those at `(1,1,-1,1)`, `(1,-1,1,1)`,
`(1,1,1,-1)` — each equal to `4 + 4·(odd combination)` — sum to `ΣL ≥ -3`.

## The level-2 correlation bound for a single edge

For a feasible level-`k` (`k ≥ 2`) Pauli-moment solution `L`, the three two-body
moments on one edge satisfy `L(XX) + L(YY) + L(ZZ) ≤ 1`.  The proof reads the
four words `{1, XX, YY, ZZ}` off the moment Gram (a 4×4 principal block with the
phase structure of the Pauli algebra) and tests positive semidefiniteness on the
vector `(1, -1, -1, -1)`, whose quadratic form is `4(1 - L(XX) - L(YY) - L(ZZ))`.
-/

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

theorem moment_correlation_range {n k : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (hL : Feasible k L)
    (i j : Fin n) (hij : i ≠ j) :
    -(3 : ℝ) ≤ L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) ∧
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
  -- symmetry of the block
  have hs : ∀ a b : Fin 4, ((realGram k L).submatrix e e) a b =
      ((realGram k L).submatrix e e) b a := by
    intro a b
    have h := h4.isHermitian.apply a b
    simp only [star_trivial] at h
    first | exact h | exact h.symm
  -- x = (1,-1,-1,-1): the upper bound ΣL ≤ 1
  set xU : Fin 4 → ℝ := fun t => if t = 0 then 1 else -1 with hxU
  have hqU := h4.dotProduct_mulVec_nonneg xU
  have hU0 : xU 0 = 1 := by simp [hxU]
  have hU1 : xU 1 = -1 := by
    simp only [hxU]
    rw [if_neg (by decide)]
  have hU2 : xU 2 = -1 := by
    simp only [hxU]
    rw [if_neg (by decide)]
  have hU3 : xU 3 = -1 := by
    simp only [hxU]
    rw [if_neg (by decide)]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    Pi.star_apply, star_trivial, hU0, hU1, hU2, hU3] at hqU
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2,
    g00, g01, g02, g03, g11, g12, g13, g22, g23, g33] at hqU
  -- x = (1,1,-1,1): gives 4 + 4(L(XX) + L(ZZ) - L(YY)) ≥ 0
  set xA : Fin 4 → ℝ := fun t => if t = 0 ∨ t = 1 ∨ t = 3 then 1 else -1 with hxA
  have hqA := h4.dotProduct_mulVec_nonneg xA
  have hA0 : xA 0 = 1 := by simp [hxA]
  have hA1 : xA 1 = 1 := by simp [hxA]
  have hA2 : xA 2 = -1 := by
    simp only [hxA]
    rw [if_neg (by decide)]
  have hA3 : xA 3 = 1 := by simp [hxA]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    Pi.star_apply, star_trivial, hA0, hA1, hA2, hA3] at hqA
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2,
    g00, g01, g02, g03, g11, g12, g13, g22, g23, g33] at hqA
  -- x = (1,-1,1,1): gives 4 + 4(L(YY) + L(ZZ) - L(XX)) ≥ 0
  set xB : Fin 4 → ℝ := fun t => if t = 0 ∨ t = 2 ∨ t = 3 then 1 else -1 with hxB
  have hqB := h4.dotProduct_mulVec_nonneg xB
  have hB0 : xB 0 = 1 := by simp [hxB]
  have hB1 : xB 1 = -1 := by
    simp only [hxB]
    rw [if_neg (by decide)]
  have hB2 : xB 2 = 1 := by simp [hxB]
  have hB3 : xB 3 = 1 := by simp [hxB]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    Pi.star_apply, star_trivial, hB0, hB1, hB2, hB3] at hqB
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2,
    g00, g01, g02, g03, g11, g12, g13, g22, g23, g33] at hqB
  -- x = (1,1,1,-1): gives 4 + 4(L(XX) + L(YY) - L(ZZ)) ≥ 0
  set xC : Fin 4 → ℝ := fun t => if t = 0 ∨ t = 1 ∨ t = 2 then 1 else -1 with hxC
  have hqC := h4.dotProduct_mulVec_nonneg xC
  have hC0 : xC 0 = 1 := by simp [hxC]
  have hC1 : xC 1 = 1 := by simp [hxC]
  have hC2 : xC 2 = 1 := by simp [hxC]
  have hC3 : xC 3 = -1 := by
    simp only [hxC]
    rw [if_neg (by decide)]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    Pi.star_apply, star_trivial, hC0, hC1, hC2, hC3] at hqC
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2,
    g00, g01, g02, g03, g11, g12, g13, g22, g23, g33] at hqC
  exact ⟨by linarith [hqA, hqB, hqC], by linarith [hqU]⟩

/-- The campaign edge value `c_e = (1 - L(XX) - L(YY) - L(ZZ))/2` of a feasible
level-`k` (`k ≥ 2`) solution lies in `[0, 2]`. -/
theorem edgeValue_range {n k : ℕ} (hk : 2 ≤ k) (L : Word n → ℝ) (hL : Feasible k L)
    (e : Edge n) :
    0 ≤ (1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2 ∧
      (1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2 ≤ 2 := by
  have hij : e.val.1 ≠ e.val.2 := by have h := e.property; omega
  have hsum : L (fun t => if t = e.val.1 ∨ t = e.val.2 then 1 else 0) +
      L (fun t => if t = e.val.1 ∨ t = e.val.2 then 2 else 0) +
      L (fun t => if t = e.val.1 ∨ t = e.val.2 then 3 else 0) =
      L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e) := rfl
  obtain ⟨hl, hu⟩ := moment_correlation_range hk L hL e.val.1 e.val.2 hij
  rw [hsum] at hl hu
  constructor <;> linarith

/-- The campaign edge parameter `s_e = -(L(XX) + L(YY) + L(ZZ))/3` of a feasible
level-`k` (`k ≥ 2`) solution lies in `[-1/3, 1]`, and the edge value is
`c_e = (1 + 3 s_e)/2`.  This is the exact domain on which the cubic scalar
certificates `lp24_strict_scalar` and `gss25_strict_scalar` are stated. -/
theorem edgeParam_range {n k : ℕ} (hk : 2 ≤ k) (L : Word n → ℝ) (hL : Feasible k L)
    (e : Edge n) :
    -(1 / 3) ≤ -(L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e)) / 3 ∧
      -(L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e)) / 3 ≤ 1 ∧
      (1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2 =
        (1 + 3 * (-(L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e)) / 3)) / 2 := by
  have hij : e.val.1 ≠ e.val.2 := by have h := e.property; omega
  have hsum : L (fun t => if t = e.val.1 ∨ t = e.val.2 then 1 else 0) +
      L (fun t => if t = e.val.1 ∨ t = e.val.2 then 2 else 0) +
      L (fun t => if t = e.val.1 ∨ t = e.val.2 then 3 else 0) =
      L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e) := rfl
  obtain ⟨hl, hu⟩ := moment_correlation_range hk L hL e.val.1 e.val.2 hij
  rw [hsum] at hl hu
  refine ⟨by linarith, by linarith, by ring⟩

end QuantumMaxCutEnergy.PauliSDP

theorem solution {n k : ℕ} (hk : 2 ≤ k) (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L) (i j : Fin n) (hij : i ≠ j) :
    -(3 : ℝ) ≤ L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) ∧
      L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) ≤ 1 :=
  QuantumMaxCutEnergy.PauliSDP.moment_correlation_range hk L hL i j hij
