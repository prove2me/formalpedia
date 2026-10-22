-- Prove2me | solution 1 for TradingPostNSW.Leontief.eps_me_sum_price_eq_total_budget
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:05:38.24618+00:00
-- url     : https://prove2.me/submissions/c0b49051-e417-4373-9d1a-ac8498cc4db2

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TPmarketAux
open TradingPostNSW.Leontief

variable {n m : ℕ}

lemma mem_D (I : Instance n m) (i : Fin n) (j : Fin m) : j ∈ D I i ↔ 0 < I.v i j := by
  simp [D]

lemma u_eq (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) :
    u I i y = (D I i).inf' (hI.D_nonempty i) (fun j => y j / I.v i j) := by
  simp [u, hI.D_nonempty i]

lemma u_le (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) (j : Fin m)
    (hj : j ∈ D I i) : u I i y ≤ y j / I.v i j := by
  rw [u_eq I hI]; exact Finset.inf'_le _ hj

lemma le_u (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) (t : ℝ)
    (h : ∀ j ∈ D I i, t ≤ y j / I.v i j) : t ≤ u I i y := by
  rw [u_eq I hI]; exact Finset.le_inf' _ _ h

lemma u_nonneg (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ)
    (hy : ∀ j, 0 ≤ y j) : 0 ≤ u I i y :=
  le_u I hI i y 0 (fun j _ => div_nonneg (hy j) (hI.v_nonneg i j))

lemma u_mul_le (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ)
    (hy : ∀ j, 0 ≤ y j) (j : Fin m) : u I i y * I.v i j ≤ y j := by
  by_cases hj : j ∈ D I i
  · have hv := (mem_D I i j).1 hj
    have := u_le I hI i y j hj
    rwa [le_div_iff₀ hv] at this
  · have hv : I.v i j = 0 := by
      have := hI.v_nonneg i j
      rw [mem_D] at hj; linarith
    rw [hv, mul_zero]; exact hy j

lemma u_scale (I : Instance n m) (hI : Standing I) (i : Fin n) (T : ℝ) :
    u I i (fun j => T * I.v i j) = T := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := hI.D_nonempty i
    have := u_le I hI i (fun j => T * I.v i j) j hj
    have hv := (mem_D I i j).1 hj
    simpa [mul_div_assoc, div_self hv.ne'] using this
  · apply le_u I hI
    intro j hj
    have hv := (mem_D I i j).1 hj
    rw [mul_div_assoc, div_self hv.ne', mul_one]

/-- Lower bound `u(y) φ_i(p) ≤ p · y`. -/
lemma u_mul_phi_le (I : Instance n m) (hI : Standing I) (i : Fin n) (p : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (y : Fin m → ℝ) (hy : ∀ j, 0 ≤ y j) :
    u I i y * phi I i p ≤ ∑ j, p j * y j := by
  unfold phi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have := u_mul_le I hI i y hy j
  nlinarith [hp j]

end TPmarketAux

open TradingPostNSW.Leontief TPmarketAux

theorem solution {n m : ℕ} (I : Instance n m) (ε : ℝ)
    (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) (hI : Standing I) (hME : IsEpsME I ε p x) :
    ∑ j, p j = ∑ i, I.B i := by
  have h1 : ∀ j, p j = ∑ i, x i j * p j := by
    intro j
    rcases (hME.p_nonneg j).lt_or_eq with h | h
    · rw [← Finset.sum_mul, hME.sold j h, one_mul]
    · rw [← h]; simp
  calc ∑ j, p j = ∑ j, ∑ i, x i j * p j := Finset.sum_congr rfl (fun j _ => h1 j)
    _ = ∑ i, ∑ j, x i j * p j := Finset.sum_comm
    _ = ∑ i, I.B i := Finset.sum_congr rfl (fun i _ => hME.budget i)

