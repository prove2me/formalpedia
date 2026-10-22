-- Prove2me | solution 1 for TradingPostNSW.Leontief.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:05:39.179136+00:00
-- url     : https://prove2.me/submissions/9347bada-8336-458c-9af3-274974088291

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

theorem solution {n m : ℕ} (I : Instance n m) (hI : Standing I) (p : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (i : Fin n) (hφ : 0 < phi I i p) :
    IsGreatest {t : ℝ | ∃ y : Fin m → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, p j * y j ≤ I.B i ∧ t = u I i y}
      (I.B i / phi I i p) := by
  have hB : 0 ≤ I.B i := le_trans zero_le_one (hI.one_le_B i)
  constructor
  · refine ⟨fun j => (I.B i / phi I i p) * I.v i j, ?_, ?_, ?_⟩
    · intro j; exact mul_nonneg (div_nonneg hB hφ.le) (hI.v_nonneg i j)
    · apply le_of_eq
      have : ∑ j, p j * (I.B i / phi I i p * I.v i j) = I.B i / phi I i p * phi I i p := by
        unfold phi; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [this, div_mul_cancel₀ _ hφ.ne']
    · rw [u_scale I hI]
  · rintro t ⟨y, hy0, hc, rfl⟩
    rw [le_div_iff₀ hφ]
    exact le_trans (u_mul_phi_le I hI i p hp y hy0) hc

