-- Prove2me | solution 2 for StrictCQ.Scaled.scaled_akkt_linear
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:22:42.107045+00:00
-- url     : https://prove2.me/submissions/4be2e699-2f47-4f91-bac1-307a6721d943

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace
open StrictCQ.Scaled

theorem solution {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (l : Fin m → ℝ) (u : Fin p → ℝ) (hu : ∀ j, 0 ≤ u j) (hcomp : ∀ j, C.g j xs ≠ 0 → u j = 0)
    (hnorm : max ‖l‖ ‖u‖ = 1)
    (h24 : ∑ i, l i • gradient (C.h i) xs + ∑ j, u j • gradient (C.g j) xs = 0)
    (c : EuclideanSpace ℝ (Fin n)) :
    C.ScaledAKKT (fun x => ⟪x, c⟫_ℝ) xs := by
  have hg : gradient (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) xs = c := by
    have h : HasGradientAt (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) c xs := by
      rw [hasGradientAt_iff_hasFDerivAt]
      have := (innerSL ℝ c).hasFDerivAt (x := xs)
      have e : (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) = fun x => ⟪c, x⟫_ℝ := by
        funext x; exact real_inner_comm _ _
      rw [e]
      exact this
    exact h.gradient
  refine ⟨fun _ => xs, fun k => (k : ℝ) • l, fun k => (k : ℝ) • u, tendsto_const_nhds, ?_, ?_, ?_⟩
  · intro k j
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (Nat.cast_nonneg k) (hu j)
  · intro j
    have : ∀ k : ℕ, min (((k : ℝ) • u) j) (-(C.g j xs)) = 0 := by
      intro k
      by_cases hj : C.g j xs = 0
      · rw [hj]
        have : 0 ≤ ((k : ℝ) • u) j := by
          simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (Nat.cast_nonneg k) (hu j)
        rw [neg_zero]; exact min_eq_right this
      · have h0 := hcomp j hj
        have hle : C.g j xs ≤ 0 := hxs.2 j
        have : 0 < -(C.g j xs) := by
          have := lt_of_le_of_ne hle hj
          linarith
        simp [h0, this.le]
    simp only [this]
    exact tendsto_const_nhds
  · have e : ∀ k : ℕ, ‖gradient (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) xs +
        ∑ i, ((k : ℝ) • l) i • gradient (C.h i) xs + ∑ j, ((k : ℝ) • u) j • gradient (C.g j) xs‖ = ‖c‖ := by
      intro k
      have : ∑ i, ((k : ℝ) • l) i • gradient (C.h i) xs + ∑ j, ((k : ℝ) • u) j • gradient (C.g j) xs = 0 := by
        have := congrArg (fun w => (k : ℝ) • w) h24
        simp only [smul_add, smul_zero, Finset.smul_sum, smul_smul] at this
        simpa [Pi.smul_apply, smul_eq_mul] using this
      rw [hg, add_assoc, this, add_zero]
    have e2 : ∀ k : ℕ, max 1 (max ‖(k : ℝ) • l‖ ‖(k : ℝ) • u‖) = max 1 (k : ℝ) := by
      intro k
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg k), ← mul_max_of_nonneg _ _ (Nat.cast_nonneg k), hnorm, mul_one]
    simp only [e, e2]
    have h1 : Tendsto (fun k : ℕ => (max 1 (k : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun k => le_max_right _ _) tendsto_natCast_atTop_atTop)
    simpa using h1.mul_const ‖c‖
