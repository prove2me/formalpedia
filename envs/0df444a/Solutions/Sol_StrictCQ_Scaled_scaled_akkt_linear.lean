-- Prove2me | solution 1 for StrictCQ.Scaled.scaled_akkt_linear
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:21:15.187856+00:00
-- url     : https://prove2.me/submissions/58da7d24-a703-498f-b18a-f1b45edf5cb1

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
  have hg : ∀ y, gradient (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) y = c := by
    intro y
    have hf : (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) = ⇑(innerSL ℝ c) := by
      funext x; simp [real_inner_comm]
    have hd : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) (innerSL ℝ c) y := by
      rw [hf]; exact (innerSL ℝ c).hasFDerivAt
    have e : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) c = innerSL ℝ c := by
      first | rfl | (ext v; simp)
    have : HasGradientAt (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) c y := by
      rw [hasGradientAt_iff_hasFDerivAt, e]; exact hd
    exact this.gradient
  refine ⟨fun _ => xs, fun k => (k : ℝ) • l, fun k => (k : ℝ) • u, tendsto_const_nhds, ?_, ?_, ?_⟩
  · intro k j
    exact mul_nonneg (Nat.cast_nonneg k) (hu j)
  · intro j
    have : ∀ k : ℕ, min (((k : ℝ) • u) j) (-(C.g j xs)) = 0 := by
      intro k
      by_cases hj : C.g j xs = 0
      · simp only [hj, neg_zero, Pi.smul_apply, smul_eq_mul]
        exact min_eq_right (mul_nonneg (Nat.cast_nonneg k) (hu j))
      · have h1 : u j = 0 := hcomp j hj
        have h2 : C.g j xs ≤ 0 := hxs.2 j
        simp only [h1, Pi.smul_apply, smul_eq_mul, mul_zero]
        exact min_eq_left (by linarith)
    simp_rw [this]
    exact tendsto_const_nhds
  · have hres : ∀ k : ℕ, gradient (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, c⟫_ℝ) xs +
        ∑ i, ((k : ℝ) • l) i • gradient (C.h i) xs +
        ∑ j, ((k : ℝ) • u) j • gradient (C.g j) xs = c := by
      intro k
      rw [hg]
      have : ∑ i, ((k : ℝ) • l) i • gradient (C.h i) xs +
          ∑ j, ((k : ℝ) • u) j • gradient (C.g j) xs =
          (k : ℝ) • (∑ i, l i • gradient (C.h i) xs + ∑ j, u j • gradient (C.g j) xs) := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, smul_add]
      rw [add_assoc, this, h24]
      simp
    have hnk : ∀ k : ℕ, max ‖(k : ℝ) • l‖ ‖(k : ℝ) • u‖ = k := by
      intro k
      rw [norm_smul, norm_smul, Real.norm_natCast, ← mul_max_of_nonneg _ _ (Nat.cast_nonneg k), hnorm,
        mul_one]
    simp_rw [hres, hnk]
    have h1 : Tendsto (fun k : ℕ => (max 1 (k : ℝ))⁻¹) atTop (𝓝 0) := by
      apply tendsto_inv_atTop_zero.comp
      exact tendsto_atTop_mono (fun k => le_max_right _ _) tendsto_natCast_atTop_atTop
    simpa using h1.mul_const ‖c‖
