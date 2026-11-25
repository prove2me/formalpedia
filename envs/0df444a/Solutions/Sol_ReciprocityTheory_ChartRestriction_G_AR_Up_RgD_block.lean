-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgD.block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:05:08.984376+00:00
-- url     : https://prove2.me/submissions/b3f5f195-a9b9-4fb2-a0f3-685c5da5cfa9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgC_quad_contDiff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgC_levi_quad_nonpos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgC_Q_formula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgC_posDef_swap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhD_cd_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgB_amgm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgB_exists_factor
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgD
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
variable {f p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgD
theorem _root_.solution (hm : 0 < min p q) {v0 : V (nD f p q)} (hv0 : v0 ∈ Dset f p q) (k : Fin f) :
    ∃ Q : V (nD f p q) → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ ξ, (leviV (nD f p q) (fun y => (Q y : ℂ)) v0 ξ).re ≤ 0) ∧
      Q v0 = (min p q : ℕ) ∧
      ∀ v ∈ Dset f p q, dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) ≤
        dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q v / (min p q : ℕ)) := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq] at hm ⊢
    have hA0 := hv0 k
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - Zof v k * (Zof v k)ᴴ) * (1 - Zof v0 k * (Zof v0 k)ᴴ)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞ (fun v : V (nD f p q) => (y * Zof v k) a b) := by
      intro a b
      simp only [Matrix.mul_apply, Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re -
        ∑ a, ∑ b, Complex.normSq ((fun a b (v : V (nD f p q)) => (y * Zof v k) a b) a b v) := by
      funext v; simp only [hQdef]; rw [hy, Q_formula]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      exact RgB.amgm hm (hv k) hA0
  · rw [min_eq_right hqp] at hm ⊢
    have hA0 := posDef_swap (hv0 k)
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - (Zof v k)ᴴ * Zof v k) * (1 - (Zof v0 k)ᴴ * Zof v0 k)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞
        (fun v : V (nD f p q) => ∑ c, star (y a c) * Zof v k b c) := by
      intro a b
      simp only [Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq
        ((fun a b (v : V (nD f p q)) => ∑ c, star (y a c) * Zof v k b c) a b v) := by
      funext v
      simp only [hQdef]
      have h1 := Q_formula (Zof v k)ᴴ y
      rw [Matrix.conjTranspose_conjTranspose] at h1
      rw [hy, h1]
      congr 1
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← Complex.normSq_conj]
      congr 1
      simp [Matrix.mul_apply, conjTranspose_apply, map_sum, Complex.star_def, mul_comm]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      have h := RgB.amgm hm (posDef_swap (hv k)) hA0
      simp only [dk]
      rw [Matrix.det_one_sub_mul_comm, Matrix.det_one_sub_mul_comm (Zof v0 k)]
      exact h
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgD
