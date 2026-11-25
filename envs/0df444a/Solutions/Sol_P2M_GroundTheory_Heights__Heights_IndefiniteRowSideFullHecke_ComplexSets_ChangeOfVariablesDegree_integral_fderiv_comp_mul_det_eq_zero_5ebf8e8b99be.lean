-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_fderiv_comp_mul_det_eq_zero_5ebf8e8b99be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:40.812944+00:00
-- url     : https://prove2.me/submissions/5625b500-3129-4c0a-a2c2-74a93634e816

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasCompactSupport_comp_sub_6ff964a89034
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_clm_apply_eq_sum_b184b9b21943
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_fderiv_eq_det_jacobian_2f5e8fc08a22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_det_fderiv_eq_zero_65eb4a12eacd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_jacobian_eq_fderiv_apply_78ebb9abef90


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory Metric
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
theorem _root_.solution (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (g : (Fin (m + 1) → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det = 0 := by
  obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
  set H : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ := fun x => Function.update (φ x) 0 (g (φ x))
    with hH
  have hH0 : (fun x => H x 0) = fun x => g (φ x) := by
    funext x; simp [hH]
  have hHk : ∀ k, k ≠ 0 → (fun x => H x k) = fun x => φ x k := by
    intro k hk; funext x; simp [hH, hk]
  have hHs : ContDiff ℝ ∞ H := by
    refine contDiff_pi.2 fun k => ?_
    by_cases hk : k = 0
    · subst hk; rw [hH0]; exact hg.comp hφ
    · rw [hHk k hk]; exact (contDiff_apply ℝ ℝ k).comp hφ
  have hHc : HasCompactSupport fun x => H x 0 := by
    rw [hH0]
    simpa using hasCompactSupport_comp_sub φ C hC g hgc 0
  have hdet : ∀ x, (fderiv ℝ H x).det =
      fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det := by
    intro x
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
    have hgd : DifferentiableAt ℝ g (φ x) := (hg.differentiable (by simp)) (φ x)
    set c : Fin (m + 1) → ℝ := fun k => fderiv ℝ g (φ x) (Pi.single k 1) with hc
    have hJ : Matrix.of (jacobian H x) = (Matrix.of (jacobian φ x)).updateRow 0
        (∑ k, c k • (Matrix.of (jacobian φ x)) k) := by
      ext r l
      rw [Matrix.of_apply, jacobian_eq_fderiv_apply H x ((hHs.differentiable (by simp)) x)]
      by_cases hr : r = 0
      · subst hr
        rw [hH0, Matrix.updateRow_self]
        have : fderiv ℝ (fun y => g (φ y)) x = (fderiv ℝ g (φ x)).comp (fderiv ℝ φ x) :=
          fderiv_comp x hgd hφd
        rw [this, ContinuousLinearMap.comp_apply, clm_apply_eq_sum]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, hc]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [jacobian, mul_comm]
      · rw [hHk r hr, Matrix.updateRow_ne hr, Matrix.of_apply,
          jacobian_eq_fderiv_apply φ x hφd]
    rw [det_fderiv_eq_det_jacobian, hJ, Matrix.det_updateRow_sum, det_fderiv_eq_det_jacobian,
      smul_eq_mul]
  simp_rw [← hdet]
  exact integral_det_fderiv_eq_zero H hHs 0 hHc
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
