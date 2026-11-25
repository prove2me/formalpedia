-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_logh_bsmul_6baf0808a0d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:13.941231+00:00
-- url     : https://prove2.me/submissions/4d5ac562-a11f-4a31-9949-de9280e7e303

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_logh_contDiffAt_620c52edbdfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_bsmulCLM_apply_681aa974daec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_fderiv_logh_bsmul_524bae19d6b0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
theorem _root_.solution (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) z w (bsmul d z) =
      -fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d w) := by
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z' => Real.log (A.h z')
  set L : ((Σ k, ι k) → ℂ) →L[ℝ] ((Σ k, ι k) → ℂ) := (bsmulCLM d).restrictScalars ℝ
  have hL : ∀ v, L v = bsmul d v := fun v => bsmulCLM_apply d v
  have hconst : (fun z' => fderiv ℝ φ z' (L z')) =ᶠ[𝓝 z]
      fun _ => deriv (fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k)) 0 := by
    filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'
    rw [hL]
    exact fderiv_logh_bsmul A hA d hz'
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((logh_contDiffAt hA hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h0 : fderiv ℝ (fun z' => fderiv ℝ φ z' (L z')) z w = 0 := by
    rw [hconst.fderiv_eq]
    simp
  rw [fderiv_clm_apply hd1 L.differentiableAt, L.fderiv] at h0
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hL] at h0
  linarith
end GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
