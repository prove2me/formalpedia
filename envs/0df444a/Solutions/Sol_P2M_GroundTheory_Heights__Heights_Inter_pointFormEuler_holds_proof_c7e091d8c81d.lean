-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_proof_c7e091d8c81d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:33.603746+00:00
-- url     : https://prove2.me/submissions/c05a3832-148f-4cf0-b2b5-2ad70fc94dbe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_cxHessian_mulVec_star_3f977e456929
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_logh_contDiffAt_620c52edbdfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_logh_bsmul_6baf0808a0d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_comp_holo_7a1539b9bd8f

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
namespace GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
theorem _root_.solution : pointFormEuler_holds.Statement := by
  intro K _ ι _ A n F y x c hA hF hblk hx
  have hφ : ContDiffAt ℝ 2 (fun z' => Real.log (A.h z')) (F y) := logh_contDiffAt hA hblk
  have hchain : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => Real.log (A.h (F y')))) y u v =
      fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ (fun z' => Real.log (A.h z')) (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) :=
    fun u v => hess_comp_holo (φ := fun z' => Real.log (A.h z')) hφ hF u v
  have hG : DifferentiableAt ℂ (fun y' => fderiv ℂ F y' x) y :=
    hF.fderiv.differentiableAt.clm_apply (differentiableAt_const x)
  have hGI : fderiv ℂ (fun y' => fderiv ℂ F y' (Complex.I • x)) y =
      Complex.I • fderiv ℂ (fun y' => fderiv ℂ F y' x) y := by
    have : (fun y' => fderiv ℂ F y' (Complex.I • x)) = fun y' => Complex.I • fderiv ℂ F y' x := by
      funext y'
      exact map_smul _ _ _
    rw [this, fderiv_fun_const_smul hG]
  have hJIx : fderiv ℂ F y (Complex.I • x) = bsmul (fun k => Complex.I * c k) (F y) := by
    rw [map_smul, hx]
    funext p
    simp only [Pi.smul_apply, bsmul, smul_eq_mul]
    ring
  have hbI : ∀ (d : K → ℂ) (w : (Σ k, ι k) → ℂ),
      bsmul d (Complex.I • w) = bsmul (fun k => Complex.I * d k) w := by
    intro d w
    funext p
    simp only [Pi.smul_apply, bsmul, smul_eq_mul]
    ring
  have hbII : ∀ (d : K → ℂ) (w : (Σ k, ι k) → ℂ),
      bsmul (fun k => Complex.I * d k) (Complex.I • w) = -bsmul d w := by
    intro d w
    funext p
    simp only [Pi.smul_apply, Pi.neg_apply, bsmul, smul_eq_mul]
    linear_combination (d p.1 * w p) * Complex.I_sq
  have hII : ∀ w : (Σ k, ι k) → ℂ, Complex.I • Complex.I • w = -w := fun w => by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have heul := fun d w => hess_logh_bsmul A hA d hblk w
  funext i
  rw [cxHessian_mulVec_star, Pi.zero_apply]
  unfold leviOf
  rw [hchain, hchain, hchain, hchain, hJIx, hx, hGI]
  simp only [map_smul, _root_.smul_apply]
  rw [heul, heul, heul, heul, hbII, hbI, hII]
  simp only [map_neg]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
