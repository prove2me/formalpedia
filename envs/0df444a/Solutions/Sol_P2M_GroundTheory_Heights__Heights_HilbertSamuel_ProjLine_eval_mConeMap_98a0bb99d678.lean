-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eval_mConeMap_98a0bb99d678
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:36.870232+00:00
-- url     : https://prove2.me/submissions/02b08573-a72c-4171-be7e-7df52522a280

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_incl_y_mul_279e0f8187fe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_zero
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_one

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
theorem _root_.solution (f : MRing (GlobalTheory (Fin 2))) :
    MvPolynomial.eval₂ incl (fun _ => Xk 0) (mConeMap y f) = algebraMap _ Kfr f := by
  have h : (MvPolynomial.eval₂Hom incl (fun _ : Unit => Xk 0)).comp (mConeMap y).toRingHom =
      algebraMap (MRing (GlobalTheory (Fin 2))) Kfr := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) (fun p => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      mConeMap, aeval_X, coe_eval₂Hom, eval₂_mul, eval₂_C, eval₂_X]
    exact incl_y_mul p
  exact congrArg (fun φ : MRing (GlobalTheory (Fin 2)) →+* Kfr => φ f) h
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
