-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eval_coneMap_ad771fde0cea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:35.778444+00:00
-- url     : https://prove2.me/submissions/34e6f355-535f-4eaf-9e94-27a7ee366b90

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
    Polynomial.eval₂ incl (Xk 0) (coneMap ℤ y f) = algebraMap _ Kfr f := by
  have h : (Polynomial.eval₂RingHom incl (Xk 0)).comp (coneMap ℤ y).toRingHom =
      algebraMap (MRing (GlobalTheory (Fin 2))) Kfr := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) (fun p => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coneMap, aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    exact incl_y_mul p
  exact congrArg (fun φ : MRing (GlobalTheory (Fin 2)) →+* Kfr => φ f) h
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
