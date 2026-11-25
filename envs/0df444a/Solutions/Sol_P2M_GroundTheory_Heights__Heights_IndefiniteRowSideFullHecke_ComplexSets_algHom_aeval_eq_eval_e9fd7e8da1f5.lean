-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algHom_aeval_eq_eval_e9fd7e8da1f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:12:06.230689+00:00
-- url     : https://prove2.me/submissions/b3d5a705-5f15-4cf9-b509-404b834cade8

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionCoordinateEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionCoordinateEquation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type*} {B : Type*} [CommRing B] [Algebra ℂ B] (e : B →ₐ[ℂ] ℂ)
    (v : σ → B) (P : MvPolynomial σ ℂ) : e (aeval v P) = eval (fun i => e (v i)) P := by
  rw [← AlgHom.comp_apply, comp_aeval]
  exact RingHom.congr_fun (coe_aeval_eq_eval _) P
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
