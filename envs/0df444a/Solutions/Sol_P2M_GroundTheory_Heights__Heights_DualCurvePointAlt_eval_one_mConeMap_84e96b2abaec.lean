-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_eval_one_mConeMap_84e96b2abaec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:46.853017+00:00
-- url     : https://prove2.me/submissions/ee8bea7f-057a-422d-8e24-8bbe20bb28d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualCurvePointAlt
variable {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)]
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    MvPolynomial.eval (fun _ => (1 : Ω)) (mConeMap y f) = eval₂ (Int.castRingHom Ω) y f := by
  have h : (MvPolynomial.eval (fun _ : B => (1 : Ω))).comp (mConeMap y : MRing ι →+* MvPolynomial B Ω) =
      eval₂Hom (Int.castRingHom Ω) y :=
    MvPolynomial.ringHom_ext (fun a => by simp [mConeMap]) (fun p => by simp [mConeMap])
  exact RingHom.congr_fun h f
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
