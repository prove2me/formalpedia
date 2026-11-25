-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mConeMap_eq_eval__a0f62726315a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:54.060396+00:00
-- url     : https://prove2.me/submissions/3ee7404f-8f30-4bf6-9a6b-c8b8178527ab

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
    mConeMap y f = eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1) f := by
  have h : (mConeMap y : MRing ι →+* MvPolynomial B Ω) =
      eval₂Hom (Int.castRingHom (MvPolynomial B Ω)) (fun p => C (y p) * X p.1) :=
    MvPolynomial.ringHom_ext (fun a => by simp [mConeMap]) (fun p => by simp [mConeMap])
  exact RingHom.congr_fun h f
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
