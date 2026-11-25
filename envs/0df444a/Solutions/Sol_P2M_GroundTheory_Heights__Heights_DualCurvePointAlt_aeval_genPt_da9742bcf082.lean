-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_genPt_da9742bcf082
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:43.017365+00:00
-- url     : https://prove2.me/submissions/c65e79cf-8f2c-437b-91fe-8018b27b5ecc

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
theorem _root_.solution (W : Ideal (MRing ι)) (f : MRing ι) :
    eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.Inter.genPt W) f =
      algebraMap (MRing ι ⧸ W) (IndefiniteRowSideFullHecke.Inter.FnField W) (Ideal.Quotient.mk W f) := by
  have h : eval₂Hom (Int.castRingHom (IndefiniteRowSideFullHecke.Inter.FnField W)) (IndefiniteRowSideFullHecke.Inter.genPt W) =
      (algebraMap (MRing ι ⧸ W) (IndefiniteRowSideFullHecke.Inter.FnField W)).comp (Ideal.Quotient.mk W) :=
    MvPolynomial.ringHom_ext (fun a => by simp) (fun p => by simp [IndefiniteRowSideFullHecke.Inter.genPt])
  exact RingHom.congr_fun h f
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
