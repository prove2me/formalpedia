-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.physicalQ_incident
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:25:57.984402+00:00
-- url     : https://prove2.me/submissions/f9833934-4a39-4b3e-8bb6-da3361d75d77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_chart_incidence

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalStarTransport
theorem _root_.solution (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    (state S (i.val+1)).presentation.qz (physicalQ S depth i odd q v)
      (qCentre S depth i odd q z hqz v)=true := by
  rw [physicalQ,qCentre,chart_incidence]
  change decide (∃ h : (Old S depth i).qz q z=true,
    qToZDoubleCylinderVertex (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible
      q z h S v=qToZDoubleCylinderVertex (Old S depth i)
        (state S i.val).admissible.toTannerSquareAdmissible q z hqz S v)=true
  exact decide_eq_true ⟨hqz,rfl⟩
end QEC.Coding.BDL26RZPhysicalStarTransport
