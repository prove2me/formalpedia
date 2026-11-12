-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.oldZ_pair_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:04:10.40741+00:00
-- url     : https://prove2.me/submissions/18bb71c7-1e2f-4abe-9cbd-0dd14142e1d1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQConcreteCoherence
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData (cqComponentTotal)
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26AlternatingCochain
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge
  (tannerCoboundary0 tannerCoboundary1 tannerCoboundary1_canonicalBasis_apply)
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXQConcreteCoherence
theorem _root_.solution (h : i.val%2=0) (z : (state S i.val).presentation.Z) :
    ((rxData S depth i h).induced.zPairEquiv (z,0)).val ≠
      ((rxData S depth i h).induced.zPairEquiv (z,1)).val := by
  intro he
  have hp := (rxData S depth i h).induced.zPairEquiv.injective (Subtype.ext he)
  exact (show (0 : Fin 2)≠1 by decide) (congrArg Prod.snd hp)
end QEC.Coding.BDL26RXQConcreteCoherence
