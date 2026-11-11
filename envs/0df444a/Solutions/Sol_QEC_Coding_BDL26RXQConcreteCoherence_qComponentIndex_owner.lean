-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.qComponentIndex_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:01:00.166531+00:00
-- url     : https://prove2.me/submissions/1a163bd1-43a4-48d6-a8db-c8fc080eef30

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_componentOwner_bijective
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_componentOwner_bijective
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
theorem _root_.solution (h : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) :
    componentOwner S depth i h sigma (qComponentIndex S depth i h sigma q)=.inr (.inl q) :=
  Classical.choose_spec ((componentOwner_bijective S depth i h sigma).2 (.inr (.inl q)))
end QEC.Coding.BDL26RXQConcreteCoherence
