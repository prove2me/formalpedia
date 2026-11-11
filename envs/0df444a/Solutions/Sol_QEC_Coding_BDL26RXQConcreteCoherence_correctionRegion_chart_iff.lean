-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_chart_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:14:26.156235+00:00
-- url     : https://prove2.me/submissions/ad18fa1f-6099-4685-aa31-9669e00ba4c5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionRegion_eq_raw
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
    (q : (state S i.val).presentation.Q)
    (r : RX1 (state S i.val).presentation S) :
    rxPhysicalQEquiv S depth i h r ∈ (rxLq S depth i h).correctionRegion q ↔
      rxCorrectionOwner (state S i.val).presentation S r=Vertex.q q := by
  rw [correctionRegion_eq_raw]
  constructor
  · intro hm
    obtain ⟨t,ht,he⟩ := Finset.mem_map.mp hm
    have hr : t=r := (rxPhysicalQEquiv S depth i h).injective he
    subst t
    exact (Finset.mem_filter.mp ht).2
  · intro hr
    exact Finset.mem_map.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,rfl⟩
end QEC.Coding.BDL26RXQConcreteCoherence
