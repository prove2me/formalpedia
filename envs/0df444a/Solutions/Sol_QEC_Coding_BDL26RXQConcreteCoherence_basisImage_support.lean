-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.basisImage_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:10:17.996629+00:00
-- url     : https://prove2.me/submissions/fdae292e-0446-4218-9a8f-54fc03ee83fa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_mem_iff
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
theorem _root_.solution (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    hammingSupport (basisImage S depth i q)=
      BDL26RXQBlockTransport.twoCopyIncidentZ S depth i h q := by
  ext p
  constructor
  · intro hp
    obtain ⟨z,copy,hz,hv⟩ := (basisImage_mem_iff S depth i h q p).mp hp
    apply Finset.mem_image.mpr
    exact ⟨(z,copy),Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,Finset.mem_univ _⟩,hv⟩
  · intro hp
    obtain ⟨⟨z,copy⟩,hz,hv⟩ := Finset.mem_image.mp hp
    exact (basisImage_mem_iff S depth i h q p).mpr
      ⟨z,copy,(Finset.mem_filter.mp (Finset.mem_product.mp hz).1).2,hv⟩
end QEC.Coding.BDL26RXQConcreteCoherence
