-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_parent_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:22:57.303104+00:00
-- url     : https://prove2.me/submissions/8348ce88-0190-4610-863a-5870fafe88c8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_physicalQ_parent
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionRegion_chart_iff
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
    (q : (state S i.val).presentation.Q) (p : FamilyQ S depth i.succ) :
    p ∈ (rxLq S depth i h).correctionRegion q ↔
      parent S (i.val+1) (Vertex.q p)=some (Vertex.q q) := by
  obtain ⟨r,rfl⟩ := (rxPhysicalQEquiv S depth i h).surjective p
  rw [correctionRegion_chart_iff,physicalQ_parent]
  rcases r with ⟨x,e⟩ | ⟨r,v⟩
  · constructor <;> intro he <;> cases he
  · constructor
    · intro he
      have hrq : r=q := Vertex.q.inj he
      exact congrArg (fun t => some (Vertex.q t)) hrq
    · intro he
      have hrq : r=q := Vertex.q.inj (Option.some.inj he)
      exact congrArg Vertex.q hrq
end QEC.Coding.BDL26RXQConcreteCoherence
