-- Prove2me | solution 1 for QEC.Locality.inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:14:35.94421+00:00
-- url     : https://prove2.me/submissions/5b49db2e-a811-4de7-82c9-002e52476cde

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Locality_inBinaryNormalizer_of_commutes_generators
import Theorems.Thm_QEC_Locality_commutes_restrictBinaryTo_generator_of_no_cross_edge
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_symmetric


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B)
    (hnoCross : P.fixedGeneratorNoCrossEdge (A : Set ι) (B : Set ι))
    (hdecompose : E.vector =
      (restrictBinaryTo A E).vector + (restrictBinaryTo B E).vector)
    (hE : P.code.1.InBinaryNormalizer E) :
    P.code.1.InBinaryNormalizer (restrictBinaryTo A E) ∧
      P.code.1.InBinaryNormalizer (restrictBinaryTo B E) := by
  have hA := inBinaryNormalizer_of_commutes_generators P (restrictBinaryTo A E)
    (fun j => commutes_restrictBinaryTo_generator_of_no_cross_edge
      P A B E hdisjoint hnoCross hdecompose j
      (hE (P.generators j) (by
        rw [← P.generated_eq]
        exact GeneratedStabilizer.generator j)))
  refine ⟨hA, ?_⟩
  have hnoCrossBA : P.fixedGeneratorNoCrossEdge (B : Set ι) (A : Set ι) := by
    intro b hb a ha hba
    exact hnoCross ha hb (P.fixedGeneratorInteractionGraph_symmetric hba)
  apply inBinaryNormalizer_of_commutes_generators P (restrictBinaryTo B E)
  intro j
  apply commutes_restrictBinaryTo_generator_of_no_cross_edge
    P B A E hdisjoint.symm hnoCrossBA
    (hdecompose.trans (add_comm _ _)) j
  exact hE (P.generators j) (by
    rw [← P.generated_eq]
    exact GeneratedStabilizer.generator j)
end QEC.Locality
