-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.no_actual_top_Z_marked_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:46:15.807736+00:00
-- url     : https://prove2.me/submissions/12392082-f72d-4656-98f7-53e32267a7a4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_top_marks_are_Z
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_no_marked_neighbor
import Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_no_marked_neighbor
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
private theorem zVertex_eq (S : OddScale) (n : Nat) (z : (state S n).presentation.Z) :
    zVertex S n z = @Vertex.z (state S n).presentation z := rfl
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
end

set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (z : (state S 3).presentation.Z)
    (hparent : parent S 3 (zVertex S 3 z) = none)
    (w : BDL26CanonicalHistoryMarks.Node S 2)
    (hw : w ∈ BDL26CanonicalHistoryMarks.marks S 2 sigma) :
    ¬ (decodingGraph S 4).adjacent (actualTopNode S (zVertex S 3 z)) w := by
  have hm : BDL26UniformTopOwnerIsolation.TopMarksAreZ S 3
      (BDL26CanonicalHistoryMarks.marks S 2 sigma) := by
    intro v hv
    obtain ⟨z,hz⟩ := actual_top_marks_are_Z S sigma v hv
    exact ⟨z,hz.trans (zVertex_eq S 3 z)⟩
  exact BDL26UniformTopOwnerIsolation.no_marked_neighbor S 3
    (BDL26CanonicalHistoryMarks.marks S 2 sigma) hm z hparent w hw
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
