-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.operation_input_size_le_qubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:32:24.062202+00:00
-- url     : https://prove2.me/submissions/af338448-b3ca-4eed-84f2-ae09c22221f1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertex_card
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_input_labels_le_qubits


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (hv : BoundedValence P) : Fintype.card (Vertex P)+Fintype.card (Triangle P) ≤ 65*Fintype.card P.Q := by
  rw [vertex_card]
  exact input_labels_le_qubits P A hv
end QEC.Coding.BDL26RandomPerturbation
