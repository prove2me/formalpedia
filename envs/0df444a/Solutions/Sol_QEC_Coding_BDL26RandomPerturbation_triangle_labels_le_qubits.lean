-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangle_labels_le_qubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:53:53.217641+00:00
-- url     : https://prove2.me/submissions/89b523ac-1c2b-4ec9-b546-c1031ac9e8b2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
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
    (hv : BoundedValence P) : Fintype.card (Triangle P) ≤ 65*Fintype.card P.Q := by
  have h := input_labels_le_qubits P A hv
  omega
end QEC.Coding.BDL26RandomPerturbation
