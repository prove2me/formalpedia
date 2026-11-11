-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.stageVertices_le_qubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:42:00.834999+00:00
-- url     : https://prove2.me/submissions/f11a1a2f-ab16-43c6-8ff8-b6644df2d001

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_operation_input_size_le_qubits


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26ReplacementMaterialization
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Fintype.card (Vertex (StagePresentation p n)) ≤ 65*stageQubits p n := by
  have h := operation_input_size_le_qubits (StagePresentation p n)
    (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible
    (state_boundedValence (perturbationOddScale p) n)
  change _ ≤ 65*Fintype.card (StagePresentation p n).Q
  omega
end QEC.Coding.BDL26ReplacementMaterialization
