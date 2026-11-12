-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.stageCost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:56:17.664888+00:00
-- url     : https://prove2.me/submissions/6d56e7b9-9094-4e03-94f0-acdda1b5f3a5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_composedStageQuery_cost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_inputRows_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26PaidRowsComposition
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) (z : Experiment p N) :
    stageCost p N i z = rowStageCost p N i z+
      ((stageMaterializationCost p N i z+
        3*Fintype.card (Vertex (StagePresentation p (i.val+1))) : ℕ) : ℝ≥0∞) := by
  rw [stageCost,inputRows_eq,composedStageQuery_cost]
  rfl
end QEC.Coding.BDL26PaidRowsComposition
