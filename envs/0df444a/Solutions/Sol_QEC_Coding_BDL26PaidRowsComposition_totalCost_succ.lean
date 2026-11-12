-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.totalCost_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:46:45.893215+00:00
-- url     : https://prove2.me/submissions/a374345c-bbd2-402a-a145-7cabb8ec7f16

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_composedStageQuery_cost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_run_rows
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p (N+1)) :
    totalCost p (N+1) z = totalCost p N z.1+
      jointRowStageCost p N (evaluate p N z.1,z.2)+
        ((materializationCost p N (evaluate p N z.1,z.2)+
          3*Fintype.card (Vertex (StagePresentation p (N+1))) : ℕ) : ℝ≥0∞) := by
  change (run p N z.1).2+(composedStageQuery p N (run p N z.1).1 z.2).2 = _
  rw [run_rows,composedStageQuery_cost]
  exact (add_assoc _ _ _).symm
end QEC.Coding.BDL26PaidRowsComposition
