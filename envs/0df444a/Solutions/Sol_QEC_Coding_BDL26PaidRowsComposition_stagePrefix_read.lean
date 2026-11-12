-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.stagePrefix_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:04:06.912196+00:00
-- url     : https://prove2.me/submissions/51ed0b06-c79d-4bbd-af39-e54a5ba37548

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stagePrefixRows_rep
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateRowQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexInputList_complete

section
noncomputable section
namespace QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
private theorem rep_read (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P))
    (R : StateRows P) (h : StateRowsRep P T c R) (v : Vertex P) :
    (stateRowQuery v R).1 = (c v,T (v,c v)) := by
  apply stateRowQuery_value v R
  · intro row hr he
    subst v
    exact h.2 row hr
  · have hv := vertexInputList_complete P v
    rw [← h.1,List.mem_map] at hv
    exact hv
end QEC.Coding.BDL26PaidRowsComposition
end
end

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) (v : Vertex (StagePresentation p i.val)) :
    (stateRowQuery v (stagePrefixRows p N i time z)).1 =
      (stageCounters p N i time z v,(tableAt p N i z) (v,stageCounters p N i time z v)) :=
  rep_read _ _ _ _ (stagePrefixRows_rep p N i time z) v
end QEC.Coding.BDL26PaidRowsComposition
