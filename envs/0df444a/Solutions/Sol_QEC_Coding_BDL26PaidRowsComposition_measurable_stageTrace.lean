-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_stageTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:27:28.38722+00:00
-- url     : https://prove2.me/submissions/f382f28b-8d6b-419c-9fd8-c6dad85edf1f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stageTrace_original
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurableSet_stageHalts
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageCounters
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageGeometricOutput
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageHaltTime
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePerturbedOutput
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePhysicalOutput
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageSelected
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_tableAt

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
private theorem measurable_stage_samples {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (time : ℕ) :
    Measurable (fun z : Experiment p N => fun v => (tableAt p N i z) (v,stageCounters p N i time z v)) := by
  apply measurable_pi_lambda
  intro v
  have lookup : Measurable (fun w : StageTables p i.val × ℕ => w.1 (v,w.2)) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply (v,k))
  exact lookup.comp ((measurable_tableAt p N i).prodMk
    ((measurable_pi_apply v).comp (measurable_stageCounters p N i time)))
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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    Measurable (stageTrace p N i) := by
  have he : stageTrace p N i = originalStageTrace p N i := funext (stageTrace_original p N i)
  rw [he]
  exact (measurable_pi_lambda _ (fun time => measurable_stageCounters p N i time)).prodMk
    ((measurable_pi_lambda _ (fun time => measurable_stageSelected p N i time)).prodMk
    ((measurable_pi_lambda _ (fun time => measurable_stage_samples p N i time)).prodMk
    ((Measurable.ite (measurableSet_stageHalts p N i) measurable_const measurable_const).prodMk
    ((measurable_stageHaltTime p N i).prodMk ((measurable_stageGeometricOutput p N i).prodMk
    ((measurable_stagePerturbedOutput p N i).prodMk (measurable_stagePhysicalOutput p N i)))))))
end QEC.Coding.BDL26PaidRowsComposition
