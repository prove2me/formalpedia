-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_stream_process
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:45:17.336119+00:00
-- url     : https://prove2.me/submissions/d4c38dd5-e4e2-4b6f-a85f-6dba3d161dab

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_streamStageCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_streamTotalCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_streamStageTrace
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamStageCost


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : BDL26CountableEmbeddingExperiment.Omega p =>
      (fun n => streamStageTrace p n omega,fun n => streamStageCost p n omega,
       fun N => streamTotalCost p N omega)) :=
  (measurable_pi_lambda _ (fun n => measurable_streamStageTrace p n)).prodMk
    ((measurable_pi_lambda _ (fun n => measurable_streamStageCost p n)).prodMk
      (measurable_pi_lambda _ (fun N => measurable_streamTotalCost p N)))
end QEC.Coding.BDL26PaidRowsComposition
