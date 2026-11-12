-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_finiteObservation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:35:38.836915+00:00
-- url     : https://prove2.me/submissions/0e81f0a4-cf15-4ea1-8b79-7c974b33d777

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_stageCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_totalCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_stageTrace
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_paidHistory_original
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_history
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageCost


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (finiteObservation p N) := by
  have hh : Measurable (paidHistory p N) := by
    have he : paidHistory p N = history p N := funext (paidHistory_original p N)
    rw [he]
    exact measurable_history p N
  exact hh.prodMk ((measurable_pi_lambda _ (fun i => measurable_stageTrace p N i)).prodMk
    ((measurable_pi_lambda _ (fun i => measurable_stageCost p N i)).prodMk (measurable_totalCost p N)))
end QEC.Coding.BDL26PaidRowsComposition
