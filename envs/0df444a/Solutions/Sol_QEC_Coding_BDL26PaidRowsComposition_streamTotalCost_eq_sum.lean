-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:43:37.595008+00:00
-- url     : https://prove2.me/submissions/62fc7226-92cc-4080-a787-ae6ecb7a10a3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_eq_sum
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamStageCost_finite_prefix
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_finite_prefix
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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamTotalCost p N omega = ∑ i : Fin N, streamStageCost p i.val omega := by
  rw [streamTotalCost_finite_prefix,totalCost_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => (streamStageCost_finite_prefix p N i omega).symm)
end QEC.Coding.BDL26PaidRowsComposition
