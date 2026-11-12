-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_totalCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:19:01.496329+00:00
-- url     : https://prove2.me/submissions/b7f7864a-fc35-4af7-bf83-8a6bf613d285

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_eq_sum
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_stageCost
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
    Measurable (totalCost p N) := by
  have he : totalCost p N = fun z => ∑ i : Fin N, stageCost p N i z :=
    funext (totalCost_eq_sum p N)
  rw [he]
  exact Finset.measurable_sum Finset.univ (fun i _ => measurable_stageCost p N i)
end QEC.Coding.BDL26PaidRowsComposition
