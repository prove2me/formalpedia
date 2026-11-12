-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:30:03.784215+00:00
-- url     : https://prove2.me/submissions/3b136c4b-1cb0-4e3d-9c1d-c3cae6fd5b1b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_totalCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_finite_prefix
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_law
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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, streamTotalCost p N omega ∂BDL26CountableEmbeddingExperiment.streamLaw p) =
      ∫⁻ z, totalCost p N z ∂experimentLaw p N := by
  calc
    _ = ∫⁻ omega, totalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega)
        ∂BDL26CountableEmbeddingExperiment.streamLaw p := lintegral_congr (streamTotalCost_finite_prefix p N)
    _ = ∫⁻ z, totalCost p N z ∂(BDL26CountableEmbeddingExperiment.streamLaw p).map
        (BDL26CountableEmbeddingExperiment.truncate p N) :=
      (lintegral_map (measurable_totalCost p N) (BDL26CountableEmbeddingExperiment.measurable_truncate p N)).symm
    _ = _ := by rw [BDL26CountableEmbeddingExperiment.truncate_law]
end QEC.Coding.BDL26PaidRowsComposition
