-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.fixed_parameters_common_paid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:26:23.302462+00:00
-- url     : https://prove2.me/submissions/a9784c80-f40f-49e7-85e0-e76374156d1b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_streamObservation
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_common_paid_ae
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_measure
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurableSet_allFiniteSuccess
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


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
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L,
      (∀ N, Measurable (streamObservation p N) ∧
        (∫⁻ omega, streamTotalCost p N omega ∂BDL26CountableEmbeddingExperiment.streamLaw p) ≤
          (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2+195)*
            (stageQubits p N+1)^12 : ℕ) : ℝ≥0∞)) ∧
      MeasurableSet (BDL26CountableEmbeddingExperiment.allFiniteSuccess p) ∧
      BDL26CountableEmbeddingExperiment.streamLaw p (BDL26CountableEmbeddingExperiment.allFiniteSuccess p) = 1 ∧
      ∀ᵐ omega ∂BDL26CountableEmbeddingExperiment.streamLaw p,
        omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p ∧
        (∀ N, streamTotalCost p N omega < ∞) ∧
        (∀ n, PhysicalSuccessorFacts p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)) ∧
        ∀ n, PhysicalGeometry (perturbationOddScale p) n
          (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  exact ⟨p,fun N => ⟨measurable_streamObservation p N,streamTotalCost_integral_le p N⟩,
    BDL26CountableEmbeddingExperiment.measurableSet_allFiniteSuccess p,
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_measure p,common_paid_ae p⟩
end QEC.Coding.BDL26PaidRowsComposition
