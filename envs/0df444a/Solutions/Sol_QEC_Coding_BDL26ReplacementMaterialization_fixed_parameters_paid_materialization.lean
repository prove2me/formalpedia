-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.fixed_parameters_paid_materialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:33.050185+00:00
-- url     : https://prove2.me/submissions/5c99dc2a-fb2a-4697-8f8c-6a464f9b3134

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_measurable_extendedTotalCost
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_finite_on_success
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26ReplacementMaterialization
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N,
      Measurable (extendedTotalCost p N) ∧
      (∫⁻ z, extendedTotalCost p N z ∂experimentLaw p N) ≤
        (((operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2)*
          (stageQubits p N+1)^11 : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ extendedTotalCost p N z < ∞ := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p,fun N => ⟨measurable_extendedTotalCost p N,extendedTotalCost_integral_le p N,?_⟩⟩
  filter_upwards [finiteSuccess_ae p N] with z h
  exact ⟨h,extendedTotalCost_finite_on_success p N z h⟩
end QEC.Coding.BDL26ReplacementMaterialization
