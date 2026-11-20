-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.totalCost_integral_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:16:38.15191+00:00
-- url     : https://prove2.me/submissions/2fe816db-93ce-4695-bbab-56049e70dc6b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_sum
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_stageCost
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stageCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_stageCost


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeFiniteComposition
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric BDL26KeyedGeometricExecution BDL26NativeKeyExecutionBridge
open BDL26NativeGeometricExecution BDL26NativeGeometricExecutionCost
open BDL26NativeGeometricScanCost BDL26NativeGeometricJointExecution
open BDL26ReplacementMaterialization BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
namespace QEC.Coding.BDL26NativeFiniteComposition
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z,totalCost p N z ∂experimentLaw p N) ≤
      ((∑ i : Fin N,stageBudget p i.val : ℕ) : ℝ≥0∞) := by
  have he : totalCost p N = fun z => ∑ i : Fin N,stageCost p N i z :=
    funext (totalCost_sum p N)
  rw [he,lintegral_finsetSum Finset.univ (fun i _ => measurable_stageCost p N i),Nat.cast_sum]
  exact Finset.sum_le_sum (fun i _ => stageCost_integral_le p N i)
end QEC.Coding.BDL26NativeFiniteComposition
