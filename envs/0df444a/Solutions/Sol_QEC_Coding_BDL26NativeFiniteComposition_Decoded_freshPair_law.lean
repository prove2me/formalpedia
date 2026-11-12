-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.Decoded.freshPair_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:34:04.790405+00:00
-- url     : https://prove2.me/submissions/c9ffe934-5a47-4617-8967-6c94efea57c1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
open QEC.Coding.BDL26NativeFiniteComposition.Decoded
namespace QEC.Coding.BDL26NativeFiniteComposition.Decoded
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (experimentLaw p (n+1)).map (freshPair p n) =
      (outputLaw p n).prod (freshLaw p n) := by
  have hid : Measurable (id : StageTables p n → StageTables p n) := measurable_id
  have h : (outputLaw p n).prod ((freshLaw p n).map (id : StageTables p n → StageTables p n)) =
      ((experimentLaw p n).prod (freshLaw p n)).map
        (Prod.map (evaluate p n) (id : StageTables p n → StageTables p n)) :=
    Measure.map_prod_map (experimentLaw p n) (freshLaw p n) (measurable_evaluate p n) hid
  rw [Measure.map_id] at h
  have hfun : Prod.map (evaluate p n) (id : StageTables p n → StageTables p n) = freshPair p n := by
    funext z
    rcases z with ⟨x,T⟩
    rfl
  rw [hfun] at h
  exact h.symm
end QEC.Coding.BDL26NativeFiniteComposition.Decoded
