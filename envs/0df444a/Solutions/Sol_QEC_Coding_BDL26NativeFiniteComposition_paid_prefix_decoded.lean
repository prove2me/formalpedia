-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.paid_prefix_decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:46:16.426185+00:00
-- url     : https://prove2.me/submissions/76ddba4f-662a-42dc-9919-37bbba918346

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_scan_refinement
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_prefix_refinement
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_encoded_decoded
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_code_scan_refinement
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_prefix_original
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
noncomputable section
namespace QEC.Coding.BDL26NativeFiniteComposition
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
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
namespace Paid
private theorem choice_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0≤r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    choice S n I r lambda K T m = eraseChoice S n (rowMap S n I) r
      (BDL26NativeGeometricExecution.choice S n (rowMap S n I) hr lambda K T m) := by
  unfold choice BDL26NativeGeometricExecution.choice
  rw [(prefix_refinement S n I hr lambda K T m).1,
    (scan_refinement S n I r lambda K _).1,
    BDL26NativeGeometricJointExecution.code_scan_refinement]
end Paid
namespace Decoded
end Decoded
namespace Paid
end Paid
end QEC.Coding.BDL26NativeFiniteComposition
end
end

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
theorem _root_.solution (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0≤r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (Paid.prefixQ S n I r lambda K T m).value.1 =
      sampleRows S n T (fun a => counters (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n (rowMap S n I) r) (B S n (rowMap S n I) r lambda K)
        (decodedTable S n T) m (SR.decode S n a)) ∧
    (Paid.prefixQ S n I r lambda K T m).value.2 =
      (originalTrace S n (rowMap S n I) r lambda K (decodedTable S n T) m).map
        (Option.map (originalCode S n (rowMap S n I) r)) ∧
    Paid.choice S n I r lambda K T m =
      (selected (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n (rowMap S n I) r) (B S n (rowMap S n I) r lambda K)
        (decodedTable S n T) m).map (originalCode S n (rowMap S n I) r) := by
  have h := native_prefix_original S n (rowMap S n I) hr lambda K (decodedTable S n T) m
  rw [encoded_decoded] at h
  have hp := Paid.prefix_refinement S n I hr lambda K T m
  exact ⟨hp.1.trans h.2.2,hp.2.1.trans h.2.1,
    (Paid.choice_refinement S n I hr lambda K T m).trans h.1⟩
end QEC.Coding.BDL26NativeFiniteComposition
