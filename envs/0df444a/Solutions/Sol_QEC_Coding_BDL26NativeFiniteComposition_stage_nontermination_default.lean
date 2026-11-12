-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.stage_nontermination_default
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:45:49.934675+00:00
-- url     : https://prove2.me/submissions/08be7a40-e67d-4ed3-8867-d4072462c58e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stageCost_nonhalting
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_nonhalting
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_joint_nontermination_default
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stageCost_nonhalting
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
namespace QEC.Coding.BDL26NativeFiniteComposition
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : ¬stageHalts p N i z) :
    stageCost p N i z=∞ ∧
    nativeHaltTime (perturbationOddScale p) i.val (stageInput p N i z)
      (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)=0 ∧
    nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z)=
      (fun v => (tableAt p N i z) ((SR.decode (perturbationOddScale p) i.val).symm v,0)) := by
  have hdefault := joint_nontermination_default (perturbationOddScale p) i.val
    (stageInput p N i z) (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z) h
  exact ⟨stageCost_nonhalting p N i z h,hdefault.2.1,hdefault.2.2⟩
end QEC.Coding.BDL26NativeFiniteComposition
