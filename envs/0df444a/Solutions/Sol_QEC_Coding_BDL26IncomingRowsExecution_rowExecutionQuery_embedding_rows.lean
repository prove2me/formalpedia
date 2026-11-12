-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowExecutionQuery_embedding_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:20:37.364097+00:00
-- url     : https://prove2.me/submissions/a3eebd09-ec85-4fa2-991c-4356c3a0f897

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowExecutionQuery_rows
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actual_emitted_embedding_rows


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton
namespace QEC.Coding.BDL26IncomingRowsExecution
theorem _root_.solution (P : TannerSquarePresentation) (I : StateRows P)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) :
    (rowExecutionQuery P I (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T).1 =
      (vertexInputList P).map (fun v => (v,perturbationEmbeddingOutput P (statePoints I) p T v)) := by
  rw [rowExecutionQuery_rows]
  exact actual_emitted_embedding_rows P (statePoints I) p T
end QEC.Coding.BDL26IncomingRowsExecution
