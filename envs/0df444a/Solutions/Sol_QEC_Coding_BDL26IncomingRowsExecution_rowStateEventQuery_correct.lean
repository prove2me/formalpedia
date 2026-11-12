-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowStateEventQuery_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:32:25.477401+00:00
-- url     : https://prove2.me/submissions/88f8e1b4-b485-4fec-87b2-e9b7facb1287

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowStateEventQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateEventQuery_correct


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
    (r lambda : ℝ) (K : ℕ) (e : Event P (statePoints I) r) (R : StateRows P) :
    (rowStateEventQuery P I r lambda K e R).1=true ↔
      statePoints R ∈ localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) e := by
  rw [rowStateEventQuery_value]
  exact stateEventQuery_correct P (statePoints I) r lambda K e R
end QEC.Coding.BDL26IncomingRowsExecution
