-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowUniverseQuery_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:32:16.901205+00:00
-- url     : https://prove2.me/submissions/e756a941-ce54-4cca-984a-4c11b7b6f292

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowUniverseQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventUniverseQuery_value


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
    {r : ℝ} (hr : 0 ≤ r) : (rowUniverseQuery P I hr).1=
      (Finset.univ : Finset (Event P (statePoints I) r)).sort (eventPriorityLE P (statePoints I) r) := by
  rw [rowUniverseQuery_value]
  exact eventUniverseQuery_value P (statePoints I) hr
end QEC.Coding.BDL26IncomingRowsExecution
