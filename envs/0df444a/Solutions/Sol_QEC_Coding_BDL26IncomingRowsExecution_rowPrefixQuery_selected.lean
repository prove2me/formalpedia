-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowPrefixQuery_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:18:36.543729+00:00
-- url     : https://prove2.me/submissions/13c1a338-d47d-4134-ac13-36cd30f66e84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowUniverseQuery_value
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowScanQuery_value
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowPrefixQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualPrefixQuery_rep
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualScanQuery_value


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
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (s : ℕ) :
    (rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1
      (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 T s).1).1=
      selected (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T s := by
  rw [rowUniverseQuery_value,rowScanQuery_value,rowPrefixQuery_value]
  exact actualScanQuery_value P (statePoints I) hr lambda K T _ _
    (actualPrefixQuery_rep P (statePoints I) hr lambda K T s)
end QEC.Coding.BDL26IncomingRowsExecution
