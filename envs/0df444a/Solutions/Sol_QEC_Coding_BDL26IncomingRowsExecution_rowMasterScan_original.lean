-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowMasterScan_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:25:15.229162+00:00
-- url     : https://prove2.me/submissions/c9f32c8f-4aa6-4c79-8c00-9468bf7d4b31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowMasterUniverseQuery_original
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowMasterStateEventQuery_original
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedScan_map_pair


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
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (R : StateRows P) :
    scanQuery (rowMasterStateEventQuery P I lambda K) (rowMasterUniverseQuery P I r).1 R=
      ((rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R).1.map
        (eventToMaster P (statePoints I) r),
       (rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R).2) := by
  rw [rowMasterUniverseQuery_original P I hr]
  exact countedScan_map_pair (eventToMaster P (statePoints I) r) _ _
    (rowMasterStateEventQuery_original P I r lambda K) _ R
end QEC.Coding.BDL26IncomingRowsExecution
