-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowMasterStateEventQuery_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:03:22.283749+00:00
-- url     : https://prove2.me/submissions/043c9cb9-8993-4f50-8502-70c9f755814f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution

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
    rowMasterStateEventQuery P I lambda K (eventToMaster P (statePoints I) r e) R=
      rowStateEventQuery P I r lambda K e R := rfl
end QEC.Coding.BDL26IncomingRowsExecution
