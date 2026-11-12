-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_finite_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:15:17.829413+00:00
-- url     : https://prove2.me/submissions/fd6e8564-a8d7-4fc6-9e51-0515ea66337b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowStageCost_finite_of_halts
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_infinite_of_nonhalting

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowTotalCost p N z<∞ ↔ ∀ i : Fin N, stageHalts p N i z := by
  constructor
  · intro h i
    by_contra hi
    rw [rowTotalCost_infinite_of_nonhalting p N i z hi] at h
    exact (lt_irrefl _) h
  · intro h
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact rowStageCost_finite_of_halts p N i z (h i)
end QEC.Coding.BDL26IncomingRowsExecution
