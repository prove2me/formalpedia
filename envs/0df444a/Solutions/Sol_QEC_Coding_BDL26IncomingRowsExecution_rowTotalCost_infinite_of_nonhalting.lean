-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_infinite_of_nonhalting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:41:56.801204+00:00
-- url     : https://prove2.me/submissions/25c6f247-0a25-4aa4-92de-4e77b5181d8a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowStageCost_nonhalting

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
    (i : Fin N) (z : Experiment p N) (h : ¬stageHalts p N i z) : rowTotalCost p N z=∞ := by
  apply top_unique
  rw [← rowStageCost_nonhalting p N i z h]
  exact Finset.single_le_sum (fun (j : Fin N) (_ : j ∈ (Finset.univ : Finset (Fin N))) =>
    show (0 : ℝ≥0∞) ≤ rowStageCost p N j z from bot_le) (Finset.mem_univ i)
end QEC.Coding.BDL26IncomingRowsExecution
