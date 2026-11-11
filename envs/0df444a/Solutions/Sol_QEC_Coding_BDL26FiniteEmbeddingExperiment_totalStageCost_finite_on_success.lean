-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_finite_on_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:58:50.262216+00:00
-- url     : https://prove2.me/submissions/d3f698f5-80d2-4366-9483-c18894814e02

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_finite_of_halts

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p n) (h : z ∈ finiteSuccess p n) : totalStageCost p n z < ∞ := by
  apply ENNReal.sum_lt_top.mpr
  intro i _
  exact stageCost_finite_of_halts p n i z (h.2.1 i)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
