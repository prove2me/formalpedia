-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.measurableSet_streamHalts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:15:57.459205+00:00
-- url     : https://prove2.me/submissions/4489b0f2-9c27-4458-b6b1-6574ac677451

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurableSet_stageHalts


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurableSet {omega | streamHalts p n omega} :=
  (measurableSet_stageHalts p (n+1) (Fin.last n)).preimage (measurable_truncate p (n+1))
end QEC.Coding.BDL26CountableEmbeddingExperiment
