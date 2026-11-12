-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamHaltTime_of_not_halts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:35:23.729494+00:00
-- url     : https://prove2.me/submissions/c7c9da10-08a6-45f1-8d1c-0ec9dc938d34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageHaltTime_of_not_halts


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (hh : ¬ streamHalts p n omega) : streamHaltTime p n omega = 0 :=
  stageHaltTime_of_not_halts p (n+1) (Fin.last n) (truncate p (n+1) omega) hh
end QEC.Coding.BDL26CountableEmbeddingExperiment
