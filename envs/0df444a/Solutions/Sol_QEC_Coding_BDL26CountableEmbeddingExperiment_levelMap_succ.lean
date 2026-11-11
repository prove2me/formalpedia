-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.levelMap_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:03:02.615251+00:00
-- url     : https://prove2.me/submissions/0ae8c4ef-1925-4500-bafa-154a24453ef7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (omega : Omega p) (n : ℕ) :
    levelMap p omega (n+1) = physicalSuccessorOutput p n (levelMap p omega n) (omega n) := rfl
end QEC.Coding.BDL26CountableEmbeddingExperiment
