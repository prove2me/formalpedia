-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.stageInput_truncate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:22:15.470614+00:00
-- url     : https://prove2.me/submissions/c79d95c2-714e-4ae6-8be3-1e54692c9204

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_prefix


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
    (omega : Omega p) (i : Fin n) :
    stageInput p n i (truncate p n omega) = levelMap p omega i.val := by
  unfold stageInput
  rw [truncate_prefix]
  rfl
end QEC.Coding.BDL26CountableEmbeddingExperiment
