-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamPhysicalOutput_eq_levelMap_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:15:32.212127+00:00
-- url     : https://prove2.me/submissions/64cffd3f-509f-4e32-a61e-a46c05e8f8cf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_levelMap_succ
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_stageInput_truncate
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_tableAt_truncate
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    (n : ℕ) (omega : Omega p) :
    streamPhysicalOutput p n omega = levelMap p omega (n+1) := by
  unfold streamPhysicalOutput stagePhysicalOutput
  rw [stageInput_truncate, tableAt_truncate]
  exact (levelMap_succ p omega n).symm
end QEC.Coding.BDL26CountableEmbeddingExperiment
