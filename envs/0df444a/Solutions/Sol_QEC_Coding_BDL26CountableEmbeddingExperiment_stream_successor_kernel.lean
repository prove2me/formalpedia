-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.stream_successor_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:14:02.944344+00:00
-- url     : https://prove2.me/submissions/e5a81d4e-2a7a-47a1-991b-8c3a7c0ce0cc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_levelMap_law
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_succ


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
    (streamLaw p).map (fun omega => levelMap p omega (n+1)) =
      successorKernel p n ∘ₘ ((streamLaw p).map (fun omega => levelMap p omega n)) := by
  rw [levelMap_law, levelMap_law]
  exact outputLaw_succ p n
end QEC.Coding.BDL26CountableEmbeddingExperiment
