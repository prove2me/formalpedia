-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.measurePreserving_truncate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:11:28.657194+00:00
-- url     : https://prove2.me/submissions/51b42dd5-40b0-4495-af8c-2ae97824ba92

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_law
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate


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
    MeasurePreserving (truncate p n) (streamLaw p) (experimentLaw p n) :=
  ⟨measurable_truncate p n, truncate_law p n⟩
end QEC.Coding.BDL26CountableEmbeddingExperiment
