-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamPhysicalOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:32:21.350202+00:00
-- url     : https://prove2.me/submissions/83f3b5aa-4e95-4e85-8b7c-ee212eee13e4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePhysicalOutput

section
noncomputable section
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
private theorem measurable_observation {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {A : Type*} [MeasurableSpace A] (f : Experiment p (n+1) → A) (hf : Measurable f) :
    Measurable (f ∘ truncate p (n+1)) :=
  @Measurable.comp (Omega p) (Experiment p (n+1)) A inferInstance inferInstance inferInstance
    f (truncate p (n+1)) hf (measurable_truncate p (n+1))
end QEC.Coding.BDL26CountableEmbeddingExperiment
end
end

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
    Measurable (streamPhysicalOutput p n) :=
  measurable_observation p n _ (measurable_stagePhysicalOutput p (n+1) (Fin.last n))
end QEC.Coding.BDL26CountableEmbeddingExperiment
