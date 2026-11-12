-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.stream_rectangle_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:11:45.924065+00:00
-- url     : https://prove2.me/submissions/fcd044df-4ab4-4bae-ae7d-104822916b91

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    (A : Finset ℕ) (B : (n : ℕ) → Set (StageTables p n))
    (hB : ∀ n ∈ A, MeasurableSet (B n)) :
    streamLaw p (Set.pi (A : Set ℕ) B) = ∏ n ∈ A, physicalTableLaw p n (B n) :=
  Measure.infinitePi_pi (physicalTableLaw p) hB
end QEC.Coding.BDL26CountableEmbeddingExperiment
