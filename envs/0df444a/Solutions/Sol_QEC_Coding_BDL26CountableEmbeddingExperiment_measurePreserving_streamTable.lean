-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.measurePreserving_streamTable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:23:05.431771+00:00
-- url     : https://prove2.me/submissions/0004db71-4ebb-4930-ab30-748989ac25ad

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurePreserving (fun omega : Omega p => omega n) (streamLaw p) (physicalTableLaw p n) :=
  measurePreserving_eval_infinitePi (physicalTableLaw p) n
end QEC.Coding.BDL26CountableEmbeddingExperiment
