-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamHaltTimeProcess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:17:42.20362+00:00
-- url     : https://prove2.me/submissions/43098855-b179-4c57-93e8-ade096f1cbcf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamHaltTime

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun n => streamHaltTime p n omega) :=
  measurable_pi_lambda _ (fun n => measurable_streamHaltTime p n)
end QEC.Coding.BDL26CountableEmbeddingExperiment
