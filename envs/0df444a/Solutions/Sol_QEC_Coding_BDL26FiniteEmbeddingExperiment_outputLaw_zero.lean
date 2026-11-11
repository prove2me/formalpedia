-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:12:14.837235+00:00
-- url     : https://prove2.me/submissions/9c1a2945-2e95-4cdd-8d06-8bd0727c9caa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    outputLaw p 0 = Measure.dirac (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)) := by
  change (Measure.dirac (() : Experiment p 0)).map (evaluate p 0) = _
  exact Measure.map_dirac' (measurable_evaluate p 0) ()
end QEC.Coding.BDL26FiniteEmbeddingExperiment
