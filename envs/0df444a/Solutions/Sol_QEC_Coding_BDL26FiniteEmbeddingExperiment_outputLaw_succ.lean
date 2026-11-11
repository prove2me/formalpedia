-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:25:33.044191+00:00
-- url     : https://prove2.me/submissions/9001a1cd-3e1d-4370-afe1-76a7cd9f8d26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_freshPair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_freshPair_law
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorOutput_law


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    outputLaw p (n+1) = (successorKernel p n) ∘ₘ (outputLaw p n) := by
  rw [← physicalSuccessorOutput_law p n (outputLaw p n), ← freshPair_law,
    Measure.map_map (measurable_joint_physicalSuccessorOutput p n) (measurable_freshPair p n)]
  rfl
end QEC.Coding.BDL26FiniteEmbeddingExperiment
