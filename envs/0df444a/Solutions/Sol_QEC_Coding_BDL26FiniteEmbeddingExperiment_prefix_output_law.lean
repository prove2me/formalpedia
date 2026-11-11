-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_output_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:41:31.408669+00:00
-- url     : https://prove2.me/submissions/523be1fe-7be9-43e7-b40f-1a845fa1888b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurePreserving_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_prefix


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    (experimentLaw p n).map ((evaluate p m) ∘ experimentPrefix p m n h) = outputLaw p m := by
  rw [← Measure.map_map (measurable_evaluate p m) (measurable_prefix p h),
    (measurePreserving_prefix p h).map_eq]
  rfl
end QEC.Coding.BDL26FiniteEmbeddingExperiment
