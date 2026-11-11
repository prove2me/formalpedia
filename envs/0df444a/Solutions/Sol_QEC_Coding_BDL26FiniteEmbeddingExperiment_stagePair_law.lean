-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stagePair_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:39:30.359262+00:00
-- url     : https://prove2.me/submissions/e6749135-42bd-48fd-bae4-4b10c0bfc040

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurePreserving_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_freshPair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_freshPair_law
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePair_eq_freshPair_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_prefix


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (experimentLaw p n).map (stagePair p n i) =
      (outputLaw p i.val).prod (physicalTableLaw p i.val) := by
  rw [stagePair_eq_freshPair_prefix, ← Measure.map_map
    (measurable_freshPair p i.val) (measurable_prefix p i.isLt),
    (measurePreserving_prefix p i.isLt).map_eq, freshPair_law]
end QEC.Coding.BDL26FiniteEmbeddingExperiment
