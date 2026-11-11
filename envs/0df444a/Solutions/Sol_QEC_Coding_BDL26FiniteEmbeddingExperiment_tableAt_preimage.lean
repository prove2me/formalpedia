-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.tableAt_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:53:45.732689+00:00
-- url     : https://prove2.me/submissions/82b3c76e-30d7-4dd8-96ca-016f29d7e426

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_tableAt_law
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_tableAt


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (B : Set (StageTables p i.val)) (hB : MeasurableSet B) :
    experimentLaw p n (tableAt p n i ⁻¹' B) = physicalTableLaw p i.val B := by
  rw [← Measure.map_apply (measurable_tableAt p n i) hB, tableAt_law]
end QEC.Coding.BDL26FiniteEmbeddingExperiment
