-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:42:13.576684+00:00
-- url     : https://prove2.me/submissions/f37cdc72-7991-4b76-bd9a-2db78cf564bb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_packTables_law
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_restrictTables_law
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_restrictTables
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_eq_packTables


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
    (streamLaw p).map (truncate p n) = experimentLaw p n := by
  calc
    (streamLaw p).map (truncate p n) =
        ((streamLaw p).map (restrictTables p n)).map (packTables p n) := by
      rw [Measure.map_map (measurable_packTables p n) (measurable_restrictTables p n)]
      exact congrArg ((streamLaw p).map) (funext (truncate_eq_packTables p n))
    _ = experimentLaw p n := by rw [restrictTables_law, packTables_law]
end QEC.Coding.BDL26CountableEmbeddingExperiment
