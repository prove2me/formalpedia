-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_truncate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:14:06.8277+00:00
-- url     : https://prove2.me/submissions/961bdc1d-ed65-4899-b7c9-f324a56a482e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_eq_packTables
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_restrictTables

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (truncate p n) := by
  have heq : truncate p n = (packTables p n) ∘ restrictTables p n :=
    funext (truncate_eq_packTables p n)
  rw [heq]
  exact @Measurable.comp (Omega p) (TableVector p n) (Experiment p n)
    inferInstance inferInstance inferInstance (packTables p n) (restrictTables p n)
    (measurable_packTables p n) (measurable_restrictTables p n)
end QEC.Coding.BDL26CountableEmbeddingExperiment
