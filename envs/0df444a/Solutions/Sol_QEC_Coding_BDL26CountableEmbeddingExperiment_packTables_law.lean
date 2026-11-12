-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.packTables_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:31:23.27345+00:00
-- url     : https://prove2.me/submissions/00a21a91-b9da-406d-a5e5-b3feb6a2aa5f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_unpackTables_law

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
    (Measure.pi (fun i : Fin n => physicalTableLaw p i.val)).map (packTables p n) =
      experimentLaw p n := by
  rw [← unpackTables_law p n,
    Measure.map_map (measurable_packTables p n) (measurable_unpackTables p n)]
  have heq : packTables p n ∘ unpackTables p n = id := funext (pack_unpackTables p n)
  rw [heq, Measure.map_id]
end QEC.Coding.BDL26CountableEmbeddingExperiment
