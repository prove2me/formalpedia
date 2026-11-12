-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.restrictTables_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:22:47.537266+00:00
-- url     : https://prove2.me/submissions/f0c5afb7-a153-4c00-b82b-7c241816e0b5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (streamLaw p).map (restrictTables p n) =
      Measure.pi (fun i : Fin n => physicalTableLaw p i.val) := by
  change (Measure.infinitePi (physicalTableLaw p)).map
    (fun omega : (j : ℕ) → StageTables p j => fun i : Fin n => omega i.val) =
      Measure.pi (fun i : Fin n => physicalTableLaw p i.val)
  exact (Measure.map_infinitePi_infinitePi_of_inj
    (Ω := StageTables p)
    (mΩ := fun j => inferInstanceAs (MeasurableSpace (StageTables p j)))
    (P := physicalTableLaw p) (f := fun i : Fin n => i.val)
    (by intro i j hij; exact Fin.ext hij)).trans
      (Measure.infinitePi_eq_pi (fun i : Fin n => physicalTableLaw p i.val))
end QEC.Coding.BDL26CountableEmbeddingExperiment
