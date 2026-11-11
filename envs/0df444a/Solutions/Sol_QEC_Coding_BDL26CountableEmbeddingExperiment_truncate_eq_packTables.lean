-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_eq_packTables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:59:08.465085+00:00
-- url     : https://prove2.me/submissions/22aa3856-fda3-4c90-95b0-5f962df41db5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) : truncate p n omega = packTables p n (restrictTables p n omega) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (truncate p n omega, omega n) =
        (packTables p n (restrictTables p n omega), omega n)
      rw [ih]
end QEC.Coding.BDL26CountableEmbeddingExperiment
