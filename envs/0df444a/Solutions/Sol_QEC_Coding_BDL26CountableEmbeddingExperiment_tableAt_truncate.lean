-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.tableAt_truncate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:21:09.010077+00:00
-- url     : https://prove2.me/submissions/35a4d28a-b3a3-40c2-9296-2e3edc6798ca

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_prefix

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (omega : Omega p) : tableAt p n i (truncate p n omega) = omega i.val := by
  change (experimentPrefix p (i.val+1) n i.isLt (truncate p n omega)).2 = omega i.val
  rw [truncate_prefix]
  rfl
end QEC.Coding.BDL26CountableEmbeddingExperiment
