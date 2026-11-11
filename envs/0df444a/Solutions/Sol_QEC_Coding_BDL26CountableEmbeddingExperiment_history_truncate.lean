-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.history_truncate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:03:29.456118+00:00
-- url     : https://prove2.me/submissions/b64eea49-8343-4a81-8809-37a85f85abcd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_prefix


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (i : Fin (n+1)) :
    history p n (truncate p n omega) i = levelMap p omega i.val := by
  unfold history
  rw [truncate_prefix]
  rfl
end QEC.Coding.BDL26CountableEmbeddingExperiment
