-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:08:38.168013+00:00
-- url     : https://prove2.me/submissions/243bfe02-0c38-4833-9154-dbf028490490

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_self
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_succ
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_self



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (omega : Omega p) :
    experimentPrefix p m n h (truncate p n omega) = truncate p m omega := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      rw [prefix_self]
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        rw [prefix_self]
      · have hmn : m ≤ n := by omega
        rw [prefix_succ p hmn]
        exact ih hmn
end QEC.Coding.BDL26CountableEmbeddingExperiment
