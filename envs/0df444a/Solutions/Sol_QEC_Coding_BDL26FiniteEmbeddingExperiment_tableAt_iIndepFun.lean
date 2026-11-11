-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.tableAt_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:56:56.648848+00:00
-- url     : https://prove2.me/submissions/9b9676d5-2ca1-47a3-be65-880f3424f118

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_tableAt_preimage
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finite_rectangle_probability
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    iIndepFun (tableAt p n) (experimentLaw p n) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hB
  rw [finite_rectangle_probability]
  apply Finset.prod_congr rfl
  intro i hi
  exact (tableAt_preimage p n i (B i) (hB i hi)).symm
end QEC.Coding.BDL26FiniteEmbeddingExperiment
