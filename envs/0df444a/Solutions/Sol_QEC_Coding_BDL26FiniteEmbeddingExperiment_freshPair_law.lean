-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.freshPair_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:14:34.261221+00:00
-- url     : https://prove2.me/submissions/8f02e19d-bfd6-41ce-9295-a01afae8c3bf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
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
    (experimentLaw p (n+1)).map (freshPair p n) =
      (outputLaw p n).prod (physicalTableLaw p n) := by
  have hid : Measurable (id : StageTables p n → StageTables p n) := measurable_id
  have h : (outputLaw p n).prod ((physicalTableLaw p n).map (id : StageTables p n → StageTables p n)) =
      ((experimentLaw p n).prod (physicalTableLaw p n)).map
        (Prod.map (evaluate p n) (id : StageTables p n → StageTables p n)) :=
    Measure.map_prod_map (experimentLaw p n) (physicalTableLaw p n) (measurable_evaluate p n) hid
  rw [Measure.map_id] at h
  have hfun : Prod.map (evaluate p n) (id : StageTables p n → StageTables p n) = freshPair p n := by
    funext z
    rcases z with ⟨x,T⟩
    rfl
  rw [hfun] at h
  exact h.symm
end QEC.Coding.BDL26FiniteEmbeddingExperiment
