-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_mem_grpN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:18.424336+00:00
-- url     : https://prove2.me/submissions/0fd2601f-9b65-4ed2-82ba-bfcd7f986163

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_shear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_mem_lieN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_neg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_st_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
variable [FiniteDimensional ℝ A]
variable {st : A →ₗ[ℝ] A}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (hF : IsFil F L) (hst : IsAdj F st) {Y : A} (hY : Y ∈ lieN F st) :
    NormedSpace.exp Y ∈ grpN F st := by
  obtain ⟨hY0, hY1⟩ := (mem_lieN (st := st)).1 hY
  show NormedSpace.exp Y - 1 ∈ F 0 ∧ st (NormedSpace.exp Y) * NormedSpace.exp Y = 1
  refine ⟨hF.exp_shear.1 Y hY0, ?_⟩
  rw [st_exp hF hst hY0, hY1]
  exact (exp_neg_mul Y).1
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
