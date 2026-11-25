-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsFil.log_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:58.429312+00:00
-- url     : https://prove2.me/submissions/f1b16236-4d03-4434-aad9-3a1deed284c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_left_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_iter_growth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_shear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_bound

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
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace IsFil
theorem _root_.solution (hF : IsFil F L) : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ Y ∈ F 0,
    ‖Y‖ ≤ C * ‖NormedSpace.exp Y - 1‖ * (1 + ‖NormedSpace.exp Y - 1‖) ^ M := by
  have hE := hF.exp_shear
  obtain ⟨C, M, hC, hbd⟩ := IsShear.iter_growth hE (Cf := (L : ℝ) + 1) (Mf := L) (by positivity)
    (fun x hx => hF.exp_bound hx) L
  refine ⟨C, M, hC, fun Y hY => ?_⟩
  have hY' : iter (fun x => NormedSpace.exp x - 1) L (NormedSpace.exp Y - 1) = Y :=
    IsShear.left_inv hF hE hY
  have h1 := hbd (NormedSpace.exp Y - 1) (hE.1 Y hY)
  rw [hY'] at h1
  exact h1
end IsFil
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
