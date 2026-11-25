-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:21.966722+00:00
-- url     : https://prove2.me/submissions/01dd14d5-2b84-4890-bc94-48c6d2ebb420

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_shear

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
omit [FiniteDimensional ℝ A]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (hF : IsFil F L) {Y Y' : A} (hY : Y ∈ F 0) (hY' : Y' ∈ F 0)
    (h : NormedSpace.exp Y = NormedSpace.exp Y') : Y = Y' := by
  exact IsShear.inj hF hF.exp_shear hY hY'
    (by show NormedSpace.exp Y - 1 = NormedSpace.exp Y' - 1; rw [h])
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
