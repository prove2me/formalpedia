-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.iter_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:03.193377+00:00
-- url     : https://prove2.me/submissions/3faced5a-e5dc-4e99-b06a-17f0aa80a379

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_comp

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
theorem _root_.solution (hf : Differentiable ℝ f) : ∀ i, Differentiable ℝ (iter f i) := by
  intro i
  induction i with
  | zero =>
    have h : iter f 0 = fun _ => (0 : A) := funext fun _ => rfl
    rw [h]
    exact differentiable_const 0
  | succ i ih =>
    have h : iter f (i + 1) = fun z => iter f i z + (z - f (iter f i z)) := funext fun _ => rfl
    rw [h]
    exact ih.add (differentiable_id.sub (hf.comp ih))
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
