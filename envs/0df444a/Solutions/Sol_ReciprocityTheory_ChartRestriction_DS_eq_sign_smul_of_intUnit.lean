-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eq_sign_smul_of_intUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:22:14.596572+00:00
-- url     : https://prove2.me/submissions/1dedfab8-c7e9-4d5c-a638-2db6edb31f26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {A : Type*} [AddCommGroup A] [Module ℂ A] (u : ℤˣ) (x y : A) (h : x = u • y) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ x = σ • y := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h⟩
end ReciprocityTheory.ChartRestriction.DS
