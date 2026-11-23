-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.mem_lieN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:24.1287+00:00
-- url     : https://prove2.me/submissions/770dece5-cbce-4349-93b9-6a3fa6f2eac4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart

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
theorem _root_.solution {Y : A} : Y ∈ lieN F st ↔ Y ∈ F 0 ∧ st Y = -Y := by
  simp only [lieN, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, eq_neg_of_add_eq_zero_left h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2]
    abel
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
