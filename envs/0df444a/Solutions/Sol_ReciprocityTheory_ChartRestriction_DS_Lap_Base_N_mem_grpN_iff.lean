-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.mem_grpN_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:41.734135+00:00
-- url     : https://prove2.me/submissions/278c7d8f-f46b-43d0-8530-d41bd6339800

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
open Matrix
open scoped Matrix.Norms.Operator
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (lev : Fin n → ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ grpN (levF lev) (adjH H) ↔ g - 1 ∈ levF lev 0 ∧ gᴴ * H * g = H := by
  have hadj : adjH H g = H * gᴴ * H := rfl
  show g - 1 ∈ levF lev 0 ∧ adjH H g * g = 1 ↔ _
  rw [hadj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc gᴴ * H * g = (H * H) * (gᴴ * H * g) := by rw [hH, Matrix.one_mul]
      _ = H * (H * gᴴ * H * g) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [h2, Matrix.mul_one]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc H * gᴴ * H * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, hH]
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
