-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.pair_separation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:28.065999+00:00
-- url     : https://prove2.me/submissions/55c0a726-a84c-4ef9-8218-fbd2e6cc3090

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_RhoProjectionAssembly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_upgrade

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift ReciprocityTheory.ChartRestriction.G.Lift.VA
open WithZero
namespace ReciprocityTheory.ChartRestriction.G.Lift.VA
theorem _root_.solution : PairSep := by
  intro Ω _ ι _ v h1 h2 i j hij
  choose π hπ using h1
  have hex : ∃ x, ¬ (v i x ≤ 1 ↔ v j x ≤ 1) := by
    by_contra hc
    push Not at hc
    exact h2 i j hij (Valuation.isEquiv_of_val_le_one hc)
  obtain ⟨x, hx⟩ := hex
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hi0 : 0 < v i x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
  have hj0 : 0 < v j x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
  by_cases hix : v i x ≤ 1
  · have hjx : 1 < v j x := lt_of_not_ge (fun h => hx (iff_of_true hix h))
    refine upgrade (v i) (v j) (π i) (hπ i) x⁻¹ ?_ ?_
    · rw [map_inv₀]
      exact (one_le_inv₀ hi0).mpr hix
    · rw [map_inv₀]
      exact (inv_lt_one₀ hj0).mpr hjx
  · have hix' : 1 < v i x := lt_of_not_ge hix
    have hjx : v j x ≤ 1 := by
      by_contra h
      exact hx (iff_of_false hix h)
    obtain ⟨y, hy1, hy2⟩ := upgrade (v j) (v i) (π j) (hπ j) x⁻¹
      (by rw [map_inv₀]; exact (one_le_inv₀ hj0).mpr hjx)
      (by rw [map_inv₀]; exact (inv_lt_one₀ hi0).mpr hix')
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy1
      exact absurd hy1 (not_lt.mpr zero_le)
    have hiy : 0 < v i y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
    have hjy : 0 < v j y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
    refine ⟨y⁻¹, ?_, ?_⟩
    · rw [map_inv₀]
      exact (one_lt_inv₀ hiy).mpr hy2
    · rw [map_inv₀]
      exact (inv_lt_one₀ hjy).mpr hy1
end ReciprocityTheory.ChartRestriction.G.Lift.VA
