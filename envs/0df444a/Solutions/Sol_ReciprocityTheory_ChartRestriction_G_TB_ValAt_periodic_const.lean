-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ValAt.periodic_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:32:38.556521+00:00
-- url     : https://prove2.me/submissions/a36525ee-ab5e-41df-adb4-59c31e5b7d67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.ValAt
theorem _root_.solution (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (L : AddSubgroup (Fin g → ℂ))
    (K : Set (Fin g → ℂ)) (hK : IsCompact K) (hcov : ∀ z, ∃ w ∈ K, z - w ∈ L)
    (hper : ∀ z, ∀ l ∈ L, f (z + l) = f z) (z w : Fin g → ℂ) : f z = f w := by
  apply hf.apply_eq_apply_of_bounded
  refine (hK.image hf.continuous).isBounded.subset ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨w, hw, hl⟩ := hcov z
  refine ⟨w, hw, ?_⟩
  have := hper w (z - w) hl
  rw [add_sub_cancel] at this
  exact this.symm
end ReciprocityTheory.ChartRestriction.G.TB.ValAt
