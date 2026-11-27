-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValUFD.isUnit_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:33.499597+00:00
-- url     : https://prove2.me/submissions/c820a97b-a26c-4fcd-bf3f-96fad12a09c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValUFD
variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
namespace ReciprocityTheory.ChartRestriction.G.T0.ValUFD
theorem _root_.solution {σ K : Type*} [Field K] (κ : MvPolynomial σ K) (h : IsUnit κ) :
    ∃ k : K, k ≠ 0 ∧ κ = MvPolynomial.C k := by
  obtain ⟨r, hr, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
  exact ⟨r, hr.ne_zero, rfl⟩
end ReciprocityTheory.ChartRestriction.G.T0.ValUFD
