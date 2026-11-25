-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.secOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:34.519833+00:00
-- url     : https://prove2.me/submissions/de17c458-d76e-4c30-aaea-224a297a8657

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (i : ∀ k, ι k) (b : K → ℕ) :
    secOf i b = monomial (∑ k, Finsupp.single (⟨k, i k⟩ : Σ k, ι k) (b k)) 1 := by
  rw [secOf, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X_pow_eq_monomial]
end ReciprocityTheory.ChartRestriction.G.Geo
