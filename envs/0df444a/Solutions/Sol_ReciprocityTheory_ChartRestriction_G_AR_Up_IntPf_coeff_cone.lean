-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.coeff_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:55.818876+00:00
-- url     : https://prove2.me/submissions/f080b699-239a-47c2-9076-f92f98bbba8c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_cone_homog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
noncomputable section
open MvPolynomial
variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
theorem _root_.solution (a : ι → E) (f : MvPolynomial ι R) (n : ℕ) :
    (cone a f).coeff n = aeval a (homogeneousComponent n f) := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [cone_homog a (homogeneousComponent_isHomogeneous _ f), Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero]
end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
