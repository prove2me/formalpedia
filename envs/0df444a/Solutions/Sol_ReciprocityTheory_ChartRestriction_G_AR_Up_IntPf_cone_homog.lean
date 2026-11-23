-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.cone_homog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:20.449998+00:00
-- url     : https://prove2.me/submissions/8135e640-7b29-4c5b-94e9-ebb96dfed4ef

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA

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
theorem _root_.solution (a : ι → E) {f : MvPolynomial ι R} {d : ℕ} (hf : f.IsHomogeneous d) :
    cone a f = Polynomial.monomial d (aeval a f) := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hp : (m.prod fun i k => (Polynomial.C (a i) * Polynomial.X) ^ k) =
      Polynomial.C (m.prod fun i k => a i ^ k) * Polynomial.X ^ d := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
      Finset.prod_pow_eq_pow_sum, hd]
  rw [cone, aeval_monomial, aeval_monomial, hp, Polynomial.algebraMap_apply, ← mul_assoc,
    ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]
end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
