-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.coeff_coneMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:41.530655+00:00
-- url     : https://prove2.me/submissions/2afe0723-1ded-4af5-84b0-0884dc7798b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
section Coord
variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}
private theorem coneMap_monomial' (x : ι → Ω) (e : ι →₀ ℕ) (a : o) :
    coneMap o x (monomial e a) = Polynomial.C (aeval x (monomial e a)) * Polynomial.X ^ e.degree := by
  unfold coneMap
  rw [aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, map_mul, mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, Polynomial.C_pow,
    Finset.prod_pow_eq_pow_sum]
  congr 1
private theorem coeff_coneMap_eq_aeval_homogeneousComponent (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  rw [Polynomial.finset_sum_coeff]
  simp only [coneMap_monomial', Polynomial.coeff_C_mul_X_pow]
  rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases eq_or_ne e.degree d with h | h
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]
end Coord
end ReciprocityTheory.ChartRestriction.G.Geo
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  exact coeff_coneMap_eq_aeval_homogeneousComponent o x f d
end ReciprocityTheory.ChartRestriction.G.Geo
