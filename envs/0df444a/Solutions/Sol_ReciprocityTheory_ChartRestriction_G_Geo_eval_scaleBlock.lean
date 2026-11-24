-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eval_scaleBlock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:34.662835+00:00
-- url     : https://prove2.me/submissions/47700f80-d5bf-4984-99eb-f2afb13d2b9a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) (a : K → ℕ)
    (hf : IsMultiHomog f a) :
    eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) =
      c ^ a k0 * eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∈ f.support := MvPolynomial.support_map_subset _ _ hm
  have hdeg := hf m hm' k0
  simp only [scaleBlock, mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ x : (Σ k, ι k), (if x.1 = k0 then c else 1) ^ m x = c ^ a k0 := by
    rw [Fintype.prod_sigma, Finset.prod_eq_single k0]
    · simp [hdeg, Finset.prod_pow_eq_pow_sum]
    · intro k _ hk
      simp [hk]
    · simp
  rw [hc]
  ring
end ReciprocityTheory.ChartRestriction.G.Geo
