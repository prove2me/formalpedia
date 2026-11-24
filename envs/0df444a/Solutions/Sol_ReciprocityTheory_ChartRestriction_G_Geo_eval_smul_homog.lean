-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:14.488881+00:00
-- url     : https://prove2.me/submissions/97729b45-039d-4d93-874f-c6cbaf7e5c2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB

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
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum,
    MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℂ))]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ m ⟨k, y⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring
end ReciprocityTheory.ChartRestriction.G.Geo
