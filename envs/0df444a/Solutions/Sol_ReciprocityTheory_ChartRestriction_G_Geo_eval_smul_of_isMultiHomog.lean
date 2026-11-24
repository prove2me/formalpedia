-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_isMultiHomog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:01.504503+00:00
-- url     : https://prove2.me/submissions/1b865f1b-5745-4de2-84ea-ce3332a6b97b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC

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
theorem _root_.solution {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hms : m ∈ s.support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_map, h0, map_zero])
  have hsub : ∀ f : (Σ k, ι k) → ℂ, ∏ i ∈ m.support, f i ^ m i = ∏ i, f i ^ m i := fun f =>
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  rw [hsub, hsub, mul_left_comm]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show (∏ s, c (⟨k, s⟩ : Σ k, ι k).fst ^ m ⟨k, s⟩) = ∏ s, c k ^ m ⟨k, s⟩ from rfl,
    Finset.prod_pow_eq_pow_sum, hs m hms k]
end ReciprocityTheory.ChartRestriction.G.Geo
