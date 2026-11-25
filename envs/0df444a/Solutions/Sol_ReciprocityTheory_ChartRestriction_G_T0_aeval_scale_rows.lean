-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.aeval_scale_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:33:00.474282+00:00
-- url     : https://prove2.me/submissions/d997565c-1c44-41e5-bff9-7b721c5ebc47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {R : Type*} [CommRing R] {B n : ℕ} (d0 : ℕ)
    (F : MvPolynomial (Fin B × Fin n) R) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F)
    {S : Type*} [CommRing S] [Algebra R S] (r : Fin B × Fin n → S) (s : Finset (Fin B)) (l : S) :
    aeval (fun t => if t.1 ∈ s then l * r t else r t) F = l ^ (s.card * d0) * aeval r F := by
  have key : ∀ m ∈ F.support, ∏ t, (if t.1 ∈ s then l * r t else r t) ^ m t =
      l ^ (s.card * d0) * ∏ t, r t ^ m t := by
    intro m hm
    have h1 : ∀ t : Fin B × Fin n, (if t.1 ∈ s then l * r t else r t) ^ m t =
        (if t.1 ∈ s then l ^ m t else 1) * r t ^ m t := by
      intro t
      split_ifs <;> simp [mul_pow]
    simp_rw [h1, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc ∑ b, ∑ j, (if b ∈ s then m (b, j) else 0) = ∑ b, (if b ∈ s then d0 else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          split_ifs with hb
          · exact hF m hm b
          · simp
      _ = s.card * d0 := by
          rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
            smul_eq_mul]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · beta_reduce
    rw [key m hm]
    ring
  · intro i
    simp
  · intro i
    simp
end ReciprocityTheory.ChartRestriction.G.T0
