-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.lamW_secondOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:46:37.688814+00:00
-- url     : https://prove2.me/submissions/56c01a15-8fe9-48ff-8c75-0ca6460eb551

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_lamW_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_lamW_monomial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_lamW_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_secondOrder_add

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (c : ι → ι → k) (P : MvPolynomial ι k) :
    lamW ψ (secondOrder k c P) = (AddMonoidAlgebra.coeff P).sum (fun n a => a * rW ψ c n) := by
  refine MvPolynomial.induction_on' P (fun n a => ?_) (fun p q hp hq => ?_)
  · show lamW ψ (secondOrder k c (MvPolynomial.monomial n a)) =
      (Finsupp.single n a).sum fun m b => b * rW ψ c m
    have hL : ∀ g : ι → k, ((Finset.univ : Finset ι).toList.map g).sum = ∑ i, g i := by
      intro g
      first
        | exact Finset.sum_map_toList _ _
        | exact Finset.sum_toList _ _
        | rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]
    rw [Finsupp.sum_single_index (zero_mul _)]
    simp only [secondOrder, lamW_sum, MvPolynomial.pderiv_monomial, MvPolynomial.C_mul_monomial,
      lamW_monomial, rW, hL, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Nat.cast_mul]
    ring
  · rw [secondOrder_add, lamW_add, hp, hq]
    show _ = (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q).sum _
    rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
end ReciprocityTheory.ChartRestriction.G.TB.G2
