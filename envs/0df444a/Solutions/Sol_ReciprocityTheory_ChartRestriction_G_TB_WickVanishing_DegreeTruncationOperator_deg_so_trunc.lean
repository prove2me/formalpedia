-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.deg_so_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:25:13.693343+00:00
-- url     : https://prove2.me/submissions/506abecf-431d-4c1e-aa7a-7b0ef7865a77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_trunc_deg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open SecondColumnDegree
variable {k : Type} [CommRing k] [Algebra ℚ k]
section General
variable {σ : Type} [Fintype σ]
private theorem totalDegree_pderiv_le' (i : σ) (y : MvPolynomial σ k) :
    (pderiv i y).totalDegree ≤ y.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum y]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sup_le fun u hu => ?_
  have hu' := MvPolynomial.support_monomial_subset hu
  rw [Finset.mem_singleton] at hu'
  subst hu'
  have hts : s - Finsupp.single i 1 ≤ s := tsub_le_self
  calc (s - Finsupp.single i 1).sum (fun _ e => e)
      ≤ (s - Finsupp.single i 1).sum (fun _ e => e) +
          (s - (s - Finsupp.single i 1)).sum (fun _ e => e) := Nat.le_add_right _ _
    _ = ((s - Finsupp.single i 1) + (s - (s - Finsupp.single i 1))).sum (fun _ e => e) :=
        (Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)).symm
    _ = s.sum (fun _ e => e) := by rw [add_tsub_cancel_of_le hts]
end General
section Columns
variable {ι : Type} [Fintype ι] {n : ℕ}
end Columns
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open SecondColumnDegree
variable {k : Type} [CommRing k] [Algebra ℚ k]
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
theorem _root_.solution (c : σ → σ → k) (N : ℕ) (x : MvPolynomial σ k) :
    (secondOrder k c (trunc N x)).totalDegree ≤ N := by
  unfold secondOrder
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun l' _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact ((totalDegree_pderiv_le' _ _).trans (totalDegree_pderiv_le' _ _)).trans (trunc_deg N x)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
