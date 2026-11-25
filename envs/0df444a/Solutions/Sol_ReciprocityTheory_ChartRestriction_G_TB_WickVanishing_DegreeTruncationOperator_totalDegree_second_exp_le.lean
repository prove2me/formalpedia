-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.totalDegree_second_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:35:05.566354+00:00
-- url     : https://prove2.me/submissions/d40b11ae-40cd-44e4-b438-5ca98b024459

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_trunc_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_deg_so_trunc
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
private theorem totalDegree_iterate_secondOrder_le (c : σ → σ → k) (M : ℕ) :
    ∀ (i : ℕ) (x : MvPolynomial σ k), x.totalDegree ≤ M →
      ((secondOrder k c)^[i] x).totalDegree ≤ M := by
  intro i
  induction i with
  | zero => intro x hx; exact hx
  | succ i ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    have h := deg_so_trunc c M ((secondOrder k c)^[i] x)
    rwa [trunc_id M _ (ih x hx)] at h
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
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
theorem _root_.solution (c : ι → ι → k) (t : k) (N : ℕ) (y : MvPolynomial ι k) :
    (E1 c t N y).totalDegree ≤ y.totalDegree := by
  unfold E1
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  exact (totalDegree_smul_le _ _).trans (totalDegree_iterate_secondOrder_le c _ i y le_rfl)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
