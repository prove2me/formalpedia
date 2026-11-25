-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.exp_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:25:23.730965+00:00
-- url     : https://prove2.me/submissions/dc99b1ff-6ba5-4869-8144-041e42202772

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_nilp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_totalDegree_second_exp_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_prodQ_deg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_exp_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_def


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
open MvPolynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open SecondColumnDegree
variable {k : Type} [CommRing k] [Algebra ℚ k]
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
theorem _root_.solution (c : ι → ι → k) (t : k) (N : ℕ) (D : Fin n → ℕ) (hD : ∑ b, D b ≤ N) :
    ∀ (S : Finset (Fin n)) (Q : Fin n → MvPolynomial ι k), (∀ b, (Q b).totalDegree ≤ D b) →
      IsNilpotent.exp (opA (cS c S) t N) (prodQ Q) =
        prodQ (fun b => if b ∈ S then E1 c t N (Q b) else Q b) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro Q _
    have h0 : opA (cS c (∅ : Finset (Fin n))) t N = 0 := by
      refine LinearMap.ext fun x => ?_
      rw [opA_apply, so_def]
      simp [cS]
    rw [h0, IsNilpotent.exp_zero]
    simp
  | insert a S ha ih =>
    intro Q hQ
    have hcs : cS c (insert a S) = fun p q => cB c a p q + cS c S p q := by
      funext p q
      simp only [cS, Finset.sum_insert ha]
    have hdeg : (prodQ fun b => if b ∈ S then E1 c t N (Q b) else Q b).totalDegree ≤ N := by
      refine (prodQ_deg _).trans (le_trans (Finset.sum_le_sum fun b _ => ?_) hD)
      split_ifs
      · exact (totalDegree_second_exp_le c t N (Q b)).trans (hQ b)
      · exact hQ b
    rw [hcs, opA_add, IsNilpotent.exp_add_of_commute (opA_comm _ _ t N) (opA_nilp _ t N)
      (opA_nilp _ t N), Module.End.mul_apply, ih Q hQ, exp_col c t N _ a hdeg]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp [ha]
    · simp [hb, Finset.mem_insert]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
