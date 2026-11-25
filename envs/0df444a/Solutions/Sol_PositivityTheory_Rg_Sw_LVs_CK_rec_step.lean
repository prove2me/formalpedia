-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.rec_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:51.906088+00:00
-- url     : https://prove2.me/submissions/8576ba1f-d430-405e-af7e-fcdda3a850d8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedDerivativeColumnCaseInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyK
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_term_p
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_determinant_power_zero_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_detD_fin
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_iterated_derivative_column_case_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_iterated_derivative_corner_case_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.phiL_apply
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.piL_apply



set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (t : ℤ) (N : ℕ) : detD (H (N + 1) t) = ((t : ℂ) + N) * detD (H N t) := by
  rw [detD_fin _ _ (analyticAt_determinant_power_zero_int _ _), detD_fin _ _ (analyticAt_determinant_power_zero_int _ _),
    Finset.univ_perm_fin_succ, ← Finset.univ_product_univ, Finset.sum_map, Finset.sum_product,
    Fin.sum_univ_succ]
  simp only [Equiv.toEmbedding_apply, term_p, Equiv.Perm.decomposeFin.symm_sign, if_pos rfl]
  have h0 : ∀ e : Equiv.Perm (Fin N),
      (iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 (0 : Fin (N + 1)) 1)) 0)
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm ((0 : Fin (N + 1)), e) k.succ) 1) =
      t * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro e
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    exact iterated_derivative_corner_case_int t e
  simp only [h0, if_true, one_mul, Fin.succ_ne_zero, if_false]
  cases N with
  | zero => simp
  | succ M =>
    simp only [iterated_derivative_column_case_int, Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg,
      Int.cast_one, neg_one_mul, neg_mul_neg]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_mul, Finset.mul_sum, Finset.mul_sum,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;> push_cast <;> ring
end PositivityTheory.Rg.Sw.LVs.CK
