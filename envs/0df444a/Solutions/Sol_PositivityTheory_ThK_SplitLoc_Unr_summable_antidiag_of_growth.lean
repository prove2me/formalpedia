-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.summable_antidiag_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:04.439614+00:00
-- url     : https://prove2.me/submissions/ce4fabcf-3ed6-4e8c-a666-3481cbdeaff8

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_summable_geom_coeff
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {n : ℕ} (Q : Fin n → ℝ) (hQ : ∀ i, 1 ≤ Q i) {r : ℝ} (hr : 0 ≤ r)
    (hrQ : ∀ i, r * Q i < 1) (M : ℕ) (T : (Fin n → ℕ) → ℂ)
    (hT : ∀ a, T a = (∏ i, (Q i : ℂ) ^ (a i - M)) * T (fun i => min (a i) M)) :
    Summable fun t : ℕ => r ^ t * ‖∑ a ∈ Finset.piAntidiag Finset.univ t, T a‖ := by
  classical
  set B : ℝ := ∑ b ∈ Fintype.piFinset (fun _ : Fin n => Finset.range (M + 1)), ‖T b‖ with hB
  have hQ0 : ∀ i, 0 ≤ Q i := fun i => zero_le_one.trans (hQ i)
  have hBle : ∀ a : Fin n → ℕ, ‖T (fun i => min (a i) M)‖ ≤ B := fun a =>
    Finset.single_le_sum (f := fun b => ‖T b‖) (fun _ _ => norm_nonneg _)
      (Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (min_le_right _ _)))
  have hTle : ∀ a : Fin n → ℕ, ‖T a‖ ≤ (∏ i, Q i ^ a i) * B := fun a => by
    rw [hT a, norm_mul, norm_prod]
    refine mul_le_mul ?_ (hBle a) (norm_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (hQ0 i) _)
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hQ0 i)]
    exact pow_le_pow_right₀ (hQ i) (Nat.sub_le _ _)
  have hs := (summable_geom_coeff (fun i => ((r * Q i : ℝ) : ℂ)) fun i => by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hr (hQ0 i))]; exact hrQ i).mul_right B
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hr _) (norm_nonneg _)) (fun t => ?_) hs
  have h1 : (∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) t, ∏ i, ((r * Q i : ℝ) : ℂ) ^ a i) =
      ((∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) t, ∏ i, (r * Q i) ^ a i : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun a _ =>
    Finset.prod_nonneg fun i _ => pow_nonneg (mul_nonneg hr (hQ0 i)) _), Finset.sum_mul]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hr _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  have ht : ∑ i, a i = t := (Finset.mem_piAntidiag.1 ha).1
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ht, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hTle a) (pow_nonneg hr _)
end PositivityTheory.ThK.SplitLoc.Unr
