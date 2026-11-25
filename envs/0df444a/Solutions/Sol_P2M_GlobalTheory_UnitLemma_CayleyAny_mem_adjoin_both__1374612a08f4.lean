-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_CayleyAny_mem_adjoin_both__1374612a08f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:13.414967+00:00
-- url     : https://prove2.me/submissions/f3cec4c0-2b43-4aa1-b635-26949f1f6ed0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_sub_inv_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyAny
open GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyAny
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A) (ξ a b : O) (Q : O[X])
    (hQm : Q.Monic) (hQ : aeval g Q = 0) (hQs : IsUnit (Q.eval ξ)) (hab : IsUnit (ξ * a - b))
    (hY : Y * (g - algebraMap O A ξ) = algebraMap O A a * g - algebraMap O A b) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  constructor
  · obtain ⟨w, hw, hgw⟩ := sub_inv_mem g ξ Q hQ hQs
    have e : Y = (algebraMap O A a * g - algebraMap O A b) * w := by
      linear_combination (-Y) * hgw + w * hY
    rw [e]
    exact mul_mem (sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
      (Subalgebra.algebraMap_mem _ _)) hw
  · set n := Q.natDegree
    let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (C ξ * X - C b) ^ i * (X - C a) ^ (n - i)
    have hgY : g * (Y - algebraMap O A a) = algebraMap O A ξ * Y - algebraMap O A b := by
      linear_combination hY
    have hR : aeval Y R = 0 := by
      have : aeval Y R = (Y - algebraMap O A a) ^ n * aeval g Q := by
        conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
        simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [← hgY, mul_pow, Algebra.smul_def]
        have : (Y - algebraMap O A a) ^ n = (Y - algebraMap O A a) ^ i * (Y - algebraMap O A a) ^ (n - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hin]
        rw [this]; ring
      rw [this, hQ, mul_zero]
    have hRe : R.eval a = (ξ * a - b) ^ n := by
      simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
      rw [Finset.sum_eq_single n]
      · simp [n, hQm.coeff_natDegree]
      · intro i hi hin
        have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
        rw [zero_pow this.ne', mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
    have hRu : IsUnit (R.eval a) := by
      rw [hRe]; exact hab.pow _
    obtain ⟨v, hv, hYv⟩ := sub_inv_mem Y a R hR hRu
    have e : g = (algebraMap O A ξ * Y - algebraMap O A b) * v := by
      linear_combination (-g) * hYv + v * hgY
    rw [e]
    exact mul_mem (sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
      (Subalgebra.algebraMap_mem _ _)) hv
end GlobalTheory.UnitLemma.CayleyAny
