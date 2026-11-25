-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_sum_steps_eq_rootPairing_ba53cdb7f981
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:20.480222+00:00
-- url     : https://prove2.me/submissions/da359f14-4443-482f-b9b1-f4188ba8e368

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sum_fin_telescope_d731859c771b
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (N p : ℕ) (lam : Fin N → ℝ) (u : LowerPair N → ℂ) :
    ∑ k : Fin N, (if h : k.val + 1 < N then
      (lam k - lam ⟨k.val + 1, h⟩) * tailSum p (k.val + 1) (lowerMatrix u) else 0) =
      ∑ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 := by
  set Λ : ℕ → ℝ := fun n => if h : n < N then lam ⟨n, h⟩ else 0 with hΛ
  set A : Fin N → Fin N → ℝ := fun a b => sigSign p b * sigSign p a * ‖lowerMatrix u a b‖ ^ 2
    with hA
  have step1 : ∀ k : Fin N, (if h : k.val + 1 < N then
      (lam k - lam ⟨k.val + 1, h⟩) * tailSum p (k.val + 1) (lowerMatrix u) else 0) =
      ∑ b : Fin N, ∑ a : Fin N,
        (if b.val ≤ k.val ∧ k.val < a.val then Λ k - Λ (k.val + 1) else 0) * A a b := by
    intro k
    by_cases h : k.val + 1 < N
    · rw [dif_pos h, tailSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have e1 : Λ k = lam k := by simp [hΛ, k.isLt]
      have e2 : Λ (k.val + 1) = lam ⟨k.val + 1, h⟩ := by simp [hΛ, h]
      by_cases hba : b.val ≤ k.val ∧ k.val < a.val
      · rw [if_pos (by omega), if_pos hba, e1, e2, hA]
      · rw [if_neg (by omega), if_neg hba]
        simp
    · rw [dif_neg h]
      symm
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg (by have := a.isLt; omega)]
      simp
  have step2 : (∑ k : Fin N, ∑ b : Fin N, ∑ a : Fin N,
      (if b.val ≤ k.val ∧ k.val < a.val then Λ k - Λ (k.val + 1) else 0) * A a b) =
      ∑ a : Fin N, ∑ b : Fin N, if b < a then (Λ b - Λ a) * A a b else 0 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul]
    by_cases hba : b < a
    · rw [if_pos hba, sum_fin_telescope Λ b.val a.val hba a.isLt.le]
    · have hba' : ¬ b.val < a.val := fun h' => hba h'
      rw [if_neg hba, Finset.sum_eq_zero (fun k _ => if_neg (by omega)), zero_mul]
  have step3 : ∑ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 =
      ∑ a : Fin N, ∑ b : Fin N, if b < a then (Λ b - Λ a) * A a b else 0 := by
    have e : ∀ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 =
        (fun x : Fin N × Fin N => if x.2 < x.1 then (Λ x.2 - Λ x.1) * A x.1 x.2 else 0) q.1 := by
      rintro ⟨⟨a, b⟩, hab⟩
      show _ = if b < a then (Λ b - Λ a) * A a b else 0
      rw [if_pos hab]
      have hl : lowerMatrix u a b = u ⟨(a, b), hab⟩ := by simp [lowerMatrix, hab]
      have hab' : b.val < a.val := hab
      simp only [hA, hΛ, hl, rootPairing, sigSign, dif_pos a.isLt, dif_pos b.isLt, Fin.eta]
      split_ifs <;> first | ring1 | (exfalso; omega)
    rw [Fintype.sum_congr _ _ e]
    rw [← Finset.sum_subtype (Finset.univ.filter fun x : Fin N × Fin N => x.2 < x.1) (by simp)
      (fun x : Fin N × Fin N => if x.2 < x.1 then (Λ x.2 - Λ x.1) * A x.1 x.2 else 0)]
    rw [Finset.sum_filter_of_ne (fun x _ hx => by by_contra h; exact hx (if_neg h)),
      Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun k _ => step1 k, step2, step3]
end GroundTheory.Heights₂.Heights.FourB
