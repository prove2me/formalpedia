-- Prove2me | solution 1 for PI.HookSteps.Cap.alt_contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:15.309802+00:00
-- url     : https://prove2.me/submissions/68efa9c5-7771-4407-98c9-b6956428ef97

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open Finset
variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]
namespace PI.HookSteps.Cap
theorem _root_.solution {k : ℕ} (Q : (Fin k → I) → 𝒰) (r : Fin (k + 1) → I) (b : I) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      ((k : ℕ) • (if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0) +
        ∑ j : Fin k, if r (σ j.succ) = b then
          Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) = 0 := by
  obtain ⟨A, hA⟩ : ∃ A : Equiv.Perm (Fin (k + 1)) → 𝒰,
      ∀ σ, A σ = if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0 := ⟨_, fun _ => rfl⟩
  have hB : ∀ (σ : Equiv.Perm (Fin (k + 1))) (j : Fin k),
      (if r (σ j.succ) = b then Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) =
        A (σ * Equiv.swap 0 j.succ) := by
    intro σ j
    have hf : Function.update (fun i => r (σ i.succ)) j (r (σ 0)) =
        fun i => r (σ (Equiv.swap 0 j.succ i.succ)) := by
      funext i
      by_cases h : i = j
      · subst h
        rw [Function.update_apply, if_pos rfl, Equiv.swap_apply_right]
      · rw [Function.update_apply, if_neg h, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i)
          (fun e => h (Fin.succ_injective _ e))]
    rw [hA]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [hf]
  have hS : ∀ j : Fin k, ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      A (σ * Equiv.swap 0 j.succ) =
      -∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A σ := by
    intro j
    rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin (k + 1)) j.succ)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [mul_assoc, Equiv.swap_mul_self, mul_one, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Fin.succ_ne_zero j).symm, Units.val_mul, Units.val_neg, Units.val_one,
      mul_neg_one, neg_smul]
  have e : ∀ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      ((k : ℕ) • (if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0) +
        ∑ j : Fin k, if r (σ j.succ) = b then
          Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) =
      (k : ℕ) • (((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A σ) +
        ∑ j : Fin k, ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A (σ * Equiv.swap 0 j.succ) := by
    intro σ
    rw [smul_add, Finset.smul_sum, smul_comm ((Equiv.Perm.sign σ : ℤˣ) : ℤ) (k : ℕ), ← hA σ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB σ j]
  rw [Finset.sum_congr rfl fun σ _ => e σ, Finset.sum_add_distrib, Finset.sum_comm,
    ← Finset.smul_sum]
  simp_rw [hS]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_neg, add_neg_cancel]
end PI.HookSteps.Cap
