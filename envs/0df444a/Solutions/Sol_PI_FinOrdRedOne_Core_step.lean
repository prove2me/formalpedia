-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:58:47.129265+00:00
-- url     : https://prove2.me/submissions/8d3b4eb4-3e41-4b23-8f1e-c9ebb95ce7eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_neg
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_mono
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_smul
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_nsmul
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_sum
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_pow_smul
import Theorems.Thm_PI_FinOrdRedOne_Core_one_add_pow_eq
import Theorems.Thm_PI_FinOrdRedOne_Core_smul_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.FinOrdRedOne.Core
theorem _root_.solution [IsDomain R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hp0 : (p : R) ≠ 0)
    (hunit : ∀ l : ℕ, l.Prime → l ≠ p → IsUnit (l : R))
    (l : ℕ) (hl : l.Prime) (X : Matrix n n R) (a : ℕ) (ha : 1 ≤ a)
    (hpow : (1 + (p : R) ^ a • X) ^ l = 1) : PDvd (p : R) (a + 1) ((p : R) ^ a • X) := by
  set D : Matrix n n R := (p : R) ^ a • X with hD
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := hl.two_le; omega⟩
  rw [one_add_pow_eq] at hpow
  set S := ∑ i ∈ range (k + 1), (k + 2).choose (i + 2) • D ^ (i + 2) with hS
  have hlin : (k + 2) • D = -S := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    have := congrArg (· - (1 : Matrix n n R)) hpow
    simpa only [add_sub_cancel_right, sub_self] using this
  by_cases hlp : k + 2 = p
  ·
    have hS2 : PDvd (p : R) (a + 2) S := by
      refine pdvd_sum _ _ fun i hi => ?_
      have hi' : i + 2 ≤ p := by rw [Finset.mem_range] at hi; omega
      rcases lt_or_eq_of_le hi' with hlt | heq
      · obtain ⟨c, hc⟩ := hp.dvd_choose_self (by omega : i + 2 ≠ 0) hlt
        rw [hlp, hc, mul_nsmul]
        refine pdvd_nsmul _ ?_
        rw [← Nat.cast_smul_eq_nsmul R]
        obtain ⟨Y, hY⟩ := pdvd_pow_smul (p : R) a (i + 2) X
        refine pdvd_mono (k := 1 + a * (i + 2)) (by nlinarith) ⟨Y, ?_⟩
        rw [hD, hY, smul_smul, ← pow_succ', add_comm]
      · refine pdvd_nsmul _ ?_
        refine pdvd_mono (k := a * (i + 2)) ?_ (pdvd_pow_smul (p : R) a (i + 2) X)
        rw [heq]; nlinarith
    have hpD : PDvd (p : R) (a + 2) ((p : R) • D) := by
      rw [← hlp] at hS2 ⊢
      have := pdvd_neg hS2
      rw [← hlin, ← Nat.cast_smul_eq_nsmul R] at this
      push_cast at this ⊢
      exact this
    obtain ⟨Y, hY⟩ := hpD
    refine ⟨Y, ?_⟩
    have hne : (p : R) ^ (a + 1) ≠ 0 := pow_ne_zero _ hp0
    have hXY : X = (p : R) • Y := by
      apply smul_cancel hne
      rw [hD, smul_smul, ← pow_succ'] at hY
      rw [hY, smul_smul, ← pow_succ]
    rw [hD, hXY, smul_smul, ← pow_succ]
  ·
    have hS1 : PDvd (p : R) (a + 1) S := by
      refine pdvd_sum _ _ fun i _ => pdvd_nsmul _ ?_
      exact pdvd_mono (k := a * (i + 2)) (by nlinarith) (pdvd_pow_smul (p : R) a (i + 2) X)
    obtain ⟨u, hu⟩ := hunit (k + 2) hl hlp
    have h1 : PDvd (p : R) (a + 1) (((k + 2 : ℕ) : R) • D) := by
      rw [Nat.cast_smul_eq_nsmul, hlin]
      exact pdvd_neg hS1
    have h2 := pdvd_smul ((u⁻¹ : Rˣ) : R) h1
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h2
end PI.FinOrdRedOne.Core
