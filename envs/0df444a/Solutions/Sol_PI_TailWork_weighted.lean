-- Prove2me | solution 1 for PI.TailWork.weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:25.06669+00:00
-- url     : https://prove2.me/submissions/7553f86e-8b2d-4288-a3a1-581765b5561e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
import Theorems.Thm_PI_TailWork_sum_log_block
import Theorems.Thm_PI_TailWork_sum_Ico_tele
import Theorems.Thm_PI_TailWork_w_nonneg
import Theorems.Thm_PI_TailWork_w_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)
      ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) := by
  classical
  set N := k + 1 + Q.sup id + 1 with hN
  have hw : ∀ p ∈ Q, g ((p + 1) / 2) - g p = ∑ m ∈ Ico ((p + 1) / 2) p, (g m - g (m + 1)) := by
    intro p hp
    have := (hQ p hp).2
    rw [sum_Ico_tele g _ _ (by omega)]
  have hL : ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)
      = ∑ m ∈ Ico (k + 1) N, (g m - g (m + 1)) *
          ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ) := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [hw p hp, Finset.mul_sum])]
    rw [Finset.sum_comm' (t' := Ico (k + 1) N)
      (s' := fun m => Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p))]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)
    · intro p m
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨hp, h1, h2⟩
        have := (hQ p hp).2
        have hs : p ≤ Q.sup id := Finset.le_sup (f := id) hp
        exact ⟨⟨hp, h1, h2⟩, by omega, by omega⟩
      · rintro ⟨⟨hp, h1, h2⟩, _, _⟩
        exact ⟨hp, h1, h2⟩
  rw [hL]
  have hb : ∀ m ∈ Ico (k + 1) N, (g m - g (m + 1)) *
      ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)
        ≤ Real.log 4 * (h m - h (m + 1)) := by
    intro m hm
    have hm2 : 2 ≤ m := by simp only [Finset.mem_Ico] at hm; omega
    have hin : ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)
        ≤ (m : ℝ) * Real.log 4 := by
      refine le_trans ?_ (sum_log_block m)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
        exact ⟨⟨hp.2.2, by omega⟩, (hQ p hp.1).1⟩
      · intro p _ _
        exact Real.log_natCast_nonneg p
    calc _ ≤ (g m - g (m + 1)) * ((m : ℝ) * Real.log 4) :=
          mul_le_mul_of_nonneg_left hin (w_nonneg m hm2)
      _ = Real.log 4 * ((g m - g (m + 1)) * m) := by ring
      _ = _ := by rw [w_mul m hm2]
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum, sum_Ico_tele h _ _ (by omega)]
  have hk1 : h (k + 1) = 1 / (k : ℝ) + 1 / ((k : ℝ) + 1) := by
    unfold h
    push_cast
    rw [add_sub_cancel_right]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hN0 : 0 ≤ h N := by
    unfold h
    exact add_nonneg (one_div_nonneg.2 (by linarith)) (one_div_nonneg.2 (by linarith))
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [hk1]
  exact mul_le_mul_of_nonneg_left (by linarith) hl
end PI.TailWork
