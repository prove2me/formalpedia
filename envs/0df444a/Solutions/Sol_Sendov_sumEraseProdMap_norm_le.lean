-- Prove2me | solution 1 for Sendov.sumEraseProdMap_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:10.464861+00:00
-- url     : https://prove2.me/submissions/c178fb80-a77c-4611-b292-baf011a71feb

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdMap_eq_esymm
import Theorems.Thm_Sendov_sum_norm_sq_one_sub_le
import Theorems.Thm_Sendov_sq_sum_le_card_mul_sum_sq
import Theorems.Thm_Sendov_Multiset_esymm_card_pred_le
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖)
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set f : ℂ → ℝ := fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ with hf
  set bs : Multiset ℝ := q.map f with hbs
  have hbcard : bs.card = n - 1 := by rw [hbs, Multiset.card_map, hqcard]
  have hNcast : ((bs.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hbcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  have hNpos : (0 : ℝ) < (bs.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbs0 : bs ≠ 0 := by
    rw [hbs]
    simpa using hq0
  have hbnn : ∀ b ∈ bs, 0 ≤ b := by
    intro b hb
    rw [hbs] at hb
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hb
    exact norm_nonneg _
  have hsumnn : 0 ≤ bs.sum := Multiset.sum_nonneg hbnn
  -- the quadratic mean
  have hsq : (bs.map (fun b => b ^ 2)).sum ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
    rw [hbs, Multiset.map_map]
    exact sum_norm_sq_one_sub_le hqcard hq1 (by omega) hx
  have hβ0 : 0 ≤ QQ (a * x) (a ^ 2) t := by
    have hnn : (0 : ℝ) ≤ (bs.map (fun b => b ^ 2)).sum :=
      Multiset.sum_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact sq_nonneg u)
    nlinarith [hsq, hnn, hNcast, hNpos]
  -- Cauchy–Schwarz
  have hcs : (bs.sum) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 * QQ (a * x) (a ^ 2) t := by
    have h := sq_sum_le_card_mul_sum_sq bs hbnn
    rw [hNcast] at h
    nlinarith [h, hsq, hNcast, hNpos]
  have hmean : bs.sum / (bs.card : ℕ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) := by
    rw [div_le_iff₀ hNpos, hNcast]
    have hsqrt : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ 2 = QQ (a * x) (a ^ 2) t :=
      Real.sq_sqrt hβ0
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by rw [← hNcast]; exact hNpos
    have hprodnn : (0 : ℝ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) * ((n : ℝ) - 1) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hn1)
    nlinarith [hcs, hsqrt, hsumnn, hprodnn, hn1]
  -- Maclaurin
  have hmac := Multiset.esymm_card_pred_le bs hbnn hbs0
  rw [sumEraseProdMap_eq_esymm q f hq0, ← hbs]
  refine hmac.trans ?_
  have hpow : (bs.sum / (bs.card : ℕ)) ^ (bs.card - 1)
      ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
    refine pow_le_pow_left₀ (by positivity) hmean _
  have hfin : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1)
      = QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (QQ (a * x) (a ^ 2) t ^ ((1 : ℝ) / 2))
      (bs.card - 1), ← Real.rpow_mul hβ0]
    congr 1
    have hcast2 : ((bs.card - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [hbcard]
      have h2 : n - 1 - 1 = n - 2 := by omega
      rw [h2]
      push_cast [Nat.cast_sub (by omega : (2 : ℕ) ≤ n)]
      ring
    rw [hcast2]
    ring
  rw [hNcast] at *
  calc ((n : ℝ) - 1) * (bs.sum / ((n : ℝ) - 1)) ^ (bs.card - 1)
      ≤ ((n : ℝ) - 1) * Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [← hNcast] at hpow ⊢
        exact hpow
    _ = ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by rw [hfin]
end Sendov
