-- Prove2me | solution 2 for SecretaryWD.DiscLower.discounted_secretary_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:47:49.234544+00:00
-- url     : https://prove2.me/submissions/c237e38b-f13e-4a2e-8aa4-11f42181c2ae

import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances
import Theorems.Thm_SecretaryWD_DiscLower_competitive_stopByProb_ge

-- carved verbatim out of submission be6a3f45-8889-4b0d-be74-4002337b528a, lines 883-888

section
open SecretaryWD
open SecretaryWD.DiscLower
open Finset

lemma sdl_telescope {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) (k : ℕ) :
    ∑ t ∈ univ.filter (fun t : Fin n => t.val < k), stopProb A h t
      + ∏ s ∈ univ.filter (fun s : Fin n => s.val < k), (1 - A.stop s h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < n
    · have hset : univ.filter (fun t : Fin n => t.val < k + 1)
          = insert (⟨k, hk⟩ : Fin n) (univ.filter (fun t : Fin n => t.val < k)) := by
        ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
      have hnot : (⟨k, hk⟩ : Fin n) ∉ univ.filter (fun t : Fin n => t.val < k) := by simp
      rw [hset, sum_insert hnot, prod_insert hnot]
      have hp : stopProb A h ⟨k, hk⟩ = A.stop ⟨k, hk⟩ h *
          ∏ s ∈ univ.filter (fun s : Fin n => s.val < k), (1 - A.stop s h) := by
        unfold stopProb
        congr 1
      rw [hp]; linarith
    · have hset : univ.filter (fun t : Fin n => t.val < k + 1)
          = univ.filter (fun t : Fin n => t.val < k) := by
        ext x; simp only [mem_filter, mem_univ, true_and]; have := x.2; omega
      rw [hset]; exact ih

lemma sdl_sum_stopProb_le_one {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) (k : ℕ) :
    ∑ t ∈ univ.filter (fun t : Fin n => t.val < k), stopProb A h t ≤ 1 := by
  have := sdl_telescope A h k
  have : 0 ≤ ∏ s ∈ univ.filter (fun s : Fin n => s.val < k), (1 - A.stop s h) :=
    prod_nonneg fun s _ => sub_nonneg.mpr (A.stop_le_one s h)
  linarith

lemma sdl_stopByProb_le_one {n : ℕ} (v : Fin n → ℝ) (A : StoppingRule n) (k : ℕ) :
    stopByProb v A k ≤ 1 := by
  unfold stopByProb
  have hN : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc _ ≤ 1 / (n.factorial : ℝ) * ∑ π : Equiv.Perm (Fin n), (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun π _ => sdl_sum_stopProb_le_one A _ k)
          (by positivity)
    _ = 1 := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp

lemma sdl_goal_core (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c)) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * c ∧
      (c : ℝ) * expectedValue (discount c) (hardInstance c t) A <
        10 * expectedOPT (discount c) (hardInstance c t) := by
  by_contra hcon
  push_neg at hcon
  have hA : ∀ s : ℕ, 1 ≤ s → s ≤ 2 * c →
      expectedOPT (discount c) (hardInstance c s) ≤
        (c : ℝ) / 10 * expectedValue (discount c) (hardInstance c s) A := by
    intro s h1 h2
    have := hcon s h1 h2
    linarith
  have h := SecretaryWD.DiscLower.competitive_stopByProb_ge c hc A hA (2 * c) (by omega) le_rfl
  have h1 := sdl_stopByProb_le_one (hardInstance c (2 * c)) A (blockEnd c (2 * c))
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  have : ((2 * c : ℕ) : ℝ) / c = 2 := by push_cast; field_simp
  linarith

end

section
open SecretaryWD.DiscLower

theorem solution (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c)) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * c ∧
      (c : ℝ) * expectedValue (discount c) (hardInstance c t) A <
        10 * expectedOPT (discount c) (hardInstance c t) := by
  exact sdl_goal_core c hc A

end
