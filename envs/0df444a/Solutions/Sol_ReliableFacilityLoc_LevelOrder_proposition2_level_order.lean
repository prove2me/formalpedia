-- Prove2me | solution 1 for ReliableFacilityLoc.LevelOrder.proposition2_level_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:42:43.321022+00:00
-- url     : https://prove2.me/submissions/cc3ae6a5-affa-4191-a979-864ea37eb90f

import Mathlib
import Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL
import Theorems.Thm_ReliableFacilityLoc_LevelOrder_swap_cost_identity
import Theorems.Thm_ReliableFacilityLoc_LevelOrder_emergency_cost_identity
import Theorems.Thm_ReliableFacilityLoc_LevelOrder_prob_pos_of_assigned

open Finset
open ReliableFacilityLoc.LevelOrder

theorem solution {I J R : ℕ} (D : Instance I J R)
    (hlam : ∀ i, 0 < D.lam i) (hq : ∀ k, 0 < D.q k)
    (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (hopt : D.IsOptimal X Y P)
    (i : Fin I) (j k : Fin (J + 1)) (r : Fin R)
    (hj : Y i j r.castSucc = 1) (hk : Y i k r.succ = 1) :
    D.dExt i j ≤ D.dExt i k := by
  obtain ⟨hfeas, hmin⟩ := hopt
  have hnn : ∀ l s, 0 ≤ Y i l s := fun l s => by
    rcases hfeas.Y_binary i l s with h | h <;> rw [h] <;> norm_num
  have hPpos := prob_pos_of_assigned D hq X Y P hfeas i j r.castSucc hj
  -- the level-`r` facility is regular
  induction j using Fin.lastCases with
  | last =>
    exfalso
    have h1 := hfeas.level_one i r.succ
    have hA : Y i k r.succ ≤ ∑ l, Y i l r.succ :=
      single_le_sum (fun l _ => hnn l r.succ) (mem_univ k)
    have hB : Y i (Fin.last J) r.castSucc ≤ ∑ s ∈ Iio r.succ, Y i (Fin.last J) s :=
      single_le_sum (fun s _ => hnn _ s) (by simp [Fin.castSucc_lt_succ])
    linarith
  | cast j' =>
    induction k using Fin.lastCases with
    | last =>
      obtain ⟨hf', hcost⟩ := emergency_cost_identity D X Y P hfeas i j' r hj hk
      have := hmin _ _ _ hf'
      have hd : D.dExt i j'.castSucc = D.d i j' := by simp [Instance.dExt]
      have he : D.dExt i (Fin.last J) = D.phi i := by simp [Instance.dExt]
      rw [hd, he]
      by_contra hlt
      push_neg at hlt
      have : D.lam i * P i j'.castSucc r.castSucc * (D.phi i - D.d i j') < 0 :=
        mul_neg_of_pos_of_neg (mul_pos (hlam i) hPpos) (by linarith)
      linarith
    | cast k' =>
      obtain ⟨hf', hcost⟩ := swap_cost_identity D X Y P hfeas i j' k' r hj hk
      have := hmin _ _ _ hf'
      have hd : ∀ l : Fin J, D.dExt i l.castSucc = D.d i l := fun l => by simp [Instance.dExt]
      rw [hd, hd]
      by_contra hlt
      push_neg at hlt
      have h1 : 0 < 1 - D.q k' := by linarith [D.q_lt_one k']
      have : D.lam i * (1 - D.q k') * (D.d i k' - D.d i j') * P i j'.castSucc r.castSucc < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos (hlam i) h1) (by linarith)) hPpos
      linarith
