-- Prove2me | solution 1 for WeberGittins.Suboptimality.greatest_prevailing_charge_ge_gittins
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:53:39.103645+00:00
-- url     : https://prove2.me/submissions/6227e108-c13e-4e2d-af0f-398835854ea8

import Definitions.Def_GittinsChargeInterleaving

open BanditAlgorithm


namespace WeberGittins.Suboptimality

lemma gpc_cnt_succ {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (t : ℕ) :
    stackPullCountBefore a i (t + 1) = stackPullCountBefore a i t + (if a t = i then 1 else 0) := by
  unfold stackPullCountBefore
  rw [Finset.sum_range_succ]

lemma gpc_cnt_mono {k : ℕ} (a : ℕ → Fin k) (i : Fin k) {s t : ℕ} (h : s ≤ t) :
    stackPullCountBefore a i s ≤ stackPullCountBefore a i t := by
  unfold stackPullCountBefore
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma gpc_cnt_sum {k : ℕ} (a : ℕ → Fin k) (t : ℕ) :
    ∑ i : Fin k, stackPullCountBefore a i t = t := by
  unfold stackPullCountBefore
  rw [Finset.sum_comm]
  simp

lemma gpc_last_pull {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (t : ℕ)
    (h : 0 < stackPullCountBefore a i t) :
    ∃ s < t, a s = i ∧ stackPullCountBefore a i s + 1 = stackPullCountBefore a i t := by
  induction t with
  | zero => simp [stackPullCountBefore] at h
  | succ t ih =>
    by_cases hat : a t = i
    · exact ⟨t, Nat.lt_succ_self t, hat, by rw [gpc_cnt_succ]; simp [hat]⟩
    · rw [gpc_cnt_succ] at h ⊢
      simp only [hat, if_false, add_zero] at h ⊢
      obtain ⟨s, hs, h1, h2⟩ := ih h
      exact ⟨s, Nat.lt_succ_of_lt hs, h1, h2⟩

theorem gpc_core {k : ℕ} (H : Fin k → ℕ → ℝ)
    (hH : ∀ i, Antitone (H i)) (astar : ℕ → Fin k)
    (hastar : IsGreedyChargeStackInterleaving H astar) (a : ℕ → Fin k) (t : ℕ) :
    (⨆ i : Fin k, H i (stackPullCountBefore astar i t)) ≤
      ⨆ i : Fin k, H i (stackPullCountBefore a i t) := by
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · simp
  refine ciSup_le fun j => ?_
  have hb : BddAbove (Set.range fun i : Fin k => H i (stackPullCountBefore a i t)) :=
    (Set.finite_range _).bddAbove
  by_cases hc : stackPullCountBefore a j t ≤ stackPullCountBefore astar j t
  · exact le_ciSup_of_le hb j (hH j hc)
  · push_neg at hc
    have : ∃ i, stackPullCountBefore a i t < stackPullCountBefore astar i t := by
      by_contra hne
      push_neg at hne
      have h1 := gpc_cnt_sum a t
      have h2 := gpc_cnt_sum astar t
      have hlt : ∑ i : Fin k, stackPullCountBefore astar i t <
          ∑ i : Fin k, stackPullCountBefore a i t :=
        Finset.sum_lt_sum (fun i _ => hne i) ⟨j, Finset.mem_univ _, hc⟩
      omega
    obtain ⟨i, hi⟩ := this
    obtain ⟨s, hst, hsi, hcnt⟩ := gpc_last_pull astar i t (by omega)
    have g := hastar s j
    rw [hsi] at g
    have g2 : H j (stackPullCountBefore astar j t) ≤ H j (stackPullCountBefore astar j s) :=
      hH j (gpc_cnt_mono astar j hst.le)
    have g3 : H i (stackPullCountBefore astar i s) ≤ H i (stackPullCountBefore a i t) :=
      hH i (by omega)
    exact le_ciSup_of_le hb i (g2.trans (g.trans g3))

end WeberGittins.Suboptimality

open WeberGittins.Suboptimality
open BanditAlgorithm

theorem solution {k : ℕ} (H : Fin k → ℕ → ℝ)
    (hH : ∀ i, Antitone (H i)) (astar : ℕ → Fin k)
    (hastar : IsGreedyChargeStackInterleaving H astar) (a : ℕ → Fin k) (t : ℕ) :
    (⨆ i : Fin k, H i (stackPullCountBefore astar i t)) ≤
      ⨆ i : Fin k, H i (stackPullCountBefore a i t) := by
  exact gpc_core H hH astar hastar a t
