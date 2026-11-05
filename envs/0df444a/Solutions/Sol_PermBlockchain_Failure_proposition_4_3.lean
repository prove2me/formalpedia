-- Prove2me | solution 1 for PermBlockchain.Failure.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:41:35.510353+00:00
-- url     : https://prove2.me/submissions/fcd9290a-c0c5-423d-aaa7-93e7855a0269

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

open PermBlockchain.Failure in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing) :
    M.WM .F < M.WM .P ∧ M.WM .P < M.WM .N := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hM.two_le_m
  have hpos := hM.χ_pos
  have hN : M.WM .N = 0 := by
    simp [Model.WM, Model.payoff, Model.grossProfit, Scenario.profile]
  have hP : M.WM .P = - ∑ i ∈ Finset.univ.filter (fun i : Mfr m => i.IsHigh), M.χ i := by
    have h1 : ∀ i : Mfr m, M.payoff Scenario.P.profile i = if i.IsHigh then -M.χ i else 0 := by
      intro i
      by_cases hi : i.IsHigh
      · have : (Scenario.P.profile : Mfr m → Bool) i = true := hi
        simp [Model.payoff, Model.grossProfit, this, hi]
      · have : (Scenario.P.profile : Mfr m → Bool) i = false := by
          simpa [Mfr.IsHigh, Scenario.profile] using hi
        simp [Model.payoff, Model.grossProfit, this, hi]
    simp only [Model.WM, h1, ← Finset.sum_filter, Finset.sum_neg_distrib]
  have hF : M.WM .F = - ∑ i, M.χ i := by
    simp [Model.WM, Model.payoff, Model.grossProfit, Scenario.profile]
  have hhigh : 0 < ∑ i ∈ Finset.univ.filter (fun i : Mfr m => i.IsHigh), M.χ i := by
    apply Finset.sum_pos
    · intro i _; exact hpos i
    · exact ⟨(0, true, ⟨0, hm⟩), Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  have hlow : 0 < ∑ i ∈ Finset.univ.filter (fun i : Mfr m => ¬ i.IsHigh), M.χ i := by
    apply Finset.sum_pos
    · intro i _; exact hpos i
    · exact ⟨(0, false, ⟨0, hm⟩), Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [Mfr.IsHigh]⟩⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Mfr m => i.IsHigh) M.χ
  rw [hN, hP, hF]
  constructor <;> linarith
