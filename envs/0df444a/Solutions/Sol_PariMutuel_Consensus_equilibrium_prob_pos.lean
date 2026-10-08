-- Prove2me | solution 1 for PariMutuel.Consensus.equilibrium_prob_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:48:12.560857+00:00
-- url     : https://prove2.me/submissions/802cabe2-9c22-48a2-8667-cdacd9a370c2

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

open PariMutuel.Consensus in
theorem solution {m n : ℕ} (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ)
    (h : M.IsEquilibrium π β) (j : Fin n) : 0 < π j := by
  obtain ⟨hπ, hβ, hb, hcol, h3⟩ := h
  rcases (hπ j).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨i, hi⟩ := M.P_col_pos j
    have hbpos : ∑ k : Fin n, (0 : ℝ) < ∑ k, β i k := by
      rw [hb i, Finset.sum_const_zero]; exact M.b_pos i
    obtain ⟨k, -, hk⟩ := Finset.exists_lt_of_sum_lt hbpos
    have hπk : 0 < π k := by
      rw [← hcol k]
      exact lt_of_lt_of_le hk
        (Finset.single_le_sum (f := fun i' => β i' k) (fun i' _ => hβ i' k) (Finset.mem_univ i))
    have key := h3 i k hk j
    rw [← heq, mul_zero] at key
    have : 0 < M.P i j * π k := mul_pos hi hπk
    linarith
