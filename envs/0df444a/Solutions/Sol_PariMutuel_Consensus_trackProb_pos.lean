-- Prove2me | solution 1 for PariMutuel.Consensus.trackProb_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:46:09.451707+00:00
-- url     : https://prove2.me/submissions/7b42197a-567c-4629-8594-982d7cca33cb

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi

open PariMutuel.Consensus in
theorem solution {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (j : Fin n) : 0 < M.trackProb ξ j := by
  obtain ⟨i, hi⟩ := M.P_col_pos j
  have hS : 0 < ∑ s, M.P i s * ξ i s := hξ.2.1 i
  have hpos : 0 < M.b i * M.P i j / ∑ s, M.P i s * ξ i s :=
    div_pos (mul_pos (M.b_pos i) hi) hS
  unfold Market.trackProb
  exact lt_of_lt_of_le hpos
    (Finset.le_sup' (fun i => M.b i * M.P i j / ∑ s, M.P i s * ξ i s) (Finset.mem_univ i))
