-- Prove2me | solution 1 for WeightedCoordGames.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T12:01:52.170511+00:00
-- url     : https://prove2.me/submissions/a3c76763-7340-4931-aa7d-56ee3bbdd038

import Mathlib
import Definitions.Def_WeightedCoordGames_Model
import Definitions.Def_WeightedCoordGames_Algorithm

open WeightedCoordGames in
theorem solution {V M : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]
    {m v : ℕ} (O : OpenChain V m v) (C : V → Finset M) (hC : ∀ u, (C u).Nonempty)
    (s s' : V → M) (hs : (chainGame O C).toGame.IsJoint s)
    (hs' : (chainGame O C).toGame.IsJoint s')
    (hmu : O.mu C s = toLex (O.guard C s, toLex (0, toLex (O.prefixLen C s, -(O.nbr C s : ℤ)))))
    (hg : O.guard C s ≤ O.guard C s') (hp : O.prefixLen C s < O.prefixLen C s') :
    O.mu C s < O.mu C s' := by
  have hgm : O.guard C s ≤ m := by
    unfold OpenChain.guard
    apply Finset.sup_le
    intro j _
    exact j.isLt
  rw [hmu]
  unfold OpenChain.mu
  split_ifs with h1 h2
  · rw [Prod.Lex.toLex_lt_toLex]
    left
    show O.guard C s < m + 1
    omega
  · rw [Prod.Lex.toLex_lt_toLex']
    refine ⟨hg, fun _ => ?_⟩
    rw [Prod.Lex.toLex_lt_toLex]
    left
    show (0 : ℕ) < 1
    norm_num
  · rw [Prod.Lex.toLex_lt_toLex']
    refine ⟨hg, fun _ => ?_⟩
    rw [Prod.Lex.toLex_lt_toLex']
    refine ⟨le_refl _, fun _ => ?_⟩
    rw [Prod.Lex.toLex_lt_toLex]
    left
    exact hp
