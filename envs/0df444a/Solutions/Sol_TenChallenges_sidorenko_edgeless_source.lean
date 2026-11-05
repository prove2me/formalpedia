-- Prove2me | solution 1 for TenChallenges.sidorenko_edgeless_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:20.000232+00:00
-- url     : https://prove2.me/submissions/a45ea25c-3a43-493f-8c13-48232c4a4021

import Definitions.Def_TenChallenges_Challenge_04
import Mathlib.SetTheory.Cardinal.Finite

open SimpleGraph

/-- An edgeless source graph satisfies Sidorenko's inequality with equality. -/
theorem solution {W V : Type*} [Fintype W] [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : SidorenkoFor (⊥ : SimpleGraph W) G := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [SidorenkoFor, homDensity, Nat.card_fun, Nat.card_eq_fintype_card, hn]
