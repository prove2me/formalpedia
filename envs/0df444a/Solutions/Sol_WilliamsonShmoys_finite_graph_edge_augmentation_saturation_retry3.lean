-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_edge_augmentation_saturation_retry3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:48:28.057538+00:00
-- url     : https://prove2.me/submissions/82238f65-b97b-405c-92f0-de05ba96250c

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V -> Prop) (L : SimpleGraph V) (M : Nat) (hP : P L) (hBound : forall G : SimpleGraph V, P G -> G.edgeSet.ncard <= M) (hAugment : forall G : SimpleGraph V, P G -> G.edgeSet.ncard < M -> exists H : SimpleGraph V, G <= H /\ P H /\ H.edgeSet.ncard = G.edgeSet.ncard + 1) : exists K : SimpleGraph V, L <= K /\ P K /\ K.edgeSet.ncard = M := by
  have key : ∀ n : ℕ, ∀ G : SimpleGraph V, L ≤ G → P G → M - G.edgeSet.ncard = n →
      ∃ K : SimpleGraph V, L ≤ K ∧ P K ∧ K.edgeSet.ncard = M := by
    intro n
    induction n with
    | zero =>
      intro G hLG hG hn
      exact ⟨G, hLG, hG, le_antisymm (hBound G hG) (by omega)⟩
    | succ n ih =>
      intro G hLG hG hn
      obtain ⟨H, hGH, hH, hc⟩ := hAugment G hG (by omega)
      exact ih H (hLG.trans hGH) hH (by omega)
  exact key _ L le_rfl hP rfl
