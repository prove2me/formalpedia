-- Prove2me | solution 1 for WilliamsonShmoys.treewidthLE_of_graph_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:41:31.074423+00:00
-- url     : https://prove2.me/submissions/e7e924d5-bcc3-44de-949a-0f2df5c64944

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

theorem solution {α β : Type} [DecidableEq α] [DecidableEq β] (K : SimpleGraph α) (H : SimpleGraph β) (f : α → β) (w : Nat) (hinj : Function.Injective f) (hadj : ∀ x y, K.Adj x y ↔ H.Adj (f x) (f y)) : RobertsonSeymour1986.GM5.TreewidthLE H w → RobertsonSeymour1986.GM5.TreewidthLE K w := by
  classical
  rintro ⟨T, hT, t, X, ⟨htree, hcov, hedge, hpath⟩, hcard⟩
  refine ⟨T, hT, t, fun s => (X s).preimage f hinj.injOn, ⟨htree, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    obtain ⟨s, hs⟩ := hcov (f v)
    exact ⟨s, by simpa using hs⟩
  · intro x y hxy
    obtain ⟨s, hx, hy⟩ := hedge (f x) (f y) ((hadj x y).1 hxy)
    exact ⟨s, by simpa using hx, by simpa using hy⟩
  · intro s s' s'' p hp hs' y hy
    simp only [Finset.mem_inter, Finset.mem_preimage] at hy ⊢
    exact hpath s s' s'' p hp hs' (Finset.mem_inter.2 hy)
  · intro s
    exact (Finset.card_le_card_of_injOn f (fun y hy => by simpa using hy) hinj.injOn).trans (hcard s)
