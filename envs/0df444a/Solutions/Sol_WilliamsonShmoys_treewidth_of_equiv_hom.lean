-- Prove2me | solution 1 for WilliamsonShmoys.treewidth_of_equiv_hom
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T08:09:20.13241+00:00
-- url     : https://prove2.me/submissions/3f50dabc-1913-4c25-9b09-2d50578fca4f

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

open RobertsonSeymour1986.GM5

theorem solution {V V' : Type} [DecidableEq V] [DecidableEq V'] (G : SimpleGraph V) (G' : SimpleGraph V')
    (e : V ≃ V') (w : ℕ) (hadj : ∀ a b, G'.Adj a b → G.Adj (e.symm a) (e.symm b))
    (h : TreewidthLE G w) : TreewidthLE G' w := by
  obtain ⟨T, hT, t, X, ⟨htree, hcov, hedge, hpath⟩, hcard⟩ := h
  refine ⟨T, hT, t, fun s => (X s).map e.toEmbedding, ⟨htree, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    obtain ⟨s, hs⟩ := hcov (e.symm v)
    exact ⟨s, Finset.mem_map_equiv.2 hs⟩
  · intro x y hxy
    obtain ⟨s, hx, hy⟩ := hedge _ _ (hadj x y hxy)
    exact ⟨s, Finset.mem_map_equiv.2 hx, Finset.mem_map_equiv.2 hy⟩
  · intro s s' s'' p hp hs' x hx
    rw [Finset.mem_inter] at hx
    have h1 := Finset.mem_map_equiv.1 hx.1
    have h2 := Finset.mem_map_equiv.1 hx.2
    exact Finset.mem_map_equiv.2 (hpath s s' s'' p hp hs' (Finset.mem_inter.2 ⟨h1, h2⟩))
  · intro s
    rw [Finset.card_map]
    exact hcard s
