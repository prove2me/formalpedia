-- Prove2me | solution 1 for OpenMath.exists_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:09.367624+00:00
-- url     : https://prove2.me/submissions/9b795d02-69c9-4743-9076-473329e4b26f

module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Real.Basic
public import Definitions.Def_OpenMath_Common

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath
open SimpleGraph Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath
theorem _root_.solution {G : SimpleGraph α} (h : G.Connected) {v w : α} (hw : w ≠ v) :
    ∃ p, G.Adj p w ∧ G.dist v p + 1 = G.dist v w := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist w v
  have hnil : ¬ q.Nil := fun hn => hw hn.eq
  refine ⟨q.snd, (q.adj_snd hnil).symm, ?_⟩
  have h1 : G.dist q.snd v ≤ q.tail.length := dist_le q.tail
  have h2 : q.tail.length + 1 = q.length := q.length_tail_add_one hnil
  have h3 : G.dist w v ≤ G.dist w q.snd + G.dist q.snd v := h.dist_triangle
  have h4 : G.dist w q.snd = 1 := dist_eq_one_iff_adj.mpr (q.adj_snd hnil)
  rw [dist_comm (u := v) (v := q.snd), dist_comm (u := v) (v := w)]
  omega
end OpenMath
