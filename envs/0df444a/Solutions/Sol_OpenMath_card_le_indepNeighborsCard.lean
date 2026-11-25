-- Prove2me | solution 1 for OpenMath.card_le_indepNeighborsCard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:08.507865+00:00
-- url     : https://prove2.me/submissions/558de9d1-04d8-4873-ba5c-ed031c6c4025

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
theorem _root_.solution {G : SimpleGraph α} {u : α} {S : Finset α}
    (hS : ∀ x ∈ S, G.Adj u x) (hind : (S : Set α).Pairwise fun x y => ¬ G.Adj x y) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  let T : Finset (G.neighborSet u) := S.subtype (· ∈ G.neighborSet u)
  have hT : (G.induce (G.neighborSet u)).IsIndepSet (T : Set (G.neighborSet u)) := by
    intro a ha b hb hab
    simp only [T, mem_coe, mem_subtype] at ha hb
    simpa using hind ha hb (fun h => hab (Subtype.ext h))
  have hcard : T.card = S.card := by
    simp only [T, card_subtype]
    congr 1
    exact filter_true_of_mem fun x hx => hS x hx
  have := hT.card_le_indepNum
  unfold indepNeighborsCard
  omega
end OpenMath
