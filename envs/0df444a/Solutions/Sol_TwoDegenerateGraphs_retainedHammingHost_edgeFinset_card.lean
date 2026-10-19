-- Prove2me | solution 1 for TwoDegenerateGraphs.retainedHammingHost_edgeFinset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/952ee72d-ebfe-4d74-b2ce-f310fe55ea5c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingHost_adj_iff

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    (retainedHammingHost dimension radius retained).edgeFinset.card =
      (retainedHammingWordEdges dimension radius retained).card := by
  classical
  let toEdge :
      ∀ edge ∈ retainedHammingWordEdges dimension radius retained,
        Sym2 retained := fun edge hedge =>
    s(⟨(false, edge.1), by
        exact (Finset.mem_filter.mp hedge).2.2.1⟩,
      ⟨(true, edge.2), by
        exact (Finset.mem_filter.mp hedge).2.2.2⟩)
  have hcard :
      (retainedHammingWordEdges dimension radius retained).card =
        (retainedHammingHost dimension radius retained).edgeFinset.card := by
    apply Finset.card_bij toEdge
    · intro edge hedge
      have hdata := (Finset.mem_filter.mp hedge).2
      change
        s(⟨(false, edge.1), hdata.2.1⟩,
          ⟨(true, edge.2), hdata.2.2⟩) ∈
          (retainedHammingHost dimension radius retained).edgeFinset
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change (hammingHost dimension radius).Adj
        (false, edge.1) (true, edge.2)
      apply (hammingHost_adj_iff dimension radius _ _).mpr
      exact ⟨by simp, hdata.1⟩
    · intro first hfirst second hsecond hequal
      dsimp [toEdge] at hequal
      rcases (Sym2.eq_iff.mp hequal) with
        ⟨hleft, hright⟩ | ⟨hswap, _⟩
      · apply Prod.ext
        · exact congrArg (fun vertex : retained => vertex.val.2) hleft
        · exact congrArg (fun vertex : retained => vertex.val.2) hright
      · have hside :=
          congrArg (fun vertex : retained => vertex.val.1) hswap
        simp at hside
    · intro edge hedge
      induction edge using Sym2.inductionOn with
      | hf first second =>
        have hadj :
            (retainedHammingHost dimension radius retained).Adj
              first second := by
          exact (SimpleGraph.mem_edgeSet
            (retainedHammingHost dimension radius retained)).mp
              ((SimpleGraph.mem_edgeFinset).mp hedge)
        have hhost :
            (hammingHost dimension radius).Adj
              first.val second.val := hadj
        rcases first with ⟨⟨firstSide, firstWord⟩, hfirst⟩
        rcases second with ⟨⟨secondSide, secondWord⟩, hsecond⟩
        have hdata :=
          (hammingHost_adj_iff dimension radius
            (firstSide, firstWord) (secondSide, secondWord)).mp hhost
        cases firstSide <;> cases secondSide
        · simp at hdata
        · refine ⟨(firstWord, secondWord), ?_, ?_⟩
          · unfold retainedHammingWordEdges
            simp [hdata.2, hfirst, hsecond]
          · simp [toEdge]
        · have hreverse : hammingDist secondWord firstWord ≤ radius := by
            simpa [hammingDist_comm] using hdata.2
          refine ⟨(secondWord, firstWord), ?_, ?_⟩
          · unfold retainedHammingWordEdges
            simp [hreverse, hfirst, hsecond]
          · dsimp [toEdge]
            exact Sym2.eq_swap
        · simp at hdata
  exact hcard.symm
end TwoDegenerateGraphs
