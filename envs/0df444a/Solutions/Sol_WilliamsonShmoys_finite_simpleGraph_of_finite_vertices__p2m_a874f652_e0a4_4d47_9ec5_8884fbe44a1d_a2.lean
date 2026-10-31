-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_of_finite_vertices__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:11:42.60964+00:00
-- url     : https://prove2.me/submissions/449b79d4-cfa5-41fb-a7c5-4dd565f92398

import Mathlib

theorem solution {V : Type} [Finite V] : Finite (SimpleGraph V) := by
  classical
  let adjacencySet : SimpleGraph V → Set (V × V) := fun G =>
    {p | G.Adj p.1 p.2}
  have hinj : Function.Injective adjacencySet := by
    intro G H h
    apply SimpleGraph.ext
    funext v w
    change ((v, w) ∈ adjacencySet G) = ((v, w) ∈ adjacencySet H)
    exact congrArg (fun s : Set (V × V) => (v, w) ∈ s) h
  exact Finite.of_injective adjacencySet hinj