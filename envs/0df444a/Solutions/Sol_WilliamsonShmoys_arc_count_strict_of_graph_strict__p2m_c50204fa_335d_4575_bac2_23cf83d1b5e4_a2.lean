-- Prove2me | solution 1 for WilliamsonShmoys.arc_count_strict_of_graph_strict__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:41:29.549871+00:00
-- url     : https://prove2.me/submissions/1fc600d3-18b1-4f51-b0fa-751bb15fa72a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V]
    (K L : SimpleGraph V) (hKL : K ≤ L) (hne : K ≠ L) :
    Nat.card {p : V × V // K.Adj p.1 p.2} <
      Nat.card {p : V × V // L.Adj p.1 p.2} := by
  classical
  change ({p : V × V | K.Adj p.1 p.2} : Set (V × V)).ncard <
      ({p : V × V | L.Adj p.1 p.2} : Set (V × V)).ncard
  have hex : ∃ u v : V, L.Adj u v ∧ ¬ K.Adj u v := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (le_antisymm hKL h)
  rcases hex with ⟨u, v, hLuv, hnKuv⟩
  have hsub : ({p : V × V | K.Adj p.1 p.2} : Set (V × V)) ⊆
      {p : V × V | L.Adj p.1 p.2} := by
    intro p hp
    change L.Adj p.1 p.2
    exact hKL (show K.Adj p.1 p.2 from hp)
  have hss : ({p : V × V | K.Adj p.1 p.2} : Set (V × V)) ⊂
      {p : V × V | L.Adj p.1 p.2} := by
    refine (Set.ssubset_iff_of_subset hsub).2 ⟨(u, v), ?_, ?_⟩
    · simpa using hLuv
    · simpa using hnKuv
  exact Set.ncard_lt_ncard hss (Set.toFinite _)
