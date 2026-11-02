-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T20:50:53.959524+00:00
-- url     : https://prove2.me/submissions/485ca1ba-377c-4c6f-b2cb-08e9f10ad22b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) ∧
      (∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
        letI : DecidableRel U.Adj := dU
        letI : DecidableRel W.Adj := dW
        HasPlanarDrawingOn W →
        U.edgeFinset ⊆ W.edgeFinset →
        W.edgeFinset = U.edgeFinset) := by
  classical
  letI : DecidableRel T.Adj := dT
  let P : SimpleGraph V → Prop := fun G =>
    HasPlanarDrawingOn G ∧ T.edgeFinset ⊆ G.edgeFinset
  have hPT : P T := by
    refine ⟨hT, ?_⟩
    intro e he
    simpa using he
  let S : Finset (SimpleGraph V) := Finset.univ.filter P
  have hS : S.Nonempty := by
    refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ T, hPT⟩⟩
  obtain ⟨U, hUmem, hUmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  have hPU : P U := (Finset.mem_filter.mp hUmem).2
  refine ⟨U, Classical.decRel U.Adj, hPU.1, hPU.2, ?_⟩
  intro W dW hW hUW
  letI : DecidableRel W.Adj := Classical.decRel W.Adj
  letI : DecidableRel U.Adj := Classical.decRel U.Adj
  have hUW' : U.edgeFinset ⊆ W.edgeFinset := by
    simpa using hUW
  have hPW : P W := ⟨hW, hPU.2.trans hUW'⟩
  have hWmem : W ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ W, hPW⟩
  have hcard : W.edgeFinset.card ≤ U.edgeFinset.card := hUmax W hWmem
  have hEq : U.edgeFinset = W.edgeFinset :=
    Finset.eq_of_subset_of_card_le hUW' hcard
  simpa using hEq.symm
