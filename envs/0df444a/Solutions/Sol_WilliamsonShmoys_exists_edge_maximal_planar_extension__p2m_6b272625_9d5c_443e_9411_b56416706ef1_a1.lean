-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:18.983105+00:00
-- url     : https://prove2.me/submissions/d9fe8cae-54fd-41ac-9f23-69f6d7fc2cdf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T) :
    ∃ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) ∧
      ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
        HasPlanarDrawingOn W →
        (letI : DecidableRel U.Adj := dU
         letI : DecidableRel W.Adj := dW
         U.edgeFinset ⊆ W.edgeFinset) →
        (letI : DecidableRel U.Adj := dU
         letI : DecidableRel W.Adj := dW
         W.edgeFinset ⊆ U.edgeFinset) := by
  classical
  let edges : SimpleGraph V → Finset (Sym2 V) := fun G => G.edgeFinset
  let P : SimpleGraph V → Prop :=
    fun G => HasPlanarDrawingOn G ∧ edges T ⊆ edges G
  let s : Finset (SimpleGraph V) := Finset.univ.filter P
  have hs : s.Nonempty := by
    refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ T, ?_⟩⟩
    exact ⟨hT, by intro e he; exact he⟩
  let edgeCount : SimpleGraph V → Nat := fun G => (edges G).card
  obtain ⟨U, hUs, hmax⟩ := Finset.exists_max_image s edgeCount hs
  have hUP : P U := (Finset.mem_filter.mp hUs).2
  let dU : DecidableRel U.Adj := Classical.decRel _
  refine ⟨U, dU, hUP.1, ?_, ?_⟩
  · intro e he
    have heT : e ∈ edges T := by
      simpa only [edges, SimpleGraph.mem_edgeFinset] using he
    have heU : e ∈ edges U := hUP.2 heT
    simpa only [edges, SimpleGraph.mem_edgeFinset] using heU
  · intro W dW hW hUW
    letI : DecidableRel U.Adj := dU
    letI : DecidableRel W.Adj := dW
    have hUW' : edges U ⊆ edges W := by
      intro e he
      have heU : e ∈ U.edgeFinset := by
        simpa only [edges, SimpleGraph.mem_edgeFinset] using he
      have heW := hUW heU
      simpa only [edges, SimpleGraph.mem_edgeFinset] using heW
    have hWP : P W := ⟨hW, hUP.2.trans hUW'⟩
    have hWs : W ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ W, hWP⟩
    have hcard : edgeCount W ≤ edgeCount U := hmax W hWs
    have hEq : edges U = edges W := Finset.eq_of_subset_of_card_le hUW' hcard
    intro e he
    have heW : e ∈ edges W := by
      simpa only [edges, SimpleGraph.mem_edgeFinset] using he
    have heU : e ∈ edges U := (Finset.ext_iff.mp hEq.symm e).mp heW
    simpa only [edges, SimpleGraph.mem_edgeFinset] using heU