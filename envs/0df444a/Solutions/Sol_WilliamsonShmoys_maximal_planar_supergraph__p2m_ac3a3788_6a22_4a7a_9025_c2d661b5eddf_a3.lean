-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:15:12.282228+00:00
-- url     : https://prove2.me/submissions/f51b6d3e-e3dd-4403-a6e5-b01e8d93fdf0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) :
    ∃ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W ∧
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) ∧
      (∀ (X : SimpleGraph V) (dX : DecidableRel X.Adj),
        HasPlanarDrawingOn X →
        (letI : DecidableRel W.Adj := dW
         letI : DecidableRel X.Adj := dX
         W.edgeFinset ⊆ X.edgeFinset) →
        (letI : DecidableRel W.Adj := dW
         letI : DecidableRel X.Adj := dX
         X.edgeFinset ⊆ W.edgeFinset)) := by
  classical
  letI : DecidableRel U.Adj := dU
  have hinj : Function.Injective
      (fun G : SimpleGraph V => fun x y => decide (G.Adj x y)) := by
    intro G H h
    apply SimpleGraph.ext
    funext x y
    apply propext
    have hh : decide (G.Adj x y) = decide (H.Adj x y) :=
      congrArg (fun f : V → V → Bool => f x y) h
    have hiff : decide (G.Adj x y) = true ↔ decide (H.Adj x y) = true := by
      rw [hh]
    simpa only [decide_eq_true_eq] using hiff
  letI : Finite (SimpleGraph V) := Finite.of_injective
    (fun G : SimpleGraph V => fun x y => decide (G.Adj x y)) hinj
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => HasPlanarDrawingOn G ∧ U ≤ G)
  have hS : S.Nonempty := by
    refine ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU, le_rfl⟩⟩
  obtain ⟨W, hWmem, hWmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hS
  have hWparts := Finset.mem_filter.mp hWmem
  have hWplanar : HasPlanarDrawingOn W := hWparts.2.1
  have hUW : U ≤ W := hWparts.2.2
  let dW : DecidableRel W.Adj := Classical.decRel W.Adj
  refine ⟨W, dW, hWplanar, ?_, ?_⟩
  · letI : DecidableRel W.Adj := dW
    simpa only [SimpleGraph.edgeFinset_subset_edgeFinset] using hUW
  · intro X dX hX hWX
    letI : DecidableRel W.Adj := dW
    letI : DecidableRel X.Adj := dX
    have hWXle : W ≤ X :=
      (SimpleGraph.edgeFinset_subset_edgeFinset).mp hWX
    by_contra hXW
    have hnotle : ¬ X ≤ W :=
      fun h => hXW ((SimpleGraph.edgeFinset_subset_edgeFinset).mpr h)
    have hUX : U ≤ X := le_trans hUW hWXle
    have hXmem : X ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX, hUX⟩
    have hlt : W < X := by
      apply lt_of_le_of_ne hWXle
      intro heq
      apply hnotle
      simpa [heq] using (le_rfl : W ≤ W)
    letI : DecidableRel X.Adj := Classical.decRel X.Adj
    have hss : W.edgeFinset ⊂ X.edgeFinset :=
      (SimpleGraph.edgeFinset_ssubset_edgeFinset).mpr hlt
    have hcard : W.edgeFinset.card < X.edgeFinset.card := Finset.card_lt_card hss
    exact (not_lt_of_ge (hWmax X hXmem)) hcard