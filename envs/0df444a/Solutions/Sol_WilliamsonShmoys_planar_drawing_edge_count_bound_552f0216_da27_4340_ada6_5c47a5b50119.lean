-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_bound_552f0216_da27_4340_ada6_5c47a5b50119
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:44:58.197202+00:00
-- url     : https://prove2.me/submissions/39fb9163-0e2f-4c6f-b319-7f5408fe44c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_bound_of_connected
import Theorems.Thm_WilliamsonShmoys_edge_count_bound_of_connected_induced_subgraph_bounds

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hlocal :
      ∀ (S : Set V), (H.induce S).Connected → 3 ≤ Nat.card S →
        (H.induce S).edgeSet.ncard + 6 ≤ 3 * Nat.card S := by
    intro S hconn hsize
    classical
    letI : Fintype S := Fintype.ofFinite S
    have hsize' : 3 ≤ Fintype.card S := by
      simpa [Nat.card_eq_fintype_card] using hsize
    have hDraw : WilliamsonShmoys.HasPlanarDrawingOn (H.induce S) := by
      rcases hH with ⟨p, arc, hp, hArc, hMeet⟩
      refine ⟨(fun x : S => p x.1), (fun x y t => arc x.1 y.1 t), ?_, ?_, ?_⟩
      · intro x y hxy
        exact Subtype.ext (hp hxy)
      · intro x y hxy hAdj
        have hv := hArc x.1 y.1 hxy (by simpa using hAdj)
        rcases hv with ⟨hc, hi, h0, h1, havoid⟩
        refine ⟨hc, hi, h0, h1, ?_⟩
        intro t ht a ha
        exact havoid t ht a.1 ha
      · intro x y z w hxy hzw hAdj₁ hAdj₂ hne t ht s hs heq
        have hv := hMeet x.1 y.1 z.1 w.1 hxy hzw
          (by simpa using hAdj₁) (by simpa using hAdj₂)
          (by
            intro he
            apply hne
            exact Prod.ext
              (Subtype.ext (congrArg Prod.fst he))
              (Subtype.ext (congrArg Prod.snd he)))
          t ht s hs heq
        simpa using hv
    have hb :=
      WilliamsonShmoys.planar_drawing_edge_count_bound_of_connected
        (H := H.induce S) hDraw hconn hsize'
    simpa [Nat.card_eq_fintype_card] using hb
  have hcard' : 3 ≤ Nat.card V := by
    simpa [Nat.card_eq_fintype_card] using hcard
  exact
    WilliamsonShmoys.edge_count_bound_of_connected_induced_subgraph_bounds
      (H := H) hlocal hcard'