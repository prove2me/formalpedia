-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_induce__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:07.841237+00:00
-- url     : https://prove2.me/submissions/285cc595-2d1c-4cb6-b107-3b94293da547

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (s : Finset V) :
    HasPlanarDrawingOn (L.induce (↑s : Set V)) := by
  rcases hL with ⟨p, arc, hp_inj, hdraw, hcross⟩
  refine ⟨fun x => p x.1, fun x y => arc x.1 y.1, ?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact hp_inj hxy
  · intro u v huv hadj
    have huvV : (u : V) < (v : V) := huv
    have hadjV : L.Adj (u : V) (v : V) := (SimpleGraph.induce_adj).mp hadj
    rcases hdraw u.1 v.1 huvV hadjV with ⟨hcont, hinj, hstart, hend, havoid⟩
    refine ⟨hcont, hinj, hstart, hend, ?_⟩
    intro t ht w
    exact havoid t ht w.1
  · intro u v x y huv hxy hadju hadjx hne t ht r hr heq
    have huvV : (u : V) < (v : V) := huv
    have hxyV : (x : V) < (y : V) := hxy
    have hadjuV : L.Adj (u : V) (v : V) := (SimpleGraph.induce_adj).mp hadju
    have hadjxV : L.Adj (x : V) (y : V) := (SimpleGraph.induce_adj).mp hadjx
    have hneV : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hne
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · exact Subtype.ext (congrArg Prod.snd h)
    exact hcross u.1 v.1 x.1 y.1 huvV hxyV hadjuV hadjxV hneV t ht r hr heq