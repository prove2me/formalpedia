-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_connected__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:13:43.647503+00:00
-- url     : https://prove2.me/submissions/86374124-f8de-47f9-8563-e8ab0074457d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution :
    Not (forall {V : Type} [Fintype V] [LinearOrder V]
      (L : SimpleGraph V), HasPlanarDrawingOn L ->
      (forall M : SimpleGraph V, LE.le L M -> HasPlanarDrawingOn M -> M = L) ->
      L.Connected) := by
  intro h
  let L : SimpleGraph Empty := (⊥ : SimpleGraph Empty)
  have hdraw : HasPlanarDrawingOn L := by
    refine ⟨ (fun u => u.elim), (fun u => u.elim), ?_, ?_, ?_ ⟩
    · intro a b hab
      exact a.elim
    · intro u v huv hadj
      exact u.elim
    · intro u v x y huv hxy hadj1 hadj2 hne
      exact u.elim
  have hmax :
      forall M : SimpleGraph Empty, LE.le L M -> HasPlanarDrawingOn M -> M = L := by
    intro M hLM hM
    ext u v
    exact u.elim
  have hc : L.Connected := h (V := Empty) L hdraw hmax
  have hc' : (⊥ : SimpleGraph Empty).Connected := by
    simpa [L] using hc
  have hne : Nonempty Empty := (SimpleGraph.connected_bot_iff.mp hc').2
  rcases hne with ⟨ e ⟩
  exact e.elim