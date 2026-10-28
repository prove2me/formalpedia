-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:56:38.976773+00:00
-- url     : https://prove2.me/submissions/8e9bd095-037f-4032-a169-17d4c79ffc6c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      HasPlanarDrawingOn H ∧
      H.Connected ∧
      (∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (∀ u v, H.Adj u v → K.Adj u v) →
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => G ≤ X0 ∧ HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : G ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have hc : ∀ X : SimpleGraph V, X.edgeSet.ncard = X.edgeFinset.card := fun X => by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  refine ⟨Q, fun u v h => hPQ h, hQ, hconn.mono hPQ, ?_⟩
  intro W hW hQW
  rw [hc, hc]
  exact hmax W (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans (fun u v h => hQW u v h), hW⟩)
