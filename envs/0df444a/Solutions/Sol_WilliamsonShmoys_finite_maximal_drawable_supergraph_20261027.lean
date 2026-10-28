-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_drawable_supergraph_20261027
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:06:27.752614+00:00
-- url     : https://prove2.me/submissions/da46e2c0-039f-4d61-b666-506ab1ee8d5c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    Exists fun Q : SimpleGraph V =>
      (forall {u v}, P.Adj u v -> Q.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn Q /\
      (forall R : SimpleGraph V,
        (forall {u v}, Q.Adj u v -> R.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn R -> R = Q) := by
  have hH := hdraw
  set H := P
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => H ≤ G ∧ HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hH⟩⟩
  obtain ⟨hPQ, hQ⟩ : H ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h1 : Q.edgeFinset ⊂ R.edgeFinset := SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
    have h2 := Finset.card_lt_card h1
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Q, fun h => hPQ h, hQ, fun R h1 h2 => key R (fun _ _ h => h1 h) h2⟩
