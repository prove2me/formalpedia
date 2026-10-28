-- Prove2me | solution 1 for WilliamsonShmoys.drawable_completion_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:45:31.346034+00:00
-- url     : https://prove2.me/submissions/b4c76ec1-d7f5-4470-ac3a-17fb1f399b24

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists P : SimpleGraph V,
      (forall {u v}, N.Adj u v -> P.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn P /\
      (forall Q : SimpleGraph V,
        (forall {u v}, P.Adj u v -> Q.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn Q -> Q = P) := by
  have hH := hdraw
  set H := N
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
