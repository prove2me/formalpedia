-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_of_finite_strict_augmentation__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:31:02.136991+00:00
-- url     : https://prove2.me/submissions/9912351d-bb9f-4cac-b135-996c8528ace5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hStep : ∀ G : SimpleGraph V, L ≤ G → HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet ⊂ H.edgeSet) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  classical
  let feasible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L ≤ G ∧ HasPlanarDrawingOn G
  have hFeasible : feasible.Nonempty := by
    refine ⟨L, ?_⟩
    simp [feasible, hL]
  obtain ⟨G, hGmem, hGmax⟩ :=
    Finset.exists_max_image feasible (fun G : SimpleGraph V => G.edgeFinset.card) hFeasible
  have hGprops : L ≤ G ∧ HasPlanarDrawingOn G := by
    simpa [feasible] using hGmem
  rcases hGprops with ⟨hLG, hGdraw⟩
  refine ⟨G, hLG, ?_, hGdraw⟩
  by_contra hGdisconnected
  obtain ⟨H, hGH, hHdraw, hStrict⟩ := hStep G hLG hGdraw hGdisconnected
  have hLH : L ≤ H := le_trans hLG hGH
  have hHmem : H ∈ feasible := by
    simp [feasible, hLH, hHdraw]
  have hCardLt : G.edgeFinset.card < H.edgeFinset.card := by
    apply Finset.card_lt_card
    simpa [SimpleGraph.edgeFinset] using hStrict
  exact (Nat.not_lt_of_ge (hGmax H hHmem)) hCardLt