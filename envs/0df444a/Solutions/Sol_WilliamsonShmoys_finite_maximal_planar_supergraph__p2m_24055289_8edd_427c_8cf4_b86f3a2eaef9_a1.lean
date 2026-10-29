-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:10:15.102847+00:00
-- url     : https://prove2.me/submissions/8a00d4a2-b82f-4583-a9f9-3cd2f2f5ebaa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K ≤ H := by
  have hF : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
  obtain ⟨H, hH⟩ := (Set.toFinite {H : SimpleGraph V | G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}).exists_maximal ⟨G, le_rfl, hG⟩
  exact ⟨H, hH.1.1, hH.1.2, fun K hHK hK => hH.2 ⟨hH.1.1.trans hHK, hK⟩ hHK⟩
