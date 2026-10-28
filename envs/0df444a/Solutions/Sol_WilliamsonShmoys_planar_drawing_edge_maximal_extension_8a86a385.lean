-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_maximal_extension_8a86a385
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:37:03.750818+00:00
-- url     : https://prove2.me/submissions/f52e85c6-13db-48ac-8c28-be037f7b33c6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ HasPlanarDrawingOn H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨G, le_rfl, hGdraw⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  have hHmem : H ∈ S := hHmax.1
  have hGH : G ≤ H := hHmem.1
  have hHdraw : HasPlanarDrawingOn H := hHmem.2
  refine ⟨H, hGH, hConn.mono hGH, hHdraw, ?_⟩
  intro K hHK hKdraw
  have hKmem : K ∈ S := ⟨hGH.trans hHK, hKdraw⟩
  have hKH : K ≤ H := hHmax.2 hKmem hHK
  exact le_antisymm hKH hHK