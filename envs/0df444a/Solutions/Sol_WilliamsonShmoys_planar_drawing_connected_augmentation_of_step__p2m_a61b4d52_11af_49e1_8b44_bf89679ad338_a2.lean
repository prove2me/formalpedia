-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_of_step__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:34:27.369219+00:00
-- url     : https://prove2.me/submissions/115a914c-4bb8-4893-9705-c11c3436c9fb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hstep : ∀ G : SimpleGraph V, L ≤ G → HasPlanarDrawingOn G →
      ¬ G.Connected → ∃ H : SimpleGraph V, G < H ∧ HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  classical
  let S : Set (SimpleGraph V) := {G | L ≤ G ∧ HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨L, le_rfl, hL⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  have hHL : L ≤ H := hHmax.1.1
  have hHplanar : HasPlanarDrawingOn H := hHmax.1.2
  have hHconnected : H.Connected := by
    by_contra hHdisconnected
    obtain ⟨K, hHK, hKplanar⟩ := hstep H hHL hHplanar hHdisconnected
    have hKmem : K ∈ S := ⟨hHL.trans hHK.1, hKplanar⟩
    have hKH : K ≤ H := hHmax.2 hKmem hHK.1
    exact hHK.2 hKH
  exact ⟨H, hHL, hHconnected, hHplanar⟩