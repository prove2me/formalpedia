-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:08:23.112575+00:00
-- url     : https://prove2.me/submissions/93bf5e81-2f36-4697-8037-e7d5d7f36326

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdrawing : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ HasPlanarDrawingOn H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨G, le_rfl, hdrawing⟩
  obtain ⟨H, hH, hmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨H, hH.1, hH.2, fun K hHK hKdraw => ?_⟩
  have hK : K ∈ S := ⟨hH.1.trans hHK, hKdraw⟩
  exact le_antisymm (hmax hK hHK) hHK