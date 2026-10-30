-- Prove2me | solution 1 for WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:45:33.154746+00:00
-- url     : https://prove2.me/submissions/4ccbacef-ed7a-4886-ba3e-1e09fd2fb6e3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ HasPlanarDrawingOn L ∧
        ∀ H : SimpleGraph V, L ≤ H → HasPlanarDrawingOn H → H = L := by
  classical
  let S : Set (SimpleGraph V) := {L | G ≤ L ∧ HasPlanarDrawingOn L}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨L, hLmax⟩ := hSfinite.exists_maximal hSnonempty
  rcases hLmax with ⟨hLmem, hLmax⟩
  change G ≤ L ∧ HasPlanarDrawingOn L at hLmem
  refine ⟨L, hLmem.1, hLmem.2, ?_⟩
  intro H hLH hH
  have hHmem : H ∈ S := ⟨hLmem.1.trans hLH, hH⟩
  exact le_antisymm (hLmax hHmem hLH) hLH