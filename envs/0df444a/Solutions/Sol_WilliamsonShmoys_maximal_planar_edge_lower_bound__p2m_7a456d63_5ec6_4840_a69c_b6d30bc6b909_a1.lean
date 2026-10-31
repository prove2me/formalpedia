-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:28:14.205848+00:00
-- url     : https://prove2.me/submissions/bc444930-2f77-497b-9cee-0cdf71cd24a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_exact_edge_count__p2m_f6ef00c3_9a62_41aa_bbc8_b32342398c0c_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hLmax : forall M : SimpleGraph V, LE.le L M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  obtain ⟨M, hLM, hMplanar, hMcount⟩ :=
    WilliamsonShmoys.maximal_planar_completion_exact_edge_count__p2m_f6ef00c3_9a62_41aa_bbc8_b32342398c0c_a2
      L hLplanar hV
  have hML : M = L := hLmax M hLM hMplanar
  have hLcount : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hML] using hMcount
  rw [hLcount]