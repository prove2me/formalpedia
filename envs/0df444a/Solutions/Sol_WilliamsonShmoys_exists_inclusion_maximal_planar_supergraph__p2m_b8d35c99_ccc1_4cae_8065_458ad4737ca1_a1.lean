-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:11:25.775881+00:00
-- url     : https://prove2.me/submissions/bb639193-6e14-4fc6-a17a-10e3df65d93f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    Exists fun M : SimpleGraph V => G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  let S : Set (SimpleGraph V) := {M | G ≤ M ∧ HasPlanarDrawingOn M}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨M, hM⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨M, hM.1.1, hM.1.2, ?_⟩
  intro N hMN hN
  have hNS : N ∈ S := ⟨hM.1.1.trans hMN, hN⟩
  have hNM : N ≤ M := hM.2 hNS hMN
  exact le_antisymm hNM hMN