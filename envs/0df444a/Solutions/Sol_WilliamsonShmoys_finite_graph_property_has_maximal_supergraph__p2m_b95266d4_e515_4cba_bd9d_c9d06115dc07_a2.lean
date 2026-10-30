-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_property_has_maximal_supergraph__p2m_b95266d4_e515_4cba_bd9d_c9d06115dc07_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:48.431403+00:00
-- url     : https://prove2.me/submissions/9ceeee25-7b59-4048-baeb-a6108406efa3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ ∀ J : SimpleGraph V, H ≤ J → P J → J = H := by
  classical
  let S : Set (SimpleGraph V) := {H | K ≤ H ∧ P H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  have hHmem : K ≤ H ∧ P H := hHmax.1
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro J hHJ hPJ
  have hJmem : J ∈ S := ⟨hHmem.1.trans hHJ, hPJ⟩
  exact le_antisymm (hHmax.2 hJmem hHJ) hHJ