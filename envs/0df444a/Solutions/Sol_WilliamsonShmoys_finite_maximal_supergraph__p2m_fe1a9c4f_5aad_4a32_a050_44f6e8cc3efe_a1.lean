-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:26:56.444224+00:00
-- url     : https://prove2.me/submissions/bea58e23-995d-4bfa-a94a-d41e9065f62f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] (K : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hPK : P K)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      ∀ J : SimpleGraph V, H ≤ J → P J → J ≤ H := by
  classical
  let S : Set (SimpleGraph V) := {H | K ≤ H ∧ P H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, by simp [S, hPK]⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  have hHmem : H ∈ S := hHmax.1
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro J hHJ hPJ
  have hJmem : J ∈ S := ⟨hHmem.1.trans hHJ, hPJ⟩
  exact hHmax.2 hJmem hHJ