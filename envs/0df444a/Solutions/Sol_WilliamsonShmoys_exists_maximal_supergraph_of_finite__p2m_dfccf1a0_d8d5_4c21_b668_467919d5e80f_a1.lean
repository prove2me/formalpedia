-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_dfccf1a0_d8d5_4c21_b668_467919d5e80f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:22:33.089462+00:00
-- url     : https://prove2.me/submissions/3926790f-8eb0-4b2d-8e58-7d52130b3b79

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      ∀ J : SimpleGraph V, H ≤ J → P J → H = J := by
  classical
  let S : Set (SimpleGraph V) := {H | K ≤ H ∧ P H}
  have hSfin : S.Finite := by
    exact Set.finite_univ.subset (by
      intro H hH
      simp)
  obtain ⟨H, hHmax⟩ := hSfin.exists_maximal (⟨K, le_rfl, hK⟩ : S.Nonempty)
  refine ⟨H, hHmax.1.1, hHmax.1.2, ?_⟩
  intro J hHJ hPJ
  have hJS : J ∈ S := ⟨hHmax.1.1.trans hHJ, hPJ⟩
  have hJH : J ≤ H := hHmax.2 hJS hHJ
  exact le_antisymm hHJ hJH