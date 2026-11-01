-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_62c66bf3_533d_43c1_bde3_37ac00c5d3e8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:15.949575+00:00
-- url     : https://prove2.me/submissions/b71dc8cb-8b15-41b8-a3e6-93d4c9a6ce68

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hL : P L) :
    ∃ K : SimpleGraph V, L ≤ K ∧ P K ∧
      (∀ H : SimpleGraph V, K ≤ H → P H → H ≤ K) := by
  classical
  let S : Set (SimpleGraph V) := {K | L ≤ K ∧ P K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨L, by simp [S, hL]⟩
  obtain ⟨K, hK, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro H hKH hPH
  exact hKmax ⟨hK.1.trans hKH, hPH⟩ hKH
