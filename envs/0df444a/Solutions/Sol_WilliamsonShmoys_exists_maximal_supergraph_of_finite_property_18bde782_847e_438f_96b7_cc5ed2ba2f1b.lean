-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_property_18bde782_847e_438f_96b7_cc5ed2ba2f1b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:36:54.015794+00:00
-- url     : https://prove2.me/submissions/edb3fb7a-cc8d-4d6b-ad22-694d8fdf03ed

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hL : P L) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ P T ∧
        ∀ U : SimpleGraph V, T ≤ U → P U → U ≤ T := by
  classical
  let S : Set (SimpleGraph V) := {T | L ≤ T ∧ P T}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨L, le_rfl, hL⟩
  obtain ⟨T, hT, hTmax⟩ := hSfin.exists_maximal hSne
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro U hTU hPU
  exact hTmax ⟨hT.1.trans hTU, hPU⟩ hTU