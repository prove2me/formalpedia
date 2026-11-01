-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:05:14.23321+00:00
-- url     : https://prove2.me/submissions/5ea22b2e-c621-47c6-9800-8eebafda7c94

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (T : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hT : P T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ P U ∧
        ∀ W : SimpleGraph V, U ≤ W → P W → W = U := by
  classical
  let s : Set (SimpleGraph V) := {U | P U}
  have hs : s.Finite := Set.toFinite s
  have hTmem : T ∈ s := hT
  obtain ⟨U, hTU, hUmax⟩ := hs.exists_le_maximal hTmem
  refine ⟨U, hTU, hUmax.1, ?_⟩
  intro W hUW hPW
  exact le_antisymm (hUmax.2 hPW hUW) hUW