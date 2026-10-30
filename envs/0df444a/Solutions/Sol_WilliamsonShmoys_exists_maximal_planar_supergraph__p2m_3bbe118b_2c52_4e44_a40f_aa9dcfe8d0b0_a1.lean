-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:51:39.124113+00:00
-- url     : https://prove2.me/submissions/aee7e2d6-9ddf-41a8-85d6-447b34b54d76

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_nonempty_set_has_maximal__p2m_728754b2_3360_4212_89f5_97b877a982a4_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  let S : Set (SimpleGraph V) := {G | L ≤ G ∧ HasPlanarDrawingOn G}
  have hS : S.Nonempty := ⟨L, le_rfl, hDraw⟩
  obtain ⟨M, hM, hMax⟩ :=
    finite_nonempty_set_has_maximal__p2m_728754b2_3360_4212_89f5_97b877a982a4_a1 S hS
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hN
  have hNmem : N ∈ S := ⟨hM.1.trans hMN, hN⟩
  have hNM := hMax N hNmem hMN
  exact le_antisymm hNM hMN