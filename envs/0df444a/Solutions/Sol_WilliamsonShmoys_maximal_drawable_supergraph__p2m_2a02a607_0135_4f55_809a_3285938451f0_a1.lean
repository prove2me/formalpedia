-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:15:58.339971+00:00
-- url     : https://prove2.me/submissions/8df09c19-24ec-42a3-b333-40b761264036

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_of_fintype__p2m_04119e1c_38ee_4062_845e_a21642e582fb_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  let S : SimpleGraph V → Prop := fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : ∃ G, S G := ⟨K, le_rfl, hK⟩
  haveI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  obtain ⟨L, hL, hmax⟩ :=
    exists_maximal_of_fintype__p2m_04119e1c_38ee_4062_845e_a21642e582fb_a1 S hS
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  have hSM : S M := ⟨le_trans hL.1 hLM, hM⟩
  have hback : M ≤ L := hmax M hSM hLM
  exact le_antisymm hback hLM