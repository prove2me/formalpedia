-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:32:15.98476+00:00
-- url     : https://prove2.me/submissions/c111f617-22bf-49c4-be8d-f0703762e7f7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V => H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G =>
    H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨H, ?_⟩
    simp [S, hH]
  obtain ⟨K, hK⟩ := S.exists_maximal hS
  have hKmem : K ∈ S := hK.1
  have hKprops : H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
    (Finset.mem_filter.mp hKmem).2
  refine ⟨K, hKprops.1, hKprops.2, ?_⟩
  intro L hKL hL
  have hLmem : L ∈ S := by
    simp [S, hKprops.1.trans hKL, hL]
  exact le_antisymm (hK.2 hLmem hKL) hKL