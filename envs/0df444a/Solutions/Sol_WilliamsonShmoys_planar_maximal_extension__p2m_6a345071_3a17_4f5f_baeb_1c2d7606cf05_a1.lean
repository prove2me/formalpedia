-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_6a345071_3a17_4f5f_baeb_1c2d7606cf05_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:36.743578+00:00
-- url     : https://prove2.me/submissions/3ea08fad-4f98-4fb8-a99a-44bbb6cd9fd2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite :=
    Set.finite_univ.subset (by
      intro G hG
      exact Set.mem_univ G)
  have hKmem : K ∈ S := ⟨le_rfl, hK⟩
  obtain ⟨H, hKH, hmax⟩ := hSfinite.exists_le_maximal hKmem
  refine ⟨H, hKH, hmax.1.2, ?_⟩
  intro J hHJ hJ
  have hJmem : J ∈ S := ⟨hKH.trans hHJ, hJ⟩
  exact hmax.2 hJmem hHJ