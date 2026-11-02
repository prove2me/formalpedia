-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:07:58.332194+00:00
-- url     : https://prove2.me/submissions/8eb16d6b-ca4a-441b-acd3-d9944cf1b8ec

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) := {K | G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨K, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨K, hKmax.1.1, hKmax.1.2, ?_⟩
  intro L hKL hL
  have hLS : L ∈ S := ⟨hKmax.1.1.trans hKL, hL⟩
  have hLK : K = L := hKmax.eq_of_le hLS hKL
  rw [← hLK]