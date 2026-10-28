-- Prove2me | solution 1 for WilliamsonShmoys.same_vertex_maximal_planar_augmentation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:27:38.167396+00:00
-- url     : https://prove2.me/submissions/3f54f73b-df83-438b-91e6-743d486431be

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_member_of_finite_set

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hS : S.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_member_of_finite_set S hS
  change H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K at hK
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  have hLS : L ∈ S := ⟨le_trans hK.1 hKL, hL⟩
  have hLK := hmax L hLS hKL
  exact le_antisymm hLK hKL