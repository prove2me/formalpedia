-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_exists_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:31:30.878787+00:00
-- url     : https://prove2.me/submissions/0dd63194-8b3d-40a0-817f-ce8c2d2d3cd3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximizer_on_fintype

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      (∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet) := by
  classical
  let P : SimpleGraph V → Prop :=
    fun K => H.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximizer_on_fintype P
      (fun K : SimpleGraph V => K.edgeSet.ncard)
      ⟨H, subset_rfl, hH⟩
  refine ⟨K, hK.1, hK.2, ?_, ?_⟩
  · exact hmax H ⟨subset_rfl, hH⟩
  · intro L hKL hL
    have hcard : L.edgeSet.ncard ≤ K.edgeSet.ncard :=
      hmax L ⟨hK.1.trans hKL, hL⟩
    have hEq : K.edgeSet = L.edgeSet :=
      Set.eq_of_subset_of_ncard_le hKL hcard
    exact hEq ▸ Set.Subset.rfl