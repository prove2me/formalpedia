-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:06.141365+00:00
-- url     : https://prove2.me/submissions/897f74ab-36a4-4781-b025-6efc9e5d63f4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Finite.Lemmas

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      Set.Subset K.edgeSet H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ H' : SimpleGraph V,
        Set.Subset H.edgeSet H'.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn H' →
        H'.edgeSet = H.edgeSet := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | WilliamsonShmoys.HasPlanarDrawingOn G ∧ K.edgeSet ⊆ G.edgeSet}
  have hSfinite : S.Finite := by
    exact Set.finite_univ.subset (Set.subset_univ S)
  have hSnonempty : S.Nonempty := ⟨K, hK, Set.Subset.rfl⟩
  obtain ⟨H, hHS, hmax⟩ :=
    Set.exists_max_image S (fun G : SimpleGraph V => G.edgeSet.encard)
      hSfinite hSnonempty
  rcases hHS with ⟨hH, hKH⟩
  refine ⟨H, hKH, hH, ?_⟩
  intro H' hHH' hH'
  have hH'S : H' ∈ S := ⟨hH', hKH.trans hHH'⟩
  have hcard : H'.edgeSet.encard ≤ H.edgeSet.encard := hmax H' hH'S
  have hsets : H.edgeSet = H'.edgeSet :=
    (Set.toFinite H.edgeSet).eq_of_subset_of_encard_le hHH' hcard
  exact hsets.symm