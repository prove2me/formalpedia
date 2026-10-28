-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_of_augmentable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:19:30.901997+00:00
-- url     : https://prove2.me/submissions/8d321d35-f4f0-467c-a7f8-1c75ce492898

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem S195_gen
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (N : SimpleGraph V) (hP : P N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun K => N ≤ K ∧ P K)
  have hS : S.Nonempty := ⟨N, by simp [S, hP]⟩
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image S (fun K => K.edgeSet.ncard) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hH hmax
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have h1 := hmax K ⟨hH.1.trans hHK, hK⟩
  have heq : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hHK) h1 (Set.toFinite _)
  exact (SimpleGraph.edgeSet_injective heq).symm


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hAugment :
      ∀ X : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn X →
        ¬ X.Connected →
        ∃ Z : SimpleGraph V,
          X ≤ Z ∧
          X.edgeSet.ncard < Z.edgeSet.ncard ∧
          WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      Y.edgeSet.ncard ≤ Z.edgeSet.ncard ∧
      Z.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen (fun K => WilliamsonShmoys.HasPlanarDrawingOn K) Y hY
  refine ⟨H, h1, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h1) (Set.toFinite _), ?_, h2⟩
  by_contra hc
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := hAugment H h2 hc
  have := h3 Z hZ1 hZ3
  subst this
  exact lt_irrefl _ hZ2
