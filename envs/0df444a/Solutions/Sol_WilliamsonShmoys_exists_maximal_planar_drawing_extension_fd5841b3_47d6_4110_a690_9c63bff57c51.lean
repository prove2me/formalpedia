-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:36:01.951353+00:00
-- url     : https://prove2.me/submissions/90526f56-eca6-4602-9a5b-19f33f64a91c

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
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      ∀ M : SimpleGraph V,
        Q ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M ≤ Q := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen (fun K => WilliamsonShmoys.HasPlanarDrawingOn K) P hP
  exact ⟨H, h1, h2, fun M hM hd => (h3 M hM hd).le⟩
