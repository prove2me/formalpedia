-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:42:27.255978+00:00
-- url     : https://prove2.me/submissions/a04cf085-823c-4f02-a742-66df7725a39b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
  have hMmem : M ∈ admissible := by
    simp [admissible, hM]
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image admissible (fun G => G.edgeFinset.card) ⟨M, hMmem⟩
  have hH : M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
    simpa [admissible] using hHmem
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ admissible := by
    simp [admissible, hH.1.trans hHK, hK]
  by_contra hneq
  have hlt : H < K := lt_of_le_of_ne hHK (Ne.symm hneq)
  have hedge : H.edgeFinset ⊂ K.edgeFinset := by
    simpa only [SimpleGraph.edgeFinset_ssubset_edgeFinset] using hlt
  have hcard : H.edgeFinset.card < K.edgeFinset.card := Finset.card_lt_card hedge
  have hmax := hHmax K hKmem
  omega