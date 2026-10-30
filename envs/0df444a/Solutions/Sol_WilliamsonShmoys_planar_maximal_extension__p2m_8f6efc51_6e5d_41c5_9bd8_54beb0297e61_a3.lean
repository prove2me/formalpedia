-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:41:58.89624+00:00
-- url     : https://prove2.me/submissions/64f67782-17db-4d06-b305-a2ef9c0c6160

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H => G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  have hS : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hG]
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image S (fun K => Fintype.card K.edgeSet) hS
  have hGH : G ≤ H := (Finset.mem_filter.mp hHmem).2.1
  have hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H :=
    (Finset.mem_filter.mp hHmem).2.2
  refine ⟨H, hGH, hHplanar, ?_⟩
  intro K hHK hKplanar
  have hGK : G ≤ K := hGH.trans hHK
  have hKmem : K ∈ S := by
    simp [S, hGK, hKplanar]
  have hmax := hHmax K hKmem
  by_contra hne
  have hlt : H < K := lt_of_le_of_ne hHK (Ne.symm hne)
  have hssub : H.edgeFinset ⊂ K.edgeFinset :=
    SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have hcard : Fintype.card H.edgeSet < Fintype.card K.edgeSet := by
    simpa only [SimpleGraph.edgeFinset_card] using Finset.card_lt_card hssub
  exact (not_le_of_gt hcard) hmax