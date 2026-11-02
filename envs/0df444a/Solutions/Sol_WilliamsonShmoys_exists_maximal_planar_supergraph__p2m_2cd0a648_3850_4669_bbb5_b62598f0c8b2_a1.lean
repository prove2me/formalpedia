-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:05:23.826812+00:00
-- url     : https://prove2.me/submissions/2a1586f5-fe38-4194-a03d-7280f728c7e4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn J) :
    ∃ H : SimpleGraph V,
      J ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      J.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H => J ≤ H ∧ HasPlanarDrawingOn H)
  have hJ : J ∈ candidates := by
    simp [candidates, hplanar]
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image candidates (fun H => H.edgeSet.ncard) ⟨J, hJ⟩
  have hHprops := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hHprops.1, hHprops.2, ?_, ?_⟩
  · intro K hHK hKplanar
    by_contra hneq
    have hK : K ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_trans hHprops.1 hHK, hKplanar⟩
    have hstrict : H.edgeSet ⊂ K.edgeSet :=
      (SimpleGraph.edgeSet_ssubset_edgeSet).2
        (lt_of_le_of_ne hHK (Ne.symm hneq))
    have hKfinite : K.edgeSet.Finite := Set.toFinite _
    have hless : H.edgeSet.ncard < K.edgeSet.ncard :=
      Set.ncard_lt_ncard hstrict hKfinite
    exact (not_lt_of_ge (hmax K hK)) hless
  · exact hmax J hJ
