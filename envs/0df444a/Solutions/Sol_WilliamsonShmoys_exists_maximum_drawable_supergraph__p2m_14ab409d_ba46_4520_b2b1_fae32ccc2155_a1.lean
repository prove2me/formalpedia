-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximum_drawable_supergraph__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:30:00.360187+00:00
-- url     : https://prove2.me/submissions/ad73d80d-37ba-4eca-9cb0-2655168fe01a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
          K.edgeSet.ncard ≤ N.edgeSet.ncard := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun N => M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N)
  have hCandidates : candidates.Nonempty := by
    refine ⟨M, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _, le_rfl, hM⟩
  let edgeCounts : Finset ℕ := candidates.image (fun G => G.edgeSet.ncard)
  have hEdgeCounts : edgeCounts.Nonempty := by
    refine ⟨M.edgeSet.ncard, Finset.mem_image.mpr ?_⟩
    exact ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hM⟩, rfl⟩
  obtain ⟨N, hNmem, hNcount⟩ :=
    Finset.mem_image.mp (edgeCounts.max'_mem hEdgeCounts)
  have hNprops := (Finset.mem_filter.mp hNmem).2
  refine ⟨N, hNprops.1, hNprops.2, ?_⟩
  intro K hMK hK
  have hKmem : K ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMK, hK⟩
  have hKcount : K.edgeSet.ncard ∈ edgeCounts :=
    Finset.mem_image.mpr ⟨K, hKmem, rfl⟩
  calc
    K.edgeSet.ncard ≤ edgeCounts.max' hEdgeCounts :=
      Finset.le_max' _ _ hKcount
    _ = N.edgeSet.ncard := hNcount.symm