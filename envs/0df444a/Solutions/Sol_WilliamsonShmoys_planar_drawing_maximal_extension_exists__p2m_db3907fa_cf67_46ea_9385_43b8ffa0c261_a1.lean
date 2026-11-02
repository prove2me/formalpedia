-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:26:21.020896+00:00
-- url     : https://prove2.me/submissions/e0aa41ad-f2b5-4311-b44a-43322e58c1d1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ N : SimpleGraph V,
        H.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet ⊆ H.edgeSet := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun N =>
      M.edgeSet ⊆ N.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn N
  have hcandidates : candidates.Nonempty := by
    refine ⟨M, ?_⟩
    simp [candidates, hM]
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image candidates (fun N => N.edgeSet.ncard) hcandidates
  have hHprops : M.edgeSet ⊆ H.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
    simpa [candidates] using (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hHprops.1, hHprops.2, ?_⟩
  intro N hHN hN
  have hMN : M.edgeSet ⊆ N.edgeSet := hHprops.1.trans hHN
  have hNmem : N ∈ candidates := by
    change N ∈ Finset.univ.filter (fun X : SimpleGraph V =>
      M.edgeSet ⊆ X.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn X)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ N, hMN, hN⟩
  have hcard_le : N.edgeSet.ncard ≤ H.edgeSet.ncard := hHmax N hNmem
  have hEq : H.edgeSet = N.edgeSet := Set.eq_of_subset_of_ncard_le hHN hcard_le
  rw [← hEq]
