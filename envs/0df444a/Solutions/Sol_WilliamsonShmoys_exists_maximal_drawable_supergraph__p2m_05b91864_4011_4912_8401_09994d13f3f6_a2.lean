-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_05b91864_4011_4912_8401_09994d13f3f6_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:27:17.446469+00:00
-- url     : https://prove2.me/submissions/029fb481-ad50-45ce-8759-ca706d2357bb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun N => M ≤ N ∧ HasPlanarDrawingOn N
  have hS : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp [S, hM]
  obtain ⟨N, hNmem, hNmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeSet.ncard) hS
  have hMN : M ≤ N := (Finset.mem_filter.mp hNmem).2.1
  have hNdraw : HasPlanarDrawingOn N := (Finset.mem_filter.mp hNmem).2.2
  refine ⟨N, hMN, hNdraw, ?_⟩
  intro P hNP hPdraw
  have hPmem : P ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hMN.trans hNP, hPdraw⟩
  have hcard : P.edgeSet.ncard ≤ N.edgeSet.ncard := hNmax P hPmem
  by_contra hne
  have hproper : N.edgeSet ⊂ P.edgeSet := by
    rw [SimpleGraph.edgeSet_ssubset_edgeSet]
    exact lt_of_le_of_ne hNP (Ne.symm hne)
  exact (not_le_of_gt (Set.ncard_lt_ncard hproper)) hcard