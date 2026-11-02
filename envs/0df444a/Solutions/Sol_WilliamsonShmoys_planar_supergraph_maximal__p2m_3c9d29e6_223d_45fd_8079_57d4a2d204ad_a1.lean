-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:30:09.64982+00:00
-- url     : https://prove2.me/submissions/d5644365-2895-46a4-a65e-ddcfe5cfe92a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => L ≤ G ∧ HasPlanarDrawingOn G)
  have hLmem : L ∈ candidates := by
    simp [candidates, hL]
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeSet.ncard) ⟨L, hLmem⟩
  have hMprops : L ≤ M ∧ HasPlanarDrawingOn M := by
    simpa [candidates] using (Finset.mem_filter.mp hMmem).2
  refine ⟨M, hMprops.1, hMprops.2, ?_⟩
  intro N hMN hNplanar
  have hLN : L ≤ N := le_trans hMprops.1 hMN
  have hNmem : N ∈ candidates := by
    simp [candidates, hLN, hNplanar]
  have hmax : N.edgeSet.ncard ≤ M.edgeSet.ncard := hMmax N hNmem
  have hmono : M.edgeSet.ncard ≤ N.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hMN)
  have hcardEq : M.edgeSet.ncard = N.edgeSet.ncard := le_antisymm hmono hmax
  have hNM : N ≤ M := by
    apply SimpleGraph.edgeSet_subset_edgeSet.mp
    intro e heN
    by_contra heM
    have hstrict : M.edgeSet ⊂ N.edgeSet := by
      refine ⟨SimpleGraph.edgeSet_mono hMN, ?_⟩
      intro hsub
      exact heM (hsub heN)
    have hlt : M.edgeSet.ncard < N.edgeSet.ncard := Set.ncard_lt_ncard hstrict
    omega
  exact le_antisymm hNM hMN