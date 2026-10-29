-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_has_triangulation_edge_count__p2m_80d3c120_40ab_4263_83fa_69737aacfbab_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:53:58.420336+00:00
-- url     : https://prove2.me/submissions/ff07d9bf-7498-4c47-a9ff-262671f49a4b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_7369a359__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a2__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a3

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => K <= G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
  have hSnonempty : S.Nonempty := by
    refine ⟨K, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _, le_rfl, hK⟩
  obtain ⟨L, hLS, hmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hSnonempty
  have hLprops : K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L :=
    (Finset.mem_filter.mp hLS).2
  have hMax : forall N : SimpleGraph V, L <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N <= L := by
    intro N hLN hN
    have hNS : N ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hLprops.1.trans hLN, hN⟩
    have hcard : N.edgeFinset.card <= L.edgeFinset.card := hmax N hNS
    have hsub : L.edgeFinset ⊆ N.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hLN
    have heq : L.edgeFinset = N.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hcard
    have hNL : N = L := (SimpleGraph.edgeFinset_inj.mp heq).symm
    simpa [hNL] using (le_rfl : L <= L)
  exact ⟨L, hLprops.1, hLprops.2,
    WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a2__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a3
      L hLprops.2 hV hMax⟩
