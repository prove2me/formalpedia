-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:36.298571+00:00
-- url     : https://prove2.me/submissions/dfb38dd8-3c74-4a0e-bbdd-f95d545c43c2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ R : SimpleGraph V,
      (∀ u v, T.Adj u v → R.Adj u v) ∧
      (∀ S : SimpleGraph V,
        (∀ u v, T.Adj u v → S.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn S →
        (∀ u v, R.Adj u v → S.Adj u v) → S = R) ∧
      WilliamsonShmoys.HasPlanarDrawingOn R := by
  classical
  have key : ∀ (P : SimpleGraph V → Prop) (T : SimpleGraph V), P T →
      ∃ L, T ≤ L ∧ P L ∧ ∀ M, L ≤ M → P M → M = L := by
    intro P T hT
    have hfin : {L : SimpleGraph V | T ≤ L ∧ P L}.Finite := Set.toFinite _
    obtain ⟨L, hL, hmax⟩ := Set.exists_max_image {L : SimpleGraph V | T ≤ L ∧ P L}
      (fun L => L.edgeSet.ncard) hfin ⟨T, le_rfl, hT⟩
    refine ⟨L, hL.1, hL.2, ?_⟩
    intro M hLM hM
    have hc : M.edgeSet.ncard ≤ L.edgeSet.ncard := hmax M ⟨le_trans hL.1 hLM, hM⟩
    have hsub : L.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hLM
    have hfM : M.edgeSet.Finite := Set.toFinite _
    have := Set.eq_of_subset_of_ncard_le hsub hc hfM
    exact (SimpleGraph.edgeSet_inj.mp this.symm)
  obtain ⟨L, hTL, hL, hm⟩ := key (fun L => WilliamsonShmoys.HasPlanarDrawingOn L) T hT
  refine ⟨L, fun u v h => hTL h, ?_, hL⟩
  intro S _ hS hLS
  exact hm S (fun u v h => hLS u v h) hS
