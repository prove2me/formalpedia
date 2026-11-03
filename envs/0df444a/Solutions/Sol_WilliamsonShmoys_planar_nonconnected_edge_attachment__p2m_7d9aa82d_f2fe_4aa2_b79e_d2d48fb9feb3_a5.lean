-- Prove2me | solution 1 for WilliamsonShmoys.planar_nonconnected_edge_attachment__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T08:02:48.001803+00:00
-- url     : https://prove2.me/submissions/f3292ce5-7bb4-4430-868b-b0625ce99afc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_6932dd3a_aa87_467b_ad6b_7c92eed114e6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_SimpleGraph_exists_adj_across_components_of_connected_supergraph__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) (hdis : ¬ G.Connected) :
    ∃ (u v : V) (huv : u ≠ v),
      ¬ G.Reachable u v ∧
      ∃ H : SimpleGraph V,
        G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ a b, H.Adj a b ↔
          G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  classical
  obtain ⟨N, hGN, hNdraw, hNmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_6932dd3a_aa87_467b_ad6b_7c92eed114e6_a1
      G hG
  have hmax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by
    intro K hNK hKdraw
    have heq : K = N := hNmax K hNK hKdraw
    simpa [heq]
  have hNconnected :=
    WilliamsonShmoys.maximal_planar_drawingOn_connected N hNdraw hmax hcard
  obtain ⟨u, v, hUnreachable, hNuv⟩ :=
    SimpleGraph.exists_adj_across_components_of_connected_supergraph__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
      G N hGN hNconnected hdis
  have huv : u ≠ v := by
    intro h
    subst v
    exact hUnreachable (by simp)
  let H : SimpleGraph V := G ⊔ SimpleGraph.edge u v
  have hAdjExact : ∀ a b, H.Adj a b ↔
      G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
    intro a b
    simp only [H, SimpleGraph.sup_adj]
    constructor
    · intro hab
      rcases hab with habG | habEdge
      · exact Or.inl habG
      · simp [SimpleGraph.edge, huv] at habEdge
        rcases habEdge with ⟨habPair, _⟩
        rcases habPair with habUV | habVU
        · exact Or.inr (Or.inl habUV)
        · exact Or.inr (Or.inr habVU)
    · intro hab
      rcases hab with habG | habUV | habVU
      · exact Or.inl habG
      · right
        simp [SimpleGraph.edge, huv, habUV]
      · right
        simp [SimpleGraph.edge, huv, huv.symm, habVU]
  have hGH : G ≤ H := by
    intro a b hab
    exact (hAdjExact a b).2 (Or.inl hab)
  have hHN : H ≤ N := by
    intro a b hab
    rcases (hAdjExact a b).1 hab with habG | habUV | habVU
    · exact hGN habG
    · rcases habUV with ⟨rfl, rfl⟩
      exact hNuv
    · rcases habVU with ⟨rfl, rfl⟩
      exact hNuv.symm
  have hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H := by
    rcases hNdraw with ⟨p, arc, hp, hEdges, hCross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro a b hab hAdj
      exact hEdges a b hab (hHN hAdj)
    · intro a b x y hab hxy hAdj hAdj' hneq t ht s hs hEq
      exact hCross a b x y hab hxy (hHN hAdj) (hHN hAdj') hneq t ht s hs hEq
  exact ⟨u, v, huv, hUnreachable, H, hGH, hHdraw, hAdjExact⟩
