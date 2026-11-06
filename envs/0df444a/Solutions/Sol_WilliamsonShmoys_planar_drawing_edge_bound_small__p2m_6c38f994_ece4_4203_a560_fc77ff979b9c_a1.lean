-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_small__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:54:04.283923+00:00
-- url     : https://prove2.me/submissions/01ae12ba-56d4-473c-a317-5c88dba5dae1

-- ID: aa93fc0d-3b8b-4ccf-af3c-fc1fe2554efb | NAME: WilliamsonShmoys.planar_drawing_edge_bound_small__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Fintype.card V ≤ 2 →
      M.edgeSet.ncard ≤ Fintype.card V - 1 := by
  classical
  intro hsmall
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hcard : M.edgeSet.ncard = M.edgeFinset.card := by
    simpa [SimpleGraph.coe_edgeFinset] using (Set.ncard_coe_finset M.edgeFinset)
  rw [hcard]
  have hle : M.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two (G := M)
  have hchoose : (Fintype.card V).choose 2 ≤ Fintype.card V - 1 := by
    by_cases h0 : Fintype.card V = 0
    · rw [h0]; norm_num
    by_cases h1 : Fintype.card V = 1
    · rw [h1]; norm_num
    have h2 : Fintype.card V = 2 := by omega
    rw [h2]; norm_num
  omega
