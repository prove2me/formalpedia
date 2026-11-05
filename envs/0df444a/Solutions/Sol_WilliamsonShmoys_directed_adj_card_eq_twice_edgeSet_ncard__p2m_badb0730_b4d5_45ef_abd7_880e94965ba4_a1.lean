-- Prove2me | solution 1 for WilliamsonShmoys.directed_adj_card_eq_twice_edgeSet_ncard__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:45:11.218+00:00
-- url     : https://prove2.me/submissions/1bba5c3b-0883-4209-8156-bc36a3c32c9d

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    Fintype.card {e : V × V // H.Adj e.1 e.2} = 2 * H.edgeSet.ncard := by
  classical
  let e : H.Dart ≃ {p : V × V // H.Adj p.1 p.2} :=
    { toFun := fun d => ⟨(d.fst, d.snd), d.adj⟩
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by
        rintro ⟨⟨a, b⟩, hadj⟩
        rfl
      right_inv := by
        rintro ⟨⟨a, b⟩, hadj⟩
        rfl }
  have hcard : H.edgeSet.ncard = H.edgeFinset.card := by
    simpa [SimpleGraph.coe_edgeFinset] using (Set.ncard_coe_finset H.edgeFinset)
  calc
    Fintype.card {p : V × V // H.Adj p.1 p.2} = Fintype.card H.Dart :=
      (Fintype.card_congr e).symm
    _ = 2 * H.edgeFinset.card := H.dart_card_eq_twice_card_edges
    _ = 2 * H.edgeSet.ncard := by rw [hcard]
