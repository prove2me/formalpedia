-- Prove2me | solution 1 for WilliamsonShmoys.three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T22:35:29.686808+00:00
-- url     : https://prove2.me/submissions/e6cecfa7-4abc-494a-a9d2-fb91eb51af40

import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : Fintype.card V = 3)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v)
    [DecidableRel H.Adj]
    (v : V) :
    Fintype.card {d : H.Dart // d.fst = v} = 2 := by
  have h_universal : H.IsUniversal v := by
    intro w hw
    exact hcomplete v w hw
  
  have hdegree : H.degree v = 2 := by
    have h₁ : H.degree v = Fintype.card V - 1 :=
      (H.degree_eq_card_sub_one v).mpr h_universal
    simpa [hV] using h₁

  classical
  rw [Fintype.card_subtype, H.dart_fst_fiber_card_eq_degree, hdegree]

