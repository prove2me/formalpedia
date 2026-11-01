-- Prove2me | solution 1 for WilliamsonShmoys.planar_facial_walk_data_edge_bound__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:06.846293+00:00
-- url     : https://prove2.me/submissions/b7ef7b97-8115-4eef-930e-2630157eb438

import Mathlib
import Theorems.Thm_WilliamsonShmoys_total_face_length_lower_bound__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
import Theorems.Thm_WilliamsonShmoys_facial_walk_total_length_eq_twice_edge_card__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (k : ℕ) (faces : Fin k → List (V × V))
    (hlen : ∀ i, 3 ≤ (faces i).length)
    (hcount : (letI : DecidableRel G.Adj := dG; ∀ u v,
      (List.flatten (List.ofFn faces)).count (u, v) =
        if G.Adj u v then 1 else 0))
    (heuler : Fintype.card V + k =
      (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) ≤ 3 * Fintype.card V - 6 := by
  letI : DecidableRel G.Adj := dG
  have hlength :=
    WilliamsonShmoys.total_face_length_lower_bound__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
      (k := k) (faces := faces) hlen
  have hcount_length :=
    WilliamsonShmoys.facial_walk_total_length_eq_twice_edge_card__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
      G dG k faces hcount
  have hineq : 3 * k ≤ 2 * G.edgeFinset.card := by
    rw [← hcount_length]
    exact hlength
  omega