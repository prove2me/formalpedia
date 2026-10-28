-- Prove2me | solution 1 for WilliamsonShmoys.triangular_map_face_dart_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:03:54.749318+00:00
-- url     : https://prove2.me/submissions/6cce2f36-6e05-45c5-9c6f-041a60dd16d7

import Definitions.Def_WilliamsonShmoys_TriangularMap

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    {m : Nat}
    (M : WilliamsonShmoys.TriangularMap H (Fin m)) :
    3 * m = 2 * H.edgeSet.ncard := by 
  classical
  have h1 : Fintype.card (Fin m × Fin 3) = Fintype.card H.Dart := Fintype.card_congr M.dart
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, SimpleGraph.dart_card_eq_twice_card_edges] at h1
  rw [Set.ncard_eq_toFinset_card', mul_comm, h1]
  congr 2
