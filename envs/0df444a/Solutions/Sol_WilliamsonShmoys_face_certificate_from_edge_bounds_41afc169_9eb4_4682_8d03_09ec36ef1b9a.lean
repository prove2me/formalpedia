-- Prove2me | solution 1 for WilliamsonShmoys.face_certificate_from_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:40:46.37083+00:00
-- url     : https://prove2.me/submissions/2a96abaf-2b18-4e72-8d4e-f0846dd77885

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCertificate
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hmin : Fintype.card V - 1 ≤ L.edgeSet.ncard)
    (hmax : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6) :
    Nonempty (WilliamsonShmoys.PlanarFaceCertificate L) := by
  classical
  have hpos : 0 < L.edgeSet.ncard := by omega
  obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  induction e using Sym2.ind with
  | h a b =>
  have hab : L.Adj a b := he
  set m := L.edgeSet.ncard
  refine ⟨⟨List.replicate (2 * m) (a, b) :: List.replicate (m + 2 - Fintype.card V - 1) [], ?_, ?_, ?_, ?_⟩⟩
  · intro face hf x hx
    simp only [List.mem_cons, List.mem_replicate] at hf
    rcases hf with rfl | ⟨-, rfl⟩
    · rw [(List.mem_replicate.mp hx).2]; exact hab
    · simp at hx
  · simp only [List.length_cons, List.length_replicate]; omega
  · simp only [List.length_cons, List.length_replicate, List.map_cons, List.map_replicate,
      List.sum_cons, List.length_nil, List.sum_replicate, smul_eq_mul, mul_zero, add_zero]; omega
  · simp only [List.map_cons, List.map_replicate, List.length_replicate, List.length_nil,
      List.sum_cons, List.sum_replicate, smul_eq_mul, mul_zero, add_zero, m]
