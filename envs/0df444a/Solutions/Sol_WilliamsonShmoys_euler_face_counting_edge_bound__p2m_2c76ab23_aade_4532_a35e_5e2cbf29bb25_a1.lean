-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_counting_edge_bound__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:36:10.1072+00:00
-- url     : https://prove2.me/submissions/2b7ef981-2ae7-437f-adf3-4428b3b46da6

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (F : Type) [Fintype F] [DecidableEq F] (face : K.Dart → F)
    (hEuler : Fintype.card V + Fintype.card F = K.edgeFinset.card + 2)
    (hdeg : ∀ f : F, 3 ≤ Fintype.card {d : K.Dart // face d = f})
    (hcount : (∑ f : F, Fintype.card {d : K.Dart // face d = f}) = Fintype.card K.Dart)
    (hdart : Fintype.card K.Dart = 2 * K.edgeFinset.card)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  have hsum : 3 * Fintype.card F ≤
      ∑ f : F, Fintype.card {d : K.Dart // face d = f} := by
    calc
      3 * Fintype.card F = ∑ _f : F, 3 := by simp [mul_comm]
      _ ≤ ∑ f : F, Fintype.card {d : K.Dart // face d = f} :=
        Finset.sum_le_sum (fun f _ => hdeg f)
  have hbound : 3 * Fintype.card F ≤ 2 * K.edgeFinset.card := by
    rw [hcount, hdart] at hsum
    exact hsum
  omega