-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T04:55:58.01231+00:00
-- url     : https://prove2.me/submissions/9d71fbc6-9dbe-4cdd-b5b8-e6e0b0324b66

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (inst : Fintype F),
      @Fintype.card V inferInstance + @Fintype.card F inst = H.edgeSet.ncard + 2 ∧
      3 * @Fintype.card F inst ≤ 2 * H.edgeSet.ncard := by
  obtain ⟨F, inst, length, heuler, hlength, htotal⟩ :=
    WilliamsonShmoys.face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5
      H hH hconn hcard
  letI : Fintype F := inst
  refine ⟨F, inst, heuler, ?_⟩
  calc
    3 * Fintype.card F = ∑ _f : F, (3 : Nat) := by
      simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ f : F, length f := by
      exact Finset.sum_le_sum (fun f _ => hlength f)
    _ = 2 * H.edgeSet.ncard := htotal