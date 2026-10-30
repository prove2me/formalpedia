-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:11.528632+00:00
-- url     : https://prove2.me/submissions/02f94f4f-6a2b-4086-85fb-f4c3929dbee5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_certificate__p2m_cf74d45a_14dc_4f14_a147_2f00563f3e8c_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 <= Fintype.card V) :
    exists (F : Type) (_ : Fintype F),
      Fintype.card V + Fintype.card F = M.edgeSet.ncard + 2 /\
      3 * Fintype.card F <= 2 * M.edgeSet.ncard := by
  obtain ⟨F, instF, length, hEuler, hTotal, hLength⟩ :=
    WilliamsonShmoys.planar_drawing_face_certificate__p2m_cf74d45a_14dc_4f14_a147_2f00563f3e8c_a1
      M hM hconn hV
  letI : Fintype F := instF
  refine ⟨F, inferInstance, hEuler, ?_⟩
  have hLower : 3 * Fintype.card F ≤ ∑ f : F, length f := by
    calc
      3 * Fintype.card F = ∑ _f : F, (3 : Nat) := by simp <;> omega
      _ ≤ ∑ f : F, length f :=
        Finset.sum_le_sum (fun f _ => hLength f)
  omega