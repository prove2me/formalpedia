-- Prove2me | solution 1 for WilliamsonShmoys.edgeBound_of_faceCounts
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:42:04.698374+00:00
-- url     : https://prove2.me/submissions/ac54d3bd-8d2e-4f6e-8351-1add2133cafd

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hFaces : ∃ (F : Nat) (faceLength : Fin F → Nat),
      Fintype.card V + F = G.edgeSet.ncard + 2 ∧
      (∑ f : Fin F, faceLength f) = 2 * G.edgeSet.ncard ∧
      ∀ f : Fin F, 3 ≤ faceLength f) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  rcases hFaces with ⟨F, faceLength, hEuler, hSum, hLength⟩
  have hLower : F * 3 ≤ ∑ f : Fin F, faceLength f := by
    calc
      F * 3 = ∑ _f : Fin F, 3 := by simp
      _ ≤ ∑ f : Fin F, faceLength f :=
        Finset.sum_le_sum (fun f _ => hLength f)
  omega