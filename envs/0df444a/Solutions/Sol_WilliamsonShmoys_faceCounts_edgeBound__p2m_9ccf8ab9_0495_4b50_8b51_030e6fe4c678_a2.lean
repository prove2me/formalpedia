-- Prove2me | solution 1 for WilliamsonShmoys.faceCounts_edgeBound__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:30:41.432018+00:00
-- url     : https://prove2.me/submissions/039c15db-91f1-45ab-a5ed-f4dd10d1f38b

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (H : SimpleGraph V) (F : ℕ)
    (faceLength : Fin F → ℕ)
    (hEuler : (Fintype.card V : ℤ) - (H.edgeSet.ncard : ℤ) + (F : ℤ) = 2)
    (hIncidences : (∑ f : Fin F, faceLength f) = 2 * H.edgeSet.ncard)
    (hFaceLength : ∀ f, 3 ≤ faceLength f)
    (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  have hsum : 3 * F ≤ ∑ f : Fin F, faceLength f := by
    calc
      3 * F = ∑ _f : Fin F, 3 := by simp [mul_comm]
      _ ≤ ∑ f : Fin F, faceLength f :=
        Finset.sum_le_sum fun f _ => hFaceLength f
  have hsumZ : (3 : ℤ) * F ≤ 2 * (H.edgeSet.ncard : ℤ) := by
    exact_mod_cast (hsum.trans_eq hIncidences)
  have hVZ : (3 : ℤ) ≤ (Fintype.card V : ℤ) := by
    exact_mod_cast hV
  omega