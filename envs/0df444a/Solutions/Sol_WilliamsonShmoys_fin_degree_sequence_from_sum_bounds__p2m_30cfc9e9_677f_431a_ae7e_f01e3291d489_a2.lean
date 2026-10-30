-- Prove2me | solution 1 for WilliamsonShmoys_fin_degree_sequence_from_sum_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:12:29.210235+00:00
-- url     : https://prove2.me/submissions/13af4c62-7b8a-4edf-b20f-298d143e2720

import Mathlib

set_option autoImplicit false

theorem solution
    (f m : ℕ)
    (hf : 0 < f)
    (hSum : 3 * f ≤ 2 * m) :
    ∃ (degrees : Fin f → ℕ),
      (∀ i, 3 ≤ degrees i) ∧
      (∑ i : Fin f, degrees i) = 2 * m := by
  let i0 : Fin f := ⟨0, by omega⟩
  let extra : ℕ := 2 * m - 3 * f
  have hextra : 0 ≤ extra := by
    dsimp [extra]
    omega
  refine ⟨fun i => 3 + if i = i0 then extra else 0, ?_, ?_⟩
  · intro i
    by_cases hi : i = i0 <;> simp [hi] <;> omega
  · calc
      (∑ i : Fin f, (3 + if i = i0 then extra else 0))
          = (∑ _i : Fin f, 3) + (∑ i : Fin f, if i = i0 then extra else 0) := by
              rw [Finset.sum_add_distrib]
      _ = f * 3 + extra := by
            simp [i0]
      _ = 2 * m := by
            dsimp [extra]
            omega
