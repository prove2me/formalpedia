-- Prove2me | solution 1 for WilliamsonShmoys.face_equations_of_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:20:03.673999+00:00
-- url     : https://prove2.me/submissions/29689607-3536-4ab9-b798-2e75a93e3daf

import Mathlib

theorem solution
    (n m : ℕ) (hn : 3 ≤ n) (hm : m + 6 = 3 * n) :
    ∃ f : ℕ, n + f = m + 2 ∧ 3 * f = 2 * m :=
  ⟨2 * n - 4, by omega, by omega⟩
