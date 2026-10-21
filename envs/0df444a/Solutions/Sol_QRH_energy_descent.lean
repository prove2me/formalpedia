-- Prove2me | solution 1 for QRH.energy_descent
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:08:41.93951+00:00
-- url     : https://prove2.me/submissions/b05cbd18-c8bf-4c63-8f74-63b36bc32408

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun
universe u

theorem solution : ¬ (∀ (f : ℕ → ℝ) (c A B : ℝ),
    f 0 ≤ c →
    (∀ i : ℕ, f (i + 1) ≤ A + B * f i) →
    0 ≤ B →
    ∀ i : ℕ, f i ≤ (c + (i : ℝ) * A) * (max 1 B) ^ i) := by
  intro h
  have := h (fun _ => 1) 1 (-1) 2 le_rfl (fun i => by norm_num) (by norm_num) 2
  norm_num at this
