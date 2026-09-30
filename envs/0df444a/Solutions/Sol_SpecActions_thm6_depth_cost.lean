-- Prove2me | solution 1 for SpecActions.thm6_depth_cost
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T04:19:00.62059+00:00
-- url     : https://prove2.me/submissions/a995997c-0d89-41d8-9045-fd91821e8380

import Mathlib
import Definitions.Def_SpecActions_model

open Finset SpecActions

theorem solution (T : ℕ) (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : 1 ≤ T) :
    (depthSpecCost T a b p - depthSeqCost T a) / depthSeqCost T a
      = ((T : ℝ) - 1) / (T : ℝ) *
          ((1 - p) * (a * ⌊a / b⌋ - b * ((1 + ⌊a / b⌋) * ⌊a / b⌋ / 2))
            + p * (b * ⌊a / b⌋)) / a := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  unfold depthSpecCost depthSeqCost
  field_simp
  ring
