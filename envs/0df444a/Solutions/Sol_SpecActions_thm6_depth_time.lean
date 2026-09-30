-- Prove2me | solution 1 for SpecActions.thm6_depth_time
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T04:19:00.061698+00:00
-- url     : https://prove2.me/submissions/a5579b72-3ad1-409c-bca9-cf2a3036b9af

import Mathlib
import Definitions.Def_SpecActions_model

open Finset SpecActions

theorem solution (T : ℕ) (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : 1 ≤ T) :
    (depthSeqTime T a - depthSpecTime T a b p) / depthSeqTime T a
      = ((T : ℝ) - 1) / (T : ℝ) * p * (1 - b / a) := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  unfold depthSeqTime depthSpecTime
  field_simp
  ring
