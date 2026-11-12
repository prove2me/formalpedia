-- Prove2me | solution 1 for PGDMap20261031.entropy_error_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:05:58.80651+00:00
-- url     : https://prove2.me/submissions/2c23a561-5441-4148-8e32-a2f6f784b177

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem solution : ∀ A B : ℝ, 0 < A → 0 < B → StrictMonoOn (fun v : ℝ => (v - A) / (v + B)) (Set.Ioi (0 : ℝ)) := by
  intro A B hA hB v hv w hw hvw
  have hvden : 0 < v + B := add_pos hv hB
  have hwden : 0 < w + B := add_pos hw hB
  apply (div_lt_div_iff₀ hvden hwden).mpr
  have hprod : 0 < (A + B) * (w - v) :=
    mul_pos (add_pos hA hB) (sub_pos.mpr hvw)
  nlinarith
