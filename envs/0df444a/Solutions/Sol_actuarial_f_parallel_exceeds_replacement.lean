-- Prove2me | solution 1 for actuarial_f_parallel_exceeds_replacement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:38:18.804917+00:00
-- url     : https://prove2.me/submissions/b320d6d2-aa48-4998-9d53-a15d44ca2fba

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_parallelPayment
import Definitions.Def_actuarial_f_replacementPayment
import Definitions.Def_actuarial_f_spouseInstalment

open ActuarialUnderpinsF

theorem solution (h r g z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (estateBase ge : ℕ → ℝ)
    (hsp : 0 ≤ spouseInstalment h z i j t s gs) :
    replacementPayment h r g z i j t s gs estateBase ge ≤
      parallelPayment h r g z i j t s gs estateBase ge := by
  unfold replacementPayment parallelPayment
  split_ifs <;> grind
