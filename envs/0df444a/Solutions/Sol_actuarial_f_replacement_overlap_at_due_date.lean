-- Prove2me | solution 1 for actuarial_f_replacement_overlap_at_due_date
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:02.355267+00:00
-- url     : https://prove2.me/submissions/c2ff4bc9-a81f-46db-b159-f91bceab0b09

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_replacementTotalInstalment
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_totalInstalment

open ActuarialUnderpinsF

theorem solution
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    totalInstalment h r g z i j t a b c s estate g0 g1 gs ge =
      replacementTotalInstalment h r g z i j t a b c s estate g0 g1 gs ge +
        (if estateDue h r g i t = 1 then
           spouseInstalment h z i j t s gs else 0) := by
  unfold totalInstalment replacementTotalInstalment replacementPayment
  split_ifs <;> grind
