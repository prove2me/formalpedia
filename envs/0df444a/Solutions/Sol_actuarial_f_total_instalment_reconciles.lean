-- Prove2me | solution 1 for actuarial_f_total_instalment_reconciles
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:49.461032+00:00
-- url     : https://prove2.me/submissions/44d24de7-6cbb-4343-a016-90de0a72b5f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_totalInstalment

open ActuarialUnderpinsF

theorem solution (h r g z i j t : ℕ)
    (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    totalInstalment h r g z i j t a b c s estate g0 g1 gs ge =
      (awardBase a b z * g0 t + c z * g1 t) * memberDue r i t +
      spouseInstalment h z i j t s gs + estateInstalment h r g z i t estate ge := by
  unfold totalInstalment memberTrancheOne memberTrancheTwo
  grind
