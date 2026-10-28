-- Prove2me | solution 1 for actuarial_f_bridge_adds_separate_instalment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:06.0036+00:00
-- url     : https://prove2.me/submissions/6e1492de-fea0-4d4f-a441-7b67dfac4149

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeAugmentedInstalment
import Definitions.Def_actuarial_f_bridgeInstalment
import Definitions.Def_actuarial_f_totalInstalment

open ActuarialUnderpinsF

theorem solution
    (h r g z i j t start stop : ℕ) (bridge : ℝ)
    (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) :
    bridgeAugmentedInstalment h r g z i j t start stop bridge
        a b c s estate g0 g1 gs ge =
      totalInstalment h r g z i j t a b c s estate g0 g1 gs ge +
        bridgeInstalment start stop t bridge := by
  rfl
