-- Prove2me | solution 1 for OnlinePrimalDual.GroupSteiner.theorem11_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:17:56.767933+00:00
-- url     : https://prove2.me/submissions/319d8d3c-8936-42ac-809f-3fe13ac84cd9

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree
import Definitions.Def_OnlinePrimalDual_GroupSteiner_expectedCost

namespace OnlinePrimalDual.GroupSteiner

end OnlinePrimalDual.GroupSteiner

open OnlinePrimalDual.GroupSteiner

theorem solution {E : Type*} [Fintype E] [DecidableEq E]
    (tr : RoundedTree E) (n : ℕ) (hn : 0 < n)
    (w' : E → ℝ) (fracRatio OPT : ℝ) (hOPT_nonneg : 0 ≤ OPT)
    (hfrac_ratio : ∑ e, tr.cost e * w' e ≤ fracRatio * OPT) (hfracRatio : fracRatio ≤ Real.log n)
    (T : ℕ)
    (ρ : RandomCover E)
    (hcost : ρ.expectedCost tr.cost ≤ (T : ℝ) * (fracRatio * OPT)) :
    ρ.expectedCost tr.cost ≤ (T : ℝ) * Real.log n * OPT := by
  have h1 : fracRatio * OPT ≤ Real.log n * OPT :=
    mul_le_mul_of_nonneg_right hfracRatio hOPT_nonneg
  have h2 : (T : ℝ) * (fracRatio * OPT) ≤ (T : ℝ) * (Real.log n * OPT) :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg T)
  calc ρ.expectedCost tr.cost ≤ (T : ℝ) * (fracRatio * OPT) := hcost
    _ ≤ (T : ℝ) * (Real.log n * OPT) := h2
    _ = (T : ℝ) * Real.log n * OPT := by ring
