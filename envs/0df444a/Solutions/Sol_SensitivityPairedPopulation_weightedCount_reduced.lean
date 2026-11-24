-- Prove2me | solution 1 for SensitivityPairedPopulation.weightedCount_reduced
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:39.410543+00:00
-- url     : https://prove2.me/submissions/6762e1d3-87d9-422b-a75e-4d83d343010c

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedReducedPopulation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityPairedPopulation
end SensitivityPairedPopulation


/-! The literal paired objectives have a common price on all tiers below the
last. Their finite population bound therefore needs two cumulative counts. -/
open SensitivityPairedPopulation

theorem solution (prices : Fin 4 → ℕ) (n : Population) (q : Fin 4)
    (h : CommonLowerPrice prices q) :
    weightedCount prices n q = previousCount n q * prices (previousTier q) +
      (prefixCount n q - previousCount n q) * prices q := by
  fin_cases q
  · simp [weightedCount,previousCount,previousTier,prefixCount]
  · simp [weightedCount,previousCount,previousTier,prefixCount]
  · have h0 := h 0 (by decide)
    change prices 0 = prices 1 at h0
    simp [weightedCount,previousCount,previousTier,prefixCount,h0]
    change n 0 * prices 1 + n 1 * prices 1 = (n 0 + n 1) * prices 1
    ring
  · have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    change prices 0 = prices 2 at h0
    change prices 1 = prices 2 at h1
    simp [weightedCount,previousCount,previousTier,prefixCount,h0,h1]
    ring
