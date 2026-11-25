-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.cW_unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:28.245992+00:00
-- url     : https://prove2.me/submissions/306263d3-daa2-4092-9ffe-4b74109fadd2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {K : Type} [Field K] (g2 g3 : K) (k : ℕ) : cW g2 g3 k =
    if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
    if 4 ≤ k then
      3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
        ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
    else 0 := by
  rw [cW]
  first
    | (rw [Nat.strongRecOn_beta]; rfl)
    | (rw [Nat.strongRecOn'_beta]; rfl)
    | (rw [Nat.strongRecOn_eq]; rfl)
    | (unfold Nat.strongRecOn; rw [Nat.strongRec_eq]; rfl)
    | (exact (Nat.strongRecOn_beta' ..).trans rfl)
end ReciprocityTheory.ChartRestriction.L1
