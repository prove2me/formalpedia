-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hon_lt_sq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:29.094641+00:00
-- url     : https://prove2.me/submissions/3939690d-d2ca-4635-ab3a-26041c324e18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : 2 ≤ l) (n : ℕ) : n < (l ^ 2) ^ n := by
  have h4 : 1 < l ^ 2 := by nlinarith
  first
  | exact Nat.lt_pow_self h4
  | exact Nat.lt_pow_self h4 n
end ReciprocityTheory.ChartRestriction.L1
