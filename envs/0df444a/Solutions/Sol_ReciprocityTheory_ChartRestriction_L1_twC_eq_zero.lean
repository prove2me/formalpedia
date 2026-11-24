-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.twC_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:38.927432+00:00
-- url     : https://prove2.me/submissions/42857496-e814-40ef-8543-195e11fd4e3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_lt_sq_pow

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
theorem _root_.solution (hl : 2 ≤ l) (τ : K →+* K) (h0 : constantCoeff lam = 0) {n m : ℕ}
    (hnm : n ≤ m) : twC l τ lam n m = 0 := by
  unfold twC
  split_ifs with hd
  · have hlt : n < (l ^ 2) ^ m := lt_of_le_of_lt hnm (hon_lt_sq_pow hl m)
    rw [Nat.div_eq_of_lt hlt, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rfl
end ReciprocityTheory.ChartRestriction.L1
