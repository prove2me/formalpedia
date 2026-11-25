-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.twC_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:31.20835+00:00
-- url     : https://prove2.me/submissions/42dd7689-5168-4f30-b4e3-536d1f0f0918

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
theorem _root_.solution (τ : K →+* K) {n i : ℕ} (hd : ¬ (l ^ 2) ^ i ∣ n) (j : ℕ) :
    twC l τ lam n (i + j) = 0 := by
  unfold twC
  rw [if_neg]
  intro h
  exact hd (dvd_trans (pow_dvd_pow _ (Nat.le_add_right i j)) h)
end ReciprocityTheory.ChartRestriction.L1
