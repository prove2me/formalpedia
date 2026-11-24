-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_expand_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:45:10.20339+00:00
-- url     : https://prove2.me/submissions/5e9cc61e-6aee-4bd7-a1c8-159d2ecde862

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {ι : Type} (x : K) (n : ℕ) (hn : n ≠ 0) (F : MvPowerSeries ι K) :
    DivByMv x (MvPowerSeries.expand n hn F) ↔ DivByMv x F := by
  classical
  constructor
  · intro h d
    have := h (n • d)
    rwa [MvPowerSeries.coeff_expand_smul] at this
  · intro h d
    by_cases hd : ∀ i, n ∣ d i
    · have e : d = n • Finsupp.mapRange (fun k => k / n) (Nat.zero_div n) d := by
        ext i
        simp [Nat.mul_div_cancel' (hd i)]
      rw [e, MvPowerSeries.coeff_expand_smul]
      exact h _
    · push_neg at hd
      obtain ⟨i, hi⟩ := hd
      rw [MvPowerSeries.coeff_expand_of_not_dvd n hn F hi, norm_zero]
      exact norm_nonneg _
end ReciprocityTheory.ChartRestriction.L1
