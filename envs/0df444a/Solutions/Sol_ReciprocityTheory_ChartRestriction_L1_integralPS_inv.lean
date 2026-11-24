-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralPS_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:13.84227+00:00
-- url     : https://prove2.me/submissions/90bc04ff-b5eb-4367-abe2-5c6acf0e8544

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
theorem _root_.solution {f : PowerSeries K} (hf : IntegralPS f) (h0 : ‖constantCoeff f‖ = 1) :
    IntegralPS f⁻¹ := by
  unfold IntegralPS at hf ⊢
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rw [PowerSeries.coeff_inv]
  split_ifs with hn
  · rw [norm_inv, h0, inv_one]
  · rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
    refine Finset.sum_induction _ (fun z : K => ‖z‖ ≤ 1)
      (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
      (by rw [norm_zero]; exact zero_le_one) ?_
    intro p _
    split_ifs with hlt
    · rw [norm_mul]
      exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hlt)
    · rw [norm_zero]
      exact zero_le_one
end ReciprocityTheory.ChartRestriction.L1
