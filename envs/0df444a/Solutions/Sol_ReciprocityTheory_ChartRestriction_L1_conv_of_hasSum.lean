-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.conv_of_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:34:35.506351+00:00
-- url     : https://prove2.me/submissions/bdd3935b-9356-4d03-a771-f4b6d211d8d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {f : PowerSeries ℂ}
    (h : ∀ x : ℂ, ‖x‖ < 1 → Summable fun n => PowerSeries.coeff n f * x ^ n) : Conv f := by
  intro x hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg x) hxr
  have hr' : r ≠ 0 := hr0.ne'
  have hrn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hs := h (r : ℂ) (by rw [hrn]; exact hr1)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ hs.tendsto_atTop_zero)
  have hq0 : 0 ≤ ‖x‖ / r := div_nonneg (norm_nonneg _) hr0.le
  have hq : ‖x‖ / r < 1 := (div_lt_one hr0).mpr hxr
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one hq0 hq).mul_left C)
  have h1 : ‖PowerSeries.coeff n f * (r : ℂ) ^ n‖ ≤ C := hC _ ⟨n, rfl⟩
  rw [norm_mul, norm_pow, hrn] at h1
  calc ‖PowerSeries.coeff n f‖ * ‖x‖ ^ n
      = (‖PowerSeries.coeff n f‖ * r ^ n) * (‖x‖ / r) ^ n := by
        rw [div_pow]
        field_simp
    _ ≤ C * (‖x‖ / r) ^ n := mul_le_mul_of_nonneg_right h1 (pow_nonneg hq0 n)
end ReciprocityTheory.ChartRestriction.L1
