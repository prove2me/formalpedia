-- Prove2me | solution 1 for PI.BeConjNormW.InverseCommuting.coeff_pow_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:22.976211+00:00
-- url     : https://prove2.me/submissions/6c6156c5-a293-498e-8078-f81b1e973589

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_MemIntegerRingIffNormLeOne
import Theorems.Thm_PI_BeConjNormW_InverseCommuting_mem_integerRing_iff_norm_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical PowerSeries
open PI PI.BeConjNormW
open PI.BeConjNormW.InverseCommuting
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeConjNormW.InverseCommuting
theorem _root_.solution {f : PowerSeries ℂ_[p]} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (k n : ℕ) :
    ‖coeff n (f ^ k)‖ ≤ 1 := by
  have hf' : ∀ m, coeff m f ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := fun m => (mem_integerRing_iff_norm_le_one _).2 (hf m)
  rw [← mem_integerRing_iff_norm_le_one]
  induction k generalizing n with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    exact sum_mem fun x _ => mul_mem (ih _) (hf' _)
end PI.BeConjNormW.InverseCommuting
