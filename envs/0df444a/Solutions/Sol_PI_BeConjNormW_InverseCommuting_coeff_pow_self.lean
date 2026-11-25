-- Prove2me | solution 1 for PI.BeConjNormW.InverseCommuting.coeff_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:33.914999+00:00
-- url     : https://prove2.me/submissions/e799a2bb-b8bc-44d9-a580-aa991fe0b190

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_MemIntegerRingIffNormLeOne

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
theorem _root_.solution {f : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) (n : ℕ) :
    coeff n (f ^ n) = coeff 1 f ^ n := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf0
  have h1 : coeff 1 (X * g) = constantCoeff g := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [h1, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow]
end PI.BeConjNormW.InverseCommuting
