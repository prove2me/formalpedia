-- Prove2me | solution 1 for PI.BeConjNormW.InverseCommuting.coeff_pow_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:27.839314+00:00
-- url     : https://prove2.me/submissions/940a047b-2607-4cad-ba54-faf8ac2fcc7c

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
theorem _root_.solution {f : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) {k n : ℕ} (h : n < k) :
    coeff n (f ^ k) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf0
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]
end PI.BeConjNormW.InverseCommuting
