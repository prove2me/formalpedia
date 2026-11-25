-- Prove2me | solution 1 for PI.DvRows.neg_vAdd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:27.332868+00:00
-- url     : https://prove2.me/submissions/c2bf6b75-ae09-4c98-bd9b-bda8770613fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x c : K) (hc : c ≠ 0)
    (hci : w.valuation K c ≤ 1) (d : ℕ) (h : w.valuation K x * (w.valuation K c) ^ d ≤ 1) :
    -vAdd w x ≤ (d : ℤ) * vAdd w c := by
  have hc0 : w.valuation K c ≠ 0 := by simpa using hc
  have hlc : WithZero.log (w.valuation K c) ≤ 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log hc0 one_ne_zero).2 hci
  unfold vAdd
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, WithZero.log_zero, neg_zero]
    nlinarith
  · have hx0 : w.valuation K x ≠ 0 := by simpa using hx
    have hp : w.valuation K x * (w.valuation K c) ^ d ≠ 0 := mul_ne_zero hx0 (pow_ne_zero _ hc0)
    have := (WithZero.log_le_log hp one_ne_zero).2 h
    rw [WithZero.log_mul hx0 (pow_ne_zero _ hc0), WithZero.log_pow, WithZero.log_one] at this
    simp only [nsmul_eq_mul] at this
    linarith
end PI.DvRows
