-- Prove2me | solution 1 for PI.BeDiagZp.IdentW.coeff_one_l_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:49.333485+00:00
-- url     : https://prove2.me/submissions/c575031b-adc5-43ad-9886-7c7d660fb8ca

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.IdentW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.IdentW
theorem _root_.solution {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 l ≠ 0 := by
  intro h1
  have hex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hXe : (PowerSeries.X : PowerSeries ℂ_[p]) ∣ ex := PowerSeries.X_dvd_iff.2 hex0
  have key := congrArg (PowerSeries.coeff 1) h
  rw [PowerSeries.coeff_subst' hex, finsum_eq_zero_of_forall_eq_zero] at key
  · simp at key
  · intro d
    rcases Nat.lt_or_ge d 2 with hd | hd
    · interval_cases d
      · simp
      · rw [h1, zero_smul]
    · have h0 : PowerSeries.coeff 1 (ex ^ d) = 0 :=
        PowerSeries.X_pow_dvd_iff.1 ((pow_dvd_pow PowerSeries.X hd).trans (pow_dvd_pow_of_dvd hXe d)) 1
          (by norm_num)
      rw [h0, smul_zero]
end PI.BeDiagZp.IdentW
