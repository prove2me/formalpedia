-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.coeff_one_l_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:03:46.848805+00:00
-- url     : https://prove2.me/submissions/22d560e4-5232-485a-bcc3-ced708842f35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_l_const

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
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
variable {l ex : PowerSeries ℂ_[p]}
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 l ≠ 0 := by
  intro h1
  have hl0 := l_const hex0 hinv
  have hX2 : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ l := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simpa using hl0
    · exact h1
  obtain ⟨q, hq⟩ := hX2
  obtain ⟨e', he'⟩ := PowerSeries.X_dvd_iff.mpr hex0
  have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key : PowerSeries.subst ex l = (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 *
      (e' ^ 2 * PowerSeries.subst ex q) := by
    rw [hq, PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, he']
    ring
  rw [hinv] at key
  have h2 : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ PowerSeries.X := ⟨_, key⟩
  rw [PowerSeries.X_pow_dvd_iff] at h2
  simpa using h2 1 (by norm_num)
end PI.PhNormUnits.UnitaryGroupMassFormula
