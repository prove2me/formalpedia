-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.coeff_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:47.507245+00:00
-- url     : https://prove2.me/submissions/ba6c12f0-c6ab-401b-90e9-6ddbf8a065c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
open PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
variable {p : ℕ} [Fact p.Prime]
namespace PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
theorem _root_.solution {σ R : Type*} [CommRing R] {F : MvPowerSeries σ R}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    ∀ (d : ℕ) (α : σ →₀ ℕ), Finsupp.degree α < d → MvPowerSeries.coeff α (F ^ d) = 0 := by
  intro d
  induction d with
  | zero => intro α h; omega
  | succ d ih =>
    intro α h
    rw [pow_succ', MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨β, γ⟩ hβγ
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hβγ
    dsimp only
    by_cases hβ : β = 0
    · subst hβ
      simp [hF]
    · have hb : Finsupp.degree β ≠ 0 := fun h0 => hβ ((Finsupp.degree_eq_zero_iff β).1 h0)
      have hdeg : Finsupp.degree α = Finsupp.degree β + Finsupp.degree γ := by
        rw [← hβγ, map_add]
      rw [ih γ (by omega), mul_zero]
end PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
