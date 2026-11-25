-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:19.141482+00:00
-- url     : https://prove2.me/submissions/40e8712c-c052-4296-ae50-4698ee0d4615

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_pow_mul_pow_eq_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv_of_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_reindex

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution {D E : MvPowerSeries σ ℂ_[p]} (hD : constantCoeff D = 0) (hE : constantCoeff E = 0) :
    expMv (D + E) = expMv D * expMv E := by
  ext α
  have hR : coeff α (expMv D * expMv E) = ∑ i ∈ Finset.range (α.degree + 1), ∑ j ∈ Finset.range (α.degree + 1),
      coeff α (D ^ i * E ^ j) / ((i.factorial : ℂ_[p]) * (j.factorial : ℂ_[p])) := by
    rw [MvPowerSeries.coeff_mul]
    have step : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α, coeff x.1 (expMv D) * coeff x.2 (expMv E) =
        ∑ i ∈ Finset.range (α.degree + 1), ∑ j ∈ Finset.range (α.degree + 1),
          coeff x.1 (D ^ i) * coeff x.2 (E ^ j) / ((i.factorial : ℂ_[p]) * (j.factorial : ℂ_[p])) := by
      intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hdeg : x.1.degree + x.2.degree = α.degree := by rw [← hx, map_add]
      rw [coeff_expMv_of_le hD α.degree (by omega), coeff_expMv_of_le hE α.degree (by omega),
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [div_mul_div_comm]
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.coeff_mul, Finset.sum_div]
  have hL : coeff α (expMv (D + E)) = ∑ n ∈ Finset.range (α.degree + 1), ∑ m ∈ Finset.range (n + 1),
      coeff α (D ^ m * E ^ (n - m)) / ((m.factorial : ℂ_[p]) * ((n - m).factorial : ℂ_[p])) := by
    rw [coeff_expMv]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_pow, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [mul_comm _ ((n.choose m : ℕ) : MvPowerSeries σ ℂ_[p]), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    have hc : ((n.choose m : ℕ) : ℂ_[p]) * (m.factorial : ℂ_[p]) * ((n - m).factorial : ℂ_[p]) =
        (n.factorial : ℂ_[p]) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmn
    have h1 : ((n.choose m : ℕ) : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hmn).ne'
    rw [← hc, mul_assoc, mul_div_mul_left _ _ h1]
  rw [hL, hR]
  exact reindex _ (fun i j => coeff α (D ^ i * E ^ j) / ((i.factorial : ℂ_[p]) * (j.factorial : ℂ_[p])))
    (fun i j hij => by rw [coeff_pow_mul_pow_eq_zero hD hE hij, zero_div])
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
