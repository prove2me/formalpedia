-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_expMv_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:41.106303+00:00
-- url     : https://prove2.me/submissions/77f350a8-8819-49ff-b53f-c48dc2593f4b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_intP_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_valuation_coeff_mul_nonneg
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_isIntegralAt_neg
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_intP_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_int_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_expMv_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_expMv_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_constantCoeff_expMv

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
theorem _root_.solution {D : MvPowerSeries σ ℂ_[p]} (hD : constantCoeff D = 0)
    (h : IntegralMv (expMv D)) : IntegralMv (expMv (-D)) := by
  have hnD : constantCoeff (-D) = 0 := by rw [map_neg, hD, neg_zero]
  have hX : expMv (-D) * expMv D = 1 := by rw [← expMv_add hnD hD, neg_add_cancel, expMv_zero]
  have hU0 : coeff 0 (expMv D) = 1 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_expMv]
  suffices H : ∀ n, ∀ α : σ →₀ ℕ, α.degree < n → IsIntP (coeff α (expMv (-D))) from
    fun α => H _ α (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro α hα; exact absurd hα (Nat.not_lt_zero _)
  | succ n ih =>
    intro α hα
    have e := congrArg (coeff α) hX
    have hmem : (α, (0 : σ →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal α := by simp
    rw [MvPowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem, hU0, mul_one] at e
    rw [eq_sub_of_add_eq e, sub_eq_add_neg]
    refine intP_add (int_one α) (isIntegralAt_neg (intP_sum _ _ fun x hx => valuation_coeff_mul_nonneg (ih x.1 ?_) (h x.2)))
    have hx' := Finset.mem_erase.mp hx
    have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx'.2
    have h2 : x.2 ≠ 0 := by
      intro h0
      apply hx'.1
      exact Prod.ext (by rw [← h1, h0, add_zero]) h0
    have h3 : x.2.degree ≠ 0 := fun hd => h2 ((Finsupp.degree_eq_zero_iff _).mp hd)
    have h4 : x.1.degree + x.2.degree = α.degree := by rw [← h1, map_add]
    omega
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
