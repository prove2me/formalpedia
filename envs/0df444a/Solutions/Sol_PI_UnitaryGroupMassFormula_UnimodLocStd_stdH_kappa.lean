-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.stdH_kappa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:41.281287+00:00
-- url     : https://prove2.me/submissions/c1984a2c-50f4-42b8-9fa9-54b357a86efd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdH_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) (hlam : lam ≠ 0) (x y : m → ℂ) :
    stdH L m x y = kappa L lam * ∑ i, (x i / lam) * conj (y i / lam) := by
  have hc : conj lam ≠ 0 := by rwa [Ne, map_eq_zero]
  have h1 : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam
  have h2 : conj lam * (conj lam)⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [stdH_apply]
  simp only [kappa]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_div₀]
  linear_combination (-(x i * conj (y i) * ((area L : ℝ) : ℂ)⁻¹) * (conj lam * (conj lam)⁻¹)) * h1 +
    (-(x i * conj (y i) * ((area L : ℝ) : ℂ)⁻¹)) * h2
end PI.UnitaryGroupMassFormula.UnimodLocStd
