-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.stdH_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:06.894622+00:00
-- url     : https://prove2.me/submissions/023e99f4-ae8f-4df8-87b6-9d37af838d31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
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
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) (m : Type*) [Fintype m] [DecidableEq m] (x y : m → ℂ) :
    stdH L m x y = (∑ i, x i * conj (y i)) * ((area L : ℝ) : ℂ)⁻¹ := by
  simp only [PI.ULS.stdH, PI.ULS.matH, LinearMap.mk₂'ₛₗ_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  · intro j _ hj
    simp only [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hj), smul_eq_mul, mul_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
end PI.UnitaryGroupMassFormula.UnimodLocStd
