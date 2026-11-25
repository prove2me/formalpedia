-- Prove2me | solution 1 for PI.HookSteps.Cap.capelli_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:57.809361+00:00
-- url     : https://prove2.me/submissions/46a39050-2062-414f-b2c1-21497b17b53a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps
import Theorems.Thm_PI_HookSteps_Cap_mulLeft_eq_lmul
import Theorems.Thm_PI_HookSteps_Cap_xw_xo
import Theorems.Thm_PI_HookSteps_Cap_sum_perm_of_noninj
import Theorems.Thm_PI_HookSteps_Cap_detD_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial Finset
namespace PI.HookSteps.Cap
theorem _root_.solution : CapSquare := by
  intro N
  set P := MvPolynomial (Fin N × Fin N) ℚ
  set M : Matrix (Fin N) (Fin N) P := Matrix.of fun a b => (X (a, b) : P) with hM
  have hdet : ∀ s : Fin N → Fin N, ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      xw (xo N) (fun j => σ j) s = Algebra.lmul ℚ P (M.submatrix id s).det := by
    intro s
    rw [Matrix.det_apply, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [xw_xo, Units.smul_def, map_zsmul]
    rfl
  unfold Pn
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← smul_mul_assoc, ← Finset.sum_mul, hdet]
  rw [sum_perm_of_noninj N (fun s => Algebra.lmul ℚ P (M.submatrix id s).det * dw (dop N) id s)]
  · rw [detD_eq, Finset.mul_sum, mulLeft_eq_lmul]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Matrix.det_permute', map_mul, map_intCast, mul_assoc, ← zsmul_eq_mul, mul_smul_comm]
    rfl
  · intro s hs
    simp only [Function.Injective, not_forall] at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij]), map_zero, zero_mul]
end PI.HookSteps.Cap
