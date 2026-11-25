-- Prove2me | solution 1 for PI.HookSteps.determinant_shift_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:50.52996+00:00
-- url     : https://prove2.me/submissions/7c479735-cb9d-46b2-9a1e-1198b89d368b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShift
import Theorems.Thm_PI_HookSteps_fockQ_smul_right
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_c2_holds_alt
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRaise
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_coeff_euler
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
variable {N : ℕ}
namespace PI.HookSteps
theorem _root_.solution : DetShiftNormOf := by
  intro hAdj hDD hPol hHw N ν hν
  have hν' : Antitone (fun i : Fin N => ν i + 1) := fun a b hab => Nat.add_le_add_right (hν hab) 1
  have hG' := hHw N ν hν

  have heul : ∀ a : Fin N, rowDiv ℚ a a 1 (hw ℚ le_rfl (fun i => ν i + 1)) =
      (((ν a + 1 : ℕ) : ℚ)) • hw ℚ le_rfl (fun i => ν i + 1) := by
    intro a
    ext m
    rw [lgraded_coeff_euler, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : coeff m (hw ℚ le_rfl (fun i : Fin N => ν i + 1)) = 0
    · simp [hm]
    · have hW := hwRowWeight ℚ N N le_rfl _ hν' hm
      have hWa := congrFun hW a
      have hr : rowNu (r := N) (fun i : Fin N => ν i + 1) a = ν a + 1 := by
        simp [rowNu]
      rw [hr] at hWa
      congr 1
      rw [← hWa]
      norm_cast
      simp [Finsupp.weight_apply, Finsupp.sum, lgraded_wa, rowW, Pi.single_apply, eq_comm]
  have hcap := Formalism.CohomologicalDescent.HeightDescentMinors.c2_holds_alt ℚ (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
    (MvPolynomial (Fin N × Fin N) ℚ) N (polE N) ((N : ℚ) - 1) (fun i => ((ν i + 1 : ℕ) : ℚ))
    (hw ℚ le_rfl (fun i => ν i + 1))
    (fun i j hij => by
      rw [Module.End.smul_def, hPol]
      exact hwRaise ℚ N N le_rfl _ i j 1 hij le_rfl)
    (fun i => by rw [Module.End.smul_def, hPol, heul])
  rw [← hDD N, Module.End.smul_def, Module.End.mul_apply, LinearMap.mulLeft_apply] at hcap
  have hdet0 : detX N ≠ 0 := by
    intro h0
    have h1 := hHw N (fun _ => 0) (fun _ _ _ => le_rfl)
    rw [h0, zero_mul] at h1
    exact hwNe ℚ N N le_rfl _ h1
  have hD : detD N (detX N * hw ℚ le_rfl ν) =
      (∏ i : Fin N, ((N : ℚ) - 1 + ((ν i + 1 : ℕ) : ℚ) - ((i : ℕ) : ℚ))) • hw ℚ le_rfl ν := by
    apply mul_left_cancel₀ hdet0
    rw [← hG', hcap, hG', mul_smul_comm]
  rw [hAdj N (hw ℚ le_rfl ν) (detX N * hw ℚ le_rfl ν), hD, fockQ_smul_right]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ ν i + N := by omega
  rw [Nat.cast_sub hi]
  push_cast
  ring
end PI.HookSteps
