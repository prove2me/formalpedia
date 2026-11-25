-- Prove2me | solution 1 for PI.WHw.stable_subspace_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:17:15.817592+00:00
-- url     : https://prove2.me/submissions/e7ac3b8c-f846-4d42-b9f0-0753b8bd378b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Theorems.Thm_PI_WHw_coeff_mem_of_eval
import Theorems.Thm_PI_WHw_eval_rowGen
import Theorems.Thm_PI_WHw_det_one_add_single_ne
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
private theorem transpose_one_add_single {N : ℕ} (a b : Fin N) (c : ℂ) :
    (1 + Matrix.single a b c).transpose = 1 + Matrix.single b a c := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, ite_and]
  split_ifs <;> subst_vars <;> simp_all
end PI.WHw
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WHw
theorem _root_.solution : StableClosedC := by
  intro N lam U _hU hstab a b k f hf
  show (rowGen ℂ a b f).coeff k ∈ U
  apply coeff_mem_of_eval U (rowGen ℂ a b f) _ k
  intro m
  rw [eval_rowGen]
  have hu : IsUnit (1 + Matrix.single a b (m : ℂ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_one_add_single_ne a b m))
  have hg := hstab hu.unit f hf
  unfold Formalism.BasicNotions.sqAct at hg
  rw [hu.unit_spec, transpose_one_add_single] at hg
  have hc : Formalism.BasicNotions.detPow ℂ N hu.unit lam.detShift ≠ 0 := by
    unfold Formalism.BasicNotions.detPow
    exact Units.ne_zero _
  have h2 := U.smul_mem (Formalism.BasicNotions.detPow ℂ N hu.unit lam.detShift)⁻¹ hg
  rwa [inv_smul_smul₀ hc] at h2
end PI.WHw
