-- Prove2me | solution 1 for PI.WMI.MMap.coeff_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:37.423553+00:00
-- url     : https://prove2.me/submissions/d000b950-9319-402d-9d58-850d65c3c50c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Theorems.Thm_PI_WMI_MMap_aeval_scale_monomial
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



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
open PI.WMI.MMap
namespace PI.WMI.MMap
theorem _root_.solution {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (aeval (fun v : σ => C (w v) * X v) f) = coeff m f * ∏ v, w v ^ m v := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]
end PI.WMI.MMap
