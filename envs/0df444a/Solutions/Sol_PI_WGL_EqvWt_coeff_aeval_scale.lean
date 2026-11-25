-- Prove2me | solution 1 for PI.WGL.EqvWt.coeff_aeval_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:08:30.203878+00:00
-- url     : https://prove2.me/submissions/8bcd8ec7-a8e9-43d9-8f0b-d0b940036d2d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {σ : Type} (e : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (aeval (fun v => C (e v) * X v) f) = (m.prod fun v k => e v ^ k) * coeff m f := by
  classical
  refine MvPolynomial.induction_on' f (fun u a => ?_) (fun p q hp hq => ?_)
  · have key : aeval (fun v => C (e v) * X v) (monomial u a) =
        monomial u (a * u.prod fun v k => e v ^ k) := by
      rw [aeval_monomial, monomial_eq]
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
        MvPolynomial.algebraMap_eq]
      ring
    rw [key, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  · rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end PI.WGL.EqvWt
