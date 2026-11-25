-- Prove2me | solution 1 for PI.WGL.EqvWt.prod_rowDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:17.06743+00:00
-- url     : https://prove2.me/submissions/019df8aa-b615-46ba-9791-f319385a9baf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {r c : ℕ} (x : Fin r → ℂ) (m : Fin r × Fin c →₀ ℕ) :
    (m.prod fun v k => x v.1 ^ k) = ∏ a, x a ^ rowDeg m a := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  unfold rowDeg
  show ∏ y : Fin c, x a ^ m (a, y) = x a ^ ∑ s, m (a, s)
  rw [Finset.prod_pow_eq_pow_sum]
end PI.WGL.EqvWt
