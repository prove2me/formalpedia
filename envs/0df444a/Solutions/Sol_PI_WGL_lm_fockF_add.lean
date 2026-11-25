-- Prove2me | solution 1 for PI.WGL.lm_fockF_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:58.41279+00:00
-- url     : https://prove2.me/submissions/a759cb67-0ab4-42d1-beff-d08765dc3064

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
import Theorems.Thm_PI_WGL_lm_fockF_eq_sum

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
namespace PI.WGL
theorem _root_.solution {σ : Type*} (f1 f2 g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f1 + f2) g = Formalism.REAL.fockF f1 g + Formalism.REAL.fockF f2 g := by
  classical
  rw [lm_fockF_eq_sum (f1 + f2) g (f1.support ∪ f2.support) MvPolynomial.support_add,
    lm_fockF_eq_sum f1 g _ Finset.subset_union_left, lm_fockF_eq_sum f2 g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring
end PI.WGL
