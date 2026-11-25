-- Prove2me | solution 1 for PI.WGL.BrInt.fockF_ext_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:07:12.701916+00:00
-- url     : https://prove2.me/submissions/f7f24aef-4ea1-4201-a0ca-19a0855be69c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_PI_WGL_BrInt_brFockF_map
import Theorems.Thm_PI_WGL_BrInt_extremal_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe


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
open Formalism.BasicNotions MvPolynomial
open PI.WGL.BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
namespace PI.WGL.BrInt
theorem _root_.solution {N : ℕ} (lam : DomWeight N) :
    fockF (extremal ℂ N lam) (extremal ℂ N lam) ≠ 0 := by
  rw [extremal_map, brFockF_map]
  have hne : extremal ℚ N lam ≠ 0 := by
    unfold extremal
    exact hwNe ℚ N N le_rfl lam.natW
  have hpos := (fockQPos (Fin N × Fin N) (extremal ℚ N lam) (extremal ℚ N lam)).2 hne
  exact_mod_cast hpos.ne'
end PI.WGL.BrInt
