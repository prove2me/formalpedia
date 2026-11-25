-- Prove2me | solution 1 for PI.WGL.BrInt.normFock_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:04.276799+00:00
-- url     : https://prove2.me/submissions/7f7a2349-107d-4ab1-bb5e-99006c91a800

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_PI_WGL_BrInt_brFockF_map
import Theorems.Thm_PI_WGL_BrInt_extremal_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (a b : MvPolynomial (Fin N × Fin N) ℚ) :
    normFock lam (map (algebraMap ℚ ℂ) a) (map (algebraMap ℚ ℂ) b) = ((normFockQ lam a b : ℚ) : ℂ) := by
  unfold normFock normFockQ
  rw [brFockF_map, extremal_map, brFockF_map]
  exact (Rat.cast_div _ _).symm
end PI.WGL.BrInt
