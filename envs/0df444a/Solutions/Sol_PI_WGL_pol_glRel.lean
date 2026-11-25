-- Prove2me | solution 1 for PI.WGL.pol_glRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:07.701969+00:00
-- url     : https://prove2.me/submissions/7fefbae1-1ad1-41da-920f-de7baac3ee55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Theorems.Thm_PI_WGL_pol_eq_Eg
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_REAL_canonicalCommutation_holds
import Theorems.Thm_Formalism_REAL_fockPairGl_of
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
namespace PI.WGL
theorem _root_.solution (r m : ℕ) : Formalism.REAL.GlRel (fun a b : Fin r => (pol ℂ (m := m) a b : Module.End ℂ _)) := by
  have h := (Formalism.REAL.fockPairGl_of Formalism.REAL.canonicalCommutation_holds r m (fun _ => true) (fun _ => true)).1
  intro a b c d
  simp only [pol_eq_Eg]
  exact h a b c d
end PI.WGL
