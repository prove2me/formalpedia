-- Prove2me | solution 1 for PI.WGL.pol_mem_dualWeyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:05.64673+00:00
-- url     : https://prove2.me/submissions/f08a678d-49b3-47e2-bfcf-36efcfe2d19f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Theorems.Thm_PI_WGL_pol_eq_rowDiv
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleRowDividedPowerStable


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
theorem _root_.solution (R : Type) [CommRing R] {r m : ℕ} (ν : Fin m → ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) (hf : f ∈ dualWeyl R r m ν) : pol R a b f ∈ dualWeyl R r m ν := by
  rw [pol_eq_rowDiv]; exact dualWeylModuleRowDividedPowerStable R r m ν a b 1 f hf
end PI.WGL
