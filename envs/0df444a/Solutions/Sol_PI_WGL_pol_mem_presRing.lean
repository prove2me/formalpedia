-- Prove2me | solution 1 for PI.WGL.pol_mem_presRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:36.794246+00:00
-- url     : https://prove2.me/submissions/5edec5ed-b04d-41c5-a374-e1dff202f5e2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Lemmata_GeneralBFactRight_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliZ
import Theorems.Thm_PI_WGL_pol_map
import Theorems.Thm_PI_WGL_pol_mem_dualWeyl


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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    (pol ℂ (m := N) a b : Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) ∈ presRing lam := by
  intro f hf
  exact ⟨pol ℤ a b f, pol_mem_dualWeyl ℤ lam.natW a b f hf, pol_map _ a b f⟩
end PI.WGL
