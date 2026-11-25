-- Prove2me | solution 1 for PI.FockOneDegW.harmonic_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:20.57421+00:00
-- url     : https://prove2.me/submissions/706034de-c6b3-4972-b25e-05c40a68c163

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Theorems.Thm_PI_FockOneDegW_harmIff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
open PI.FockOneDegW.RedOps
namespace PI.FockOneDegW
theorem _root_.solution : HarmSub := by
  intro p q r s
  refine ⟨?_, ?_, ?_⟩
  · rw [harmIff]; intro c d _; exact map_zero _
  · intro P Q hP hQ
    rw [harmIff] at hP hQ ⊢
    intro c d hcd
    rw [map_add, hP c d hcd, hQ c d hcd, add_zero]
  · intro k P hP
    rw [harmIff] at hP ⊢
    intro c d hcd
    rw [map_smul, hP c d hcd, smul_zero]
end PI.FockOneDegW
