-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.cofinStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:38.889971+00:00
-- url     : https://prove2.me/submissions/7838c596-8059-4735-843f-b74583554a45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_cofin1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : CofinStep := by
  intro E _ _ V _ _ _ _ _ L N hL hN
  obtain ⟨y1, hy1, h1⟩ := cofin1 L N hL.fg hN.span_eq_top
  obtain ⟨y2, hy2, h2⟩ := cofin1 N L hN.fg hL.span_eq_top
  refine ⟨y1 * y2, mul_ne_zero hy1 hy2, fun v hv => ?_, fun v hv => ?_⟩
  · have h3 := N.smul_mem (y2 : 𝓞 E) (h1 v hv)
    rw [← mul_smul] at h3
    rwa [Int.cast_mul, mul_comm]
  · have h3 := L.smul_mem (y1 : 𝓞 E) (h2 v hv)
    rw [← mul_smul] at h3
    rwa [Int.cast_mul]
end PI.UnitaryGroupMassFormula.UJClassMass
