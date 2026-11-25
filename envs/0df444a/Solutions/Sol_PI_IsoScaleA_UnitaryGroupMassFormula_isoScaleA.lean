-- Prove2me | solution 1 for PI.IsoScaleA.UnitaryGroupMassFormula.isoScaleA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:11.230809+00:00
-- url     : https://prove2.me/submissions/2edc2dc7-9b7f-460f-935d-38e8a6790e8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoScaleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryScaleCount_CardEqSumColLen
import Theorems.Thm_PI_IsoScaleA_UnitaryGroupMassFormula_PIJ_scale
import Theorems.Thm_PI_IsoScaleA_UnitaryGroupMassFormula_applyAt0_C_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoScaleA PI.IsoScaleA.UnitaryGroupMassFormula
open PI.IsoScaleA
namespace PI.IsoScaleA.UnitaryGroupMassFormula
theorem _root_.solution : IsoScaleA := by
  intro Lt T _ _ _ tp N N' nu c s Θ φ
  funext I
  simp only [AOp, Pi.smul_apply, smul_eq_mul, PIJ_scale, applyAt0_C_mul, mul_assoc]
  rw [mul_finsum]
end PI.IsoScaleA.UnitaryGroupMassFormula
