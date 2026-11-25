-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.isInt_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:10.830868+00:00
-- url     : https://prove2.me/submissions/2d00e3bf-7d9a-4f63-abc0-473f5d9c5230

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_IsIntIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution [StarRing K] {x : K} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  h.map (starRingEnd K).toIntAlgHom
end PI.UnitaryGroupMassFormula.CntFormula
