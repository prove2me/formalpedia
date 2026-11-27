-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.absV_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:17:51.771927+00:00
-- url     : https://prove2.me/submissions/d05153d4-2da4-47d0-aa7c-046408b19a68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution {x : Fv F v} (hx : x ≠ 0) : absV v x ≠ 0 := (absV_pos v hx).ne'
end PI.UnitaryGroupMassFormula.LocJacTyp
