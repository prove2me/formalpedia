-- Prove2me | solution 1 for P2M_PI_Dv_IdxW_ideal_localized__4df3c3d4c027
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:53.973046+00:00
-- url     : https://prove2.me/submissions/5ee27000-4f86-4642-a126-f1288643b1d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
namespace PI.Dv.IdxW
theorem _root_.solution (S : Submonoid R) (I : Ideal R) :
    I.localized' (Localization S) S (Algebra.linearMap R (Localization S)) =
      I.map (algebraMap R (Localization S)) := by
  exact Ideal.localized'_eq_map (Localization S) S I
end PI.Dv.IdxW
