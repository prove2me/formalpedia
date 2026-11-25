-- Prove2me | solution 1 for PI.Dv.IdxW.comap_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:38.296351+00:00
-- url     : https://prove2.me/submissions/19492d4e-e906-4335-8783-01ba194e1faa

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
theorem _root_.solution (I : Ideal R) (M : Submodule R V) :
    (I • M).comap M.subtype = I • (⊤ : Submodule R M) := by
  have e := Submodule.map_smul'' I (⊤ : Submodule R M) M.subtype
  rw [Submodule.map_subtype_top] at e
  rw [← e, Submodule.comap_map_eq_of_injective M.injective_subtype]
end PI.Dv.IdxW
