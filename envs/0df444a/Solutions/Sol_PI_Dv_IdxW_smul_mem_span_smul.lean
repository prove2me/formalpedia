-- Prove2me | solution 1 for PI.Dv.IdxW.smul_mem_span_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:35.521784+00:00
-- url     : https://prove2.me/submissions/129cfc6a-2b7d-488a-bb1a-1f167bd6fc9c

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
theorem _root_.solution (c : R) (M : Submodule R V) {x : V} (hx : x ∈ M) :
    c • x ∈ Ideal.span {c} • M := by
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) hx
end PI.Dv.IdxW
