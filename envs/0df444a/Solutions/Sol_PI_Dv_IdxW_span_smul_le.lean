-- Prove2me | solution 1 for PI.Dv.IdxW.span_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:04.10504+00:00
-- url     : https://prove2.me/submissions/a020c7ac-c273-4d1e-94c5-5a32e1ac1ec4

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
theorem _root_.solution (c : R) (M N : Submodule R V) (h : ∀ x ∈ M, c • x ∈ N) :
    Ideal.span {c} • M ≤ N := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [mul_smul]
  exact N.smul_mem a (h x hx)
end PI.Dv.IdxW
