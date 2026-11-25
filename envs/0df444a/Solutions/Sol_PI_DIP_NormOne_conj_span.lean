-- Prove2me | solution 1 for PI.DIP.NormOne.conj_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:51.850751+00:00
-- url     : https://prove2.me/submissions/5e3b6dc8-3b24-4ba6-9ec3-30e48f4f2158

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open PI PI.DIP PI.DIP.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace PI.DIP.NormOne
theorem _root_.solution (c : E →+* E) (hc : ∀ x, c (c x) = x) {B : Submodule (𝓞 E) E} (a : E)
    (hB : ∀ x, x ∈ B ↔ c x ∈ Submodule.span (𝓞 E) {a}) :
    B = Submodule.span (𝓞 E) {c a} := by
  ext x
  rw [hB, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨σ c r, ?_⟩
    rw [Algebra.smul_def] at hr ⊢
    have := congrArg c hr
    rw [hc, map_mul] at this
    rw [← this]
    rfl
  · rintro ⟨r, rfl⟩
    refine ⟨σ c r, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
    rfl
end PI.DIP.NormOne
