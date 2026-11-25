-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.ne_bot_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:04.866815+00:00
-- url     : https://prove2.me/submissions/140a5b9d-3eb5-4ebc-bb45-6a799cf41970

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {F : IntermediateField ℚ ℂ} {S T : Submodule (𝓞 F) ℂ} {c : ℂ} (hc : c ≠ 0)
    (hST : span (𝓞 F) {c} * S ≤ T) (hS : S ≠ ⊥) : T ≠ ⊥ := by
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  intro hT
  have hmem : c * x ∈ span (𝓞 F) {c} * S :=
    Submodule.mul_mem_mul (Submodule.mem_span_singleton_self c) hxS
  have h2 := hST hmem
  rw [hT, Submodule.mem_bot] at h2
  exact mul_ne_zero hc hx0 h2
end PI.UnitaryGroupMassFormula.UnitDetRoot
