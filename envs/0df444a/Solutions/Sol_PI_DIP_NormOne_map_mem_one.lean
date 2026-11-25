-- Prove2me | solution 1 for PI.DIP.NormOne.map_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:58.472711+00:00
-- url     : https://prove2.me/submissions/b8b5c76e-7d33-4aea-b575-c7529df5508e

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
theorem _root_.solution (c : E →+* E) : ∀ x ∈ (1 : Submodule (𝓞 E) E), c x ∈ (1 : Submodule (𝓞 E) E) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨σ c y, rfl⟩
end PI.DIP.NormOne
