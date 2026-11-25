-- Prove2me | solution 1 for PI.SqPairLocal.divAt_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:49.599248+00:00
-- url     : https://prove2.me/submissions/9dc15181-134d-41bf-9bdd-d44aa5cf0bf3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]
namespace PI.SqPairLocal
theorem _root_.solution {c : 𝓞 E} {K : ℕ}
    (hK : ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w) {x : 𝓞 E} (hx : x ∈ Q ^ K) :
    DivAt Q c (x : E) := by
  unfold DivAt
  obtain ⟨s, hs, w, hw⟩ := hK x hx
  exact ⟨s, hs, w, by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hw⟩
end PI.SqPairLocal
