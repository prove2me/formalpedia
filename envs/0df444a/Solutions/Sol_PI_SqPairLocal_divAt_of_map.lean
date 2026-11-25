-- Prove2me | solution 1 for PI.SqPairLocal.divAt_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:17.387812+00:00
-- url     : https://prove2.me/submissions/168ef187-1c72-4d4d-836f-07b1baaaf3c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero

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
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {Q : Ideal (𝓞 E)} {N : ℕ} (A : Matrix (Fin N) (Fin N) (𝓞 E)) (c : 𝓞 E)
    (h : ∀ a b, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * A a b = c * w) (a b : Fin N) :
    DivAt Q c ((algebraMap (𝓞 E) E).mapMatrix A a b) := by
  obtain ⟨s, hs, w, hw⟩ := h a b
  refine ⟨s, hs, w, ?_⟩
  have h2 := congrArg (algebraMap (𝓞 E) E) hw
  rw [map_mul, map_mul] at h2
  exact h2
end PI.SqPairLocal
