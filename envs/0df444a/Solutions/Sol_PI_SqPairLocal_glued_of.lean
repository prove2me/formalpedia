-- Prove2me | solution 1 for PI.SqPairLocal.glued_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:55.42892+00:00
-- url     : https://prove2.me/submissions/eb1d388f-5b0d-49f7-8eb2-bd389afa8094

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps

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
namespace PI.SqPairLocal
theorem _root_.solution (hG : Glue) (hS : SplitPlace) (hI : InertPlace) : Glued := by
  apply hG
  intro E _ _ _ hE N L' L'' hN h' h'' Q hQ c hc
  by_cases hq : Q.comap (cj E) = Q
  · obtain ⟨e, h1, h2, h3⟩ := hI E hE N L' L'' hN h' h'' Q hQ hq c hc
    refine ⟨e, h1, h2, h3, ?_⟩
    rw [hq]
    exact h3
  · exact hS E hE N L' L'' hN h' h'' Q hQ hq c hc
end PI.SqPairLocal
