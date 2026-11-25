-- Prove2me | solution 1 for PI.SqPairLocal.intAt_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:59.111915+00:00
-- url     : https://prove2.me/submissions/1db6b8d3-3687-4d74-8e15-c43ae5338a4f

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
theorem _root_.solution {c : 𝓞 E} (hc : (c : E) ≠ 0) {x : E} (hx : DivAt Q c x) :
    IntAt Q ((c : E)⁻¹ * x) := by
  unfold DivAt at hx
  unfold IntAt
  obtain ⟨s, hs, w, hw⟩ := hx
  refine ⟨s, hs, w, ?_⟩
  calc (s : E) * ((c : E)⁻¹ * x) = (c : E)⁻¹ * ((s : E) * x) := by ring
    _ = (w : E) := by rw [hw, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
end PI.SqPairLocal
