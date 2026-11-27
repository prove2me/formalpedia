-- Prove2me | solution 1 for PI.SqPairLocal.StModel.notMem_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:15:37.692805+00:00
-- url     : https://prove2.me/submissions/ac0d4f84-768d-42c6-a1bf-f9029876852e

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
open PI.SqPairLocal.StModel
variable {Q : Ideal (𝓞 E)} (M : StModel E Q)
namespace PI.SqPairLocal.StModel
theorem _root_.solution {x : 𝓞 E} (hx : IsUnit (M.j x)) : x ∉ Q := by
  intro hxQ
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, z, hyz⟩ := M.dense (↑u⁻¹) 1
  have hdz : ∃ z' : M.R, M.j (1 - x * y) = M.j M.ϖ ^ 1 * z' := by
    refine ⟨M.j x * z, ?_⟩
    have h1 : M.j y = ↑u⁻¹ - M.j M.ϖ ^ 1 * z := by rw [← hyz]; ring
    rw [map_sub, map_one, map_mul, h1, ← hu, mul_sub, Units.mul_inv]
    ring
  obtain ⟨s, hs, w, hw⟩ := M.detect (1 - x * y) 1 hdz
  apply hs
  have hsw : s = s * x * y + M.ϖ ^ 1 * w := by linear_combination hw
  rw [hsw]
  refine Q.add_mem (Q.mul_mem_right _ (Q.mul_mem_left _ hxQ)) (Q.mul_mem_right _ ?_)
  rw [pow_one]; exact M.ϖ_Q
end PI.SqPairLocal.StModel
