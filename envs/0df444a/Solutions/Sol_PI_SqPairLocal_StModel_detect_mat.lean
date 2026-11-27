-- Prove2me | solution 1 for PI.SqPairLocal.StModel.detect_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:15:28.914878+00:00
-- url     : https://prove2.me/submissions/60cbf462-23f5-464f-be13-4f1fba1f564b

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
theorem _root_.solution {N : ℕ} (A : Matrix (Fin N) (Fin N) (𝓞 E)) (m : ℕ)
    (Y : Matrix (Fin N) (Fin N) M.R) (h : M.j.mapMatrix A = (M.j M.ϖ ^ m) • Y) (a b : Fin N) :
    ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * A a b = M.ϖ ^ m * w := by
  apply M.detect
  refine ⟨Y a b, ?_⟩
  have := congrFun (congrFun h a) b
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply] using this
end PI.SqPairLocal.StModel
