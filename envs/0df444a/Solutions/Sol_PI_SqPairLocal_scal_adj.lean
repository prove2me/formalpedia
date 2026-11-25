-- Prove2me | solution 1 for PI.SqPairLocal.scal_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:05.111158+00:00
-- url     : https://prove2.me/submissions/e73a6de6-be24-472c-982f-09c478b659d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SplitPlaceOf

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
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (ε : 𝓞 E) :
    (ε : E) • (1 : Matrix (Fin N) (Fin N) E) + ((ε : E) • (1 : Matrix (Fin N) (Fin N) E))ᴴ - 1 =
      ((ε + cj E ε - 1 : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E) := by
  have hc0 : ((cj E ε : 𝓞 E) : E) = star (ε : E) := rfl
  have hc : ((ε + cj E ε - 1 : 𝓞 E) : E) = (ε : E) + star (ε : E) - 1 := by
    push_cast
    exact congrArg (fun z => (ε : E) + z - 1) hc0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hc, sub_smul, add_smul, one_smul]
end PI.SqPairLocal
