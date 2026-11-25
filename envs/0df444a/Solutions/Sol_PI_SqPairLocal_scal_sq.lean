-- Prove2me | solution 1 for PI.SqPairLocal.scal_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:23:54.990408+00:00
-- url     : https://prove2.me/submissions/d8ce3c41-fe99-48d1-a090-b5b0a0122ff2

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
    (ε : E) • (1 : Matrix (Fin N) (Fin N) E) * (ε : E) • 1 - (ε : E) • 1 =
      ((ε * (ε - 1) : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring
end PI.SqPairLocal
