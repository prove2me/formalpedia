-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:16:43.560242+00:00
-- url     : https://prove2.me/submissions/203c81ab-3c03-47ae-9f9c-114734c8ca50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution (ϖ : R) (hϖ : σ ϖ = ϖ) (m a k : ℕ) (hk : m + a = k) :
    σ (ϖ ^ m) * (ϖ ^ m * ϖ ^ (2 * a)) = ϖ ^ (2 * k) := by
  rw [map_pow, hϖ, ← hk]
  ring
end PI.SqPair.LocCartanPairW
