-- Prove2me | solution 1 for PI.UnitKronW.eq_zero_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:49.249846+00:00
-- url     : https://prove2.me/submissions/42f4a7da-15c0-41f3-a6aa-6a5f782df147

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_EqZeroOfMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder
namespace PI.UnitKronW
theorem _root_.solution {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ) (h : ∀ x, N *ᵥ x = 0) : N = 0 := by
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by simp [Matrix.toLin'_apply, h])
end PI.UnitKronW
