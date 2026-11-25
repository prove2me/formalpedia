-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.Amat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:43.560535+00:00
-- url     : https://prove2.me/submissions/57bcf053-25a8-4923-9270-9eb3ae182a97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Alin_apply

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
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (s : Fin r → ℝ) (v : Fin n → ℂ) : Amat ε e f s *ᵥ v = Afun ε e f s v := by
  unfold Amat
  rw [LinearMap.toMatrix'_mulVec, Alin_apply]
end PI.NMeasInv.UnitaryGroupMassFormula
