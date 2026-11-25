-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.inUJ_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:19.402799+00:00
-- url     : https://prove2.me/submissions/5d3a0e6f-c9a3-4d58-9a8b-9f7504f8683b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Amat_mulVec
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_A
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_inUJ_of_hJ

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
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Formalism.REAL.inUJ ε (Amat ε e f s) := inUJ_of_hJ _ (fun x y => by rw [Amat_mulVec, Amat_mulVec]; exact hJ_A hG s hs x y)
end PI.NMeasInv.UnitaryGroupMassFormula
