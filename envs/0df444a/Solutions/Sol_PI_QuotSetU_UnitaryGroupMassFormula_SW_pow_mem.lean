-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:03.780351+00:00
-- url     : https://prove2.me/submissions/4a69ed85-9a26-47b7-a2aa-acda1da6ff8b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {D : Matrix (Fin m) (Fin m) ℂ → ℝ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (hG : IsMatGroup G) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G) (n : ℕ) : x ^ n ∈ G := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact hG.2.1
  | succ n ih =>
    rw [pow_succ]
    exact hG.2.2.1 _ ih _ hx
end PI.QuotSetU.UnitaryGroupMassFormula.SW
