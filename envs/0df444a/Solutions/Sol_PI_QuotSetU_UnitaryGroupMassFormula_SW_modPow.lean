-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.modPow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:02.865902+00:00
-- url     : https://prove2.me/submissions/d1fd342b-eee8-4d54-a838-1d6468ae5b13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_modOne
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_pow_mem

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
theorem _root_.solution (hG : IsMatGroup G) (hD : ModProps G D) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G)
    (n : ℕ) : D (x ^ n) = D x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact modOne hG hD
  | succ n ih =>
    rw [pow_succ, pow_succ, hD.2.1 _ (pow_mem hG hx n) _ hx, ih]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
