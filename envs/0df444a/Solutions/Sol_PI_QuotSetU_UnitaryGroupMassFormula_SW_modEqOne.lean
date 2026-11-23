-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.modEqOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:02.752874+00:00
-- url     : https://prove2.me/submissions/2fdea99e-6b56-4658-8b4e-761872491da3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_modOne

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
    (h1 : D x ≤ 1) (h2 : D x⁻¹ ≤ 1) : D x = 1 := by
  have hinv := (hG.2.2.2 x hx).1
  have hxx := (hG.2.2.2 x hx).2
  have hm := hD.2.1 x hx x⁻¹ hinv
  rw [hxx, modOne hG hD] at hm
  have h0 := hD.1 x hx
  have hle : D x * D x⁻¹ ≤ D x := by
    calc D x * D x⁻¹ ≤ D x * 1 := mul_le_mul_of_nonneg_left h2 h0.le
      _ = D x := mul_one _
  linarith
end PI.QuotSetU.UnitaryGroupMassFormula.SW
