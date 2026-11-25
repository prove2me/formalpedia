-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.adjugate_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:18.036643+00:00
-- url     : https://prove2.me/submissions/7f9cdab0-faa4-4b8f-a254-934057a9b675

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.PolyCoef
theorem _root_.solution {N : ℕ} (g : UG N) :
    (g : Matrix (Fin N) (Fin N) ℂ).adjugate =
      (g : Matrix (Fin N) (Fin N) ℂ).det • star (g : Matrix (Fin N) (Fin N) ℂ) := by
  have h1 : star (g : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self g
  calc (g : Matrix (Fin N) (Fin N) ℂ).adjugate
      = (star (g : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ)) *
          (g : Matrix (Fin N) (Fin N) ℂ).adjugate := by rw [h1, Matrix.one_mul]
    _ = star (g : Matrix (Fin N) (Fin N) ℂ) * ((g : Matrix (Fin N) (Fin N) ℂ) *
          (g : Matrix (Fin N) (Fin N) ℂ).adjugate) := by rw [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
end PI.UnitaryGroupMassFormula.PolyCoef
