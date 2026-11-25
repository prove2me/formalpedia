-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.IsPD.conjEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:31.221546+00:00
-- url     : https://prove2.me/submissions/59b09b78-3da7-4db1-b470-be9a82370692

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_mapX_eval
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_adjugate_eq

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
namespace IsPD
theorem _root_.solution {N : ℕ} (i j : Fin N) :
    IsPD (fun g : UG N => star ((g : Matrix (Fin N) (Fin N) ℂ) i j)) := by
  refine ⟨1, (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate j i, fun g => ?_⟩
  have h : MvPolynomial.eval (ent g) ((Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate j i) =
      ((MvPolynomial.eval (ent g)).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate) j i := rfl
  rw [h, RingHom.map_adjugate, mapX_eval, adjugate_eq]
  show star ((g : Matrix (Fin N) (Fin N) ℂ) i j) * (g : Matrix (Fin N) (Fin N) ℂ).det ^ 1 = _
  simp [Matrix.star_apply, mul_comm]
end IsPD
end PI.UnitaryGroupMassFormula.PolyCoef
