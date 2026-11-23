-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.mapX_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:09.874973+00:00
-- url     : https://prove2.me/submissions/25cb201d-20b6-46d4-8c81-280ac80f7458

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
    (MvPolynomial.eval (ent g)).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ) =
      (g : Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.mvPolynomialX_mapMatrix_eval (g : Matrix (Fin N) (Fin N) ℂ)
end PI.UnitaryGroupMassFormula.PolyCoef
