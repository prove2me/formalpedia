-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScalDeg.polD_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:28.439846+00:00
-- url     : https://prove2.me/submissions/441d0d8f-a58f-430c-86f7-c9e17160ebb4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScalDeg
open MvPolynomial PI.ScalDeg
namespace PI.UnitaryGroupMassFormula.ScalDeg
theorem _root_.solution {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : polD s Q y' = aeval (gv s y') Q := rfl
end PI.UnitaryGroupMassFormula.ScalDeg
