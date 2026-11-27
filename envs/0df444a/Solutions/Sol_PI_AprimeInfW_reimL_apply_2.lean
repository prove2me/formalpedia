-- Prove2me | solution 2 for PI.AprimeInfW.reimL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:31.290974+00:00
-- url     : https://prove2.me/submissions/9aca9611-31a0-42e0-9b0d-cff09b1e9701

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MpOfIsomProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix ComplexConjugate
namespace PI.AprimeInfW
theorem _root_.solution {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) : reimL Y = reim Y := rfl
end PI.AprimeInfW
