-- Prove2me | solution 1 for PI.KerIso.FourSqW.qmap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:14.062399+00:00
-- url     : https://prove2.me/submissions/f84f6206-7140-4c7f-9b58-c124dbc52c5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerIso PI.KerIso.FourSqW
open PI.KerFourSqW
namespace PI.KerIso.FourSqW
theorem _root_.solution {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → E) (w : Fin 4 × n) :
    qmap b Q x w = ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2 := rfl
end PI.KerIso.FourSqW
