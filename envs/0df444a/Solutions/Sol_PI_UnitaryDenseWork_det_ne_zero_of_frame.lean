-- Prove2me | solution 1 for PI.UnitaryDenseWork.det_ne_zero_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:18.533872+00:00
-- url     : https://prove2.me/submissions/4b4a6c40-44b9-474b-9f32-689346350bec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Derived

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UnitaryDenseWork
namespace PI.UnitaryDenseWork
theorem _root_.solution {n : ℕ} (G y : Matrix (Fin n) (Fin n) ℂ) (hy : yᴴ * G * y = 1) :
    y.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hy
  rw [det_mul, det_mul, det_one, h0, mul_zero] at this
  exact zero_ne_one this
end PI.UnitaryDenseWork
