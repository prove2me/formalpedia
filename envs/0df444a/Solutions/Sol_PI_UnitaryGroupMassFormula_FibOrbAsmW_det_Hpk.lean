-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.det_Hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:51.405388+00:00
-- url     : https://prove2.me/submissions/b5447c97-a4cc-45cc-b810-1002b7ac8adc

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_Hpk_mul_self

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FibOrbAsmW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
namespace PI.UnitaryGroupMassFormula.FibOrbAsmW
theorem _root_.solution (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := congrArg Matrix.det (Hpk_mul_self k r)
  rw [det_mul, det_one] at h
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h
end PI.UnitaryGroupMassFormula.FibOrbAsmW
