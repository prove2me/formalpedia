-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.sgn_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:33.082466+00:00
-- url     : https://prove2.me/submissions/d2fb6c4f-207e-4e80-9c58-b38744d51f3b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn; split_ifs <;> norm_num
end PI.UnitaryGroupMassFormula.FibOrbAsmW
