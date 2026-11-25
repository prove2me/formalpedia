-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.sig_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:39.168794+00:00
-- url     : https://prove2.me/submissions/5d8b72b5-1298-4247-94a2-94c19660716b

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by
  have hi := i.isLt
  unfold sig
  split_ifs <;> first | rfl | (ext; simp only at *; omega)
end PI.UnitaryGroupMassFormula.FibOrbAsmW
