-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.Hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:22.590611+00:00
-- url     : https://prove2.me/submissions/d5a78fe6-a7d0-4bbd-9124-dcf1b66ac35c

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
theorem _root_.solution (k r : ℕ) (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l = sig k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  simp only [Hpk, sig, sgn, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | (simp_all; omega)
end PI.UnitaryGroupMassFormula.FibOrbAsmW
