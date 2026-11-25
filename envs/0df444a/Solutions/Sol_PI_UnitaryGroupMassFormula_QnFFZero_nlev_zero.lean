-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QnFFZero.nlev_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:14.134708+00:00
-- url     : https://prove2.me/submissions/9d3833da-bee6-446c-a72b-a5bcfdedbd55

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelGeneralLinear_GlevZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_glev_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_nset_uh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QnFFZero
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.QnFFZero
theorem _root_.solution (k r : ℕ) (n : Mx k r) : n ∈ Nlev k r 0 ↔ n ∈ Nset k r := by
  simp only [Nlev, Set.mem_inter_iff]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, (glev_zero k r n).2 (nset_uh k r n h)⟩
end PI.UnitaryGroupMassFormula.QnFFZero
