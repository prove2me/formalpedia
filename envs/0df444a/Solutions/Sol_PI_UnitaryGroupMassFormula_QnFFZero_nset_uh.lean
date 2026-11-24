-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QnFFZero.nset_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:54:04.877038+00:00
-- url     : https://prove2.me/submissions/da7bfcfb-0dd9-4e08-bc73-eaae6319a56d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelGeneralLinear_GlevZero

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
theorem _root_.solution (k r : ℕ) (n : Mx k r) (h : n ∈ Nset k r) : n ∈ UH (Hpk k r) := by
  simp only [Nset, Set.mem_ofPred_eq] at h
  exact h.1
end PI.UnitaryGroupMassFormula.QnFFZero
