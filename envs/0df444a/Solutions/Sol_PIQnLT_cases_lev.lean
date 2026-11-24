-- Prove2me | solution 1 for PIQnLT.cases_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:19.578405+00:00
-- url     : https://prove2.me/submissions/78e14b66-3dfb-4a47-bf52-cdf07f48c8ce

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose

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
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
namespace PIQnLT
theorem _root_.solution (p : Fin (2 * (i + r') + k + 1)) :
    (∃ p', p = levPos k i r' p') ∨ ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) := by
  by_cases h : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · left
    exact ⟨⟨p.val - i, by omega⟩, Fin.ext (by simp [levPos]; omega)⟩
  · right
    exact h
end PIQnLT
