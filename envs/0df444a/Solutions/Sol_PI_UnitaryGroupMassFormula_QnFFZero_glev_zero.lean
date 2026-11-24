-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QnFFZero.glev_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:54:03.9278+00:00
-- url     : https://prove2.me/submissions/409f2b85-2f3a-48af-bf5e-6be3af484988

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
theorem _root_.solution (k r : ℕ) (g : Mx k r) : g ∈ Glev k r 0 ↔ g ∈ UH (Hpk k r) := by
  simp only [Glev, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, fun a ha => absurd ha (by simp)⟩
end PI.UnitaryGroupMassFormula.QnFFZero
