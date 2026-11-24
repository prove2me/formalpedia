-- Prove2me | solution 1 for PIQnLT.isUnit_det_of_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:24:19.672673+00:00
-- url     : https://prove2.me/submissions/9d2a93bb-c4bd-4728-92ce-e62d1bf6306a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


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
theorem _root_.solution (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r')) :
    IsUnit g.det := by
  obtain ⟨_, hI, -⟩ := hpkFacts k r'
  have hU : gᴴ * Hpk k r' * g = Hpk k r' := hg
  exact Matrix.isUnit_det_of_left_inverse (B := Hpk k r' * gᴴ * Hpk k r') (by
    rw [Matrix.mul_assoc (Hpk k r' * gᴴ), Matrix.mul_assoc (Hpk k r'), ← Matrix.mul_assoc gᴴ, hU, hI])
end PIQnLT
