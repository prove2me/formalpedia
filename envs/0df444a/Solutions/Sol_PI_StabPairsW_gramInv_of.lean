-- Prove2me | solution 1 for PI.StabPairsW.gramInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:19.499901+00:00
-- url     : https://prove2.me/submissions/f16f3b8e-ea42-4709-91e0-7fe8c2003143

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward

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
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (h : GramIndependentSignature) : GramInv := by
  intro k r z z' γ hs hp
  obtain ⟨-, ⟨Q, -, hQG⟩, -, -⟩ := h k r z z' γ hs hp
  have hdet := congrArg Matrix.det hQG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg,
    Matrix.det_one] at hdet
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero, zero_mul] at hdet
  exact absurd hdet.symm (by simp)
end PI.StabPairsW
