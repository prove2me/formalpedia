-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:51:08.240067+00:00
-- url     : https://prove2.me/submissions/2ed55d72-97ba-410b-9d40-c5277e5b06b7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {e : ℝ} {f : B.Mat k r → ℂ} (h : PG e f) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ w : List (Bool × B.Mat k r), (∀ x ∈ w, B.unitLie k r x.2) → w.length ≤ n →
      ∀ g ∈ B.GV k r, ‖Dw w f g‖ ≤ C * B.gN g ^ e := by
  obtain ⟨C, hC⟩ := h.2 n
  refine ⟨max C 0, le_max_right _ _, fun w hw hl g hg => (hC w hw hl g hg).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (by unfold B.gN; positivity) _)
end PI.UnitaryCorollaryDerivatives
