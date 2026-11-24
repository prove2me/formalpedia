-- Prove2me | solution 1 for PI.PolynomialProperness.CB.det_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:18.947802+00:00
-- url     : https://prove2.me/submissions/a6b90408-b010-425b-9eaa-a059b84e0d22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) {c : ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ c) : ‖A.det‖ ≤ (Fintype.card ι).factorial * c ^ Fintype.card ι := by
  have h' : ∀ i j, NormedField.toAbsoluteValue ℂ (A i j) ≤ c := h
  have := Matrix.det_le h'
  rw [nsmul_eq_mul] at this
  exact this
end PI.PolynomialProperness.CB
