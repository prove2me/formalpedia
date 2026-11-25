-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.dot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:47.842275+00:00
-- url     : https://prove2.me/submissions/94e7cc70-03a3-4fd1-9110-43e7115af3c3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution {n : ℕ} (w v : Fin n → ℂ) : ‖star w ⬝ᵥ v‖ ≤ eN w * eN v := by
  have e : star w ⬝ᵥ v =
      inner ℂ (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v) := by
    simp [PiLp.inner_apply, dotProduct, RCLike.inner_apply, mul_comm]
  rw [e]
  exact norm_inner_le_norm _ _
end PI.PolynomialProperness.CoreW
