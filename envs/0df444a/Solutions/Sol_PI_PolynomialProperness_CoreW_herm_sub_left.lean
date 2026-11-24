-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:25.122562+00:00
-- url     : https://prove2.me/submissions/b34389d5-fb4c-4c25-86b3-f075fb1d251a

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
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution (v v' w : Fin n → ℂ) : herm H (v - v') w = herm H v w - herm H v' w := by
  simp [herm, Matrix.mulVec_sub, dotProduct_sub]
end PI.PolynomialProperness.CoreW
