-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:23.536742+00:00
-- url     : https://prove2.me/submissions/90291a6c-a782-4126-aa3e-c04d9c513b28

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
theorem _root_.solution (c : ℂ) (v w : Fin n → ℂ) : herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]
end PI.PolynomialProperness.CoreW
