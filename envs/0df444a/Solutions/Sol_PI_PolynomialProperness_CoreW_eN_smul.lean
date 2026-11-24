-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.eN_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:21.252572+00:00
-- url     : https://prove2.me/submissions/d91feb08-7195-4acd-a27b-ffa2fca6f46c

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
theorem _root_.solution {n : ℕ} (c : ℂ) (x : Fin n → ℂ) : eN (c • x) = ‖c‖ * eN x := by
  simp only [eN, WithLp.toLp_smul]
  exact norm_smul _ _
end PI.PolynomialProperness.CoreW
