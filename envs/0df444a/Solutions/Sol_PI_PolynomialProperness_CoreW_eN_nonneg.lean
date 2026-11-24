-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.eN_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:17:10.737604+00:00
-- url     : https://prove2.me/submissions/e18230d3-bf71-4152-8dbd-3931c4ec5d0c

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
theorem _root_.solution {n : ℕ} (x : Fin n → ℂ) : 0 ≤ eN x := norm_nonneg _
end PI.PolynomialProperness.CoreW
