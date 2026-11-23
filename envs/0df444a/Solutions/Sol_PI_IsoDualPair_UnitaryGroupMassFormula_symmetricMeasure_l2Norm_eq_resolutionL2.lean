-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.symmetricMeasure_l2Norm_eq_resolutionL2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:28.037253+00:00
-- url     : https://prove2.me/submissions/d5ef9caa-7958-40b4-bedd-ec0bba2e27b3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.IsoDualPair PI.IsoDualPair.UnitaryGroupMassFormula
open PI.IsoDualPair
variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoDualPair.UnitaryGroupMassFormula
theorem _root_.solution (φ : LaC N nu) : l2 φ = ∑ J, ‖φ J‖ ^ 2 := finsum_eq_sum_of_fintype _
end PI.IsoDualPair.UnitaryGroupMassFormula
