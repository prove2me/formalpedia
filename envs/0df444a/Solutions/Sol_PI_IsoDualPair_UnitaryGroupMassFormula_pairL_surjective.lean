-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.pairL_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:28.110404+00:00
-- url     : https://prove2.me/submissions/3e920e63-b261-4eac-b722-f93826283238

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_pairL_injective

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
theorem _root_.solution : Function.Surjective (pairL (N := N) (nu := nu)) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 pairL_injective
end PI.IsoDualPair.UnitaryGroupMassFormula
