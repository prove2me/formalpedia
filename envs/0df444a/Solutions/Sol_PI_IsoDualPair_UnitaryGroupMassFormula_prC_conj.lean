-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.prC_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:30.668044+00:00
-- url     : https://prove2.me/submissions/e65f33bd-f09d-4d20-a6ec-8dd5517bf4f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_symmetricMeasure_l2Norm_eq_resolutionL2

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
theorem _root_.solution (φ : LaC N nu) : prC φ (fun J => conj (φ J)) = (l2 φ : ℂ) := by
  rw [prC_eq, symmetricMeasure_l2Norm_eq_resolutionL2, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
end PI.IsoDualPair.UnitaryGroupMassFormula
