-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.eq_zero_of_l2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:45:34.794092+00:00
-- url     : https://prove2.me/submissions/27ba24dd-8397-4f03-b64a-02b493bac21d

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
theorem _root_.solution (φ : LaC N nu) (h : l2 φ = 0) : φ = 0 := by
  rw [symmetricMeasure_l2Norm_eq_resolutionL2] at h
  funext J
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun J _ => by positivity)).1 h J (Finset.mem_univ _)
  simpa using this
end PI.IsoDualPair.UnitaryGroupMassFormula
