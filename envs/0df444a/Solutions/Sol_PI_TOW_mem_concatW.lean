-- Prove2me | solution 1 for PI.TOW.mem_concatW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:12.983842+00:00
-- url     : https://prove2.me/submissions/daf96fa6-88b1-43f9-a506-3ad9aa88dc85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
namespace PI.TOW
theorem _root_.solution {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) (z : Fin n' × (Fin k × Fin k)) :
    z ∈ concatW w ↔ z.2 ∈ w z.1 := by
  simp only [concatW, liftW, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨t, y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨z.1, z.2, h, rfl⟩
end PI.TOW
