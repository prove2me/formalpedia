-- Prove2me | solution 1 for PI.TOW.filter_concatW_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:00.219989+00:00
-- url     : https://prove2.me/submissions/a9bec447-3910-455c-9b90-64b5e57fb3bf

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
theorem _root_.solution {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) (t : Fin n') :
    ((concatW w).filter fun z => z.1 = t).length = (w t).length := by
  rw [← List.countP_eq_length_filter]
  simp only [concatW, liftW, List.countP_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_eq_single t]
  · simp [Function.comp_def]
  · intro b _ hb
    simp [Function.comp_def, hb]
  · simp
end PI.TOW
