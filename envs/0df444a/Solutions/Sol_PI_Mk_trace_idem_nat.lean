-- Prove2me | solution 1 for PI.Mk.trace_idem_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:19.126328+00:00
-- url     : https://prove2.me/submissions/6d58520a-55a7-4465-9663-4dd5277cea51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Matrix Finset
namespace PI.Mk
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (E : Matrix n n ℚ) (hE : E * E = E) :
    ∃ r : ℕ, E.trace = (r : ℚ) := by
  have hf : IsIdempotentElem (Matrix.toLin' E) := by
    change Matrix.toLin' E ∘ₗ Matrix.toLin' E = Matrix.toLin' E
    rw [← Matrix.toLin'_mul, hE]
  refine ⟨Module.finrank ℚ (LinearMap.range (Matrix.toLin' E)), ?_⟩
  rw [← Matrix.trace_toLin'_eq]
  exact (LinearMap.IsIdempotentElem.isProj_range _ hf).trace
end PI.Mk
