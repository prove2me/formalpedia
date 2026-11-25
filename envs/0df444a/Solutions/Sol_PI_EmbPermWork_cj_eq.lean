-- Prove2me | solution 1 for PI.EmbPermWork.cj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:15.828116+00:00
-- url     : https://prove2.me/submissions/65c89c8a-5fc0-4207-adf2-6ed249f9ee25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_EmbPerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingPermutations_CjEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EmbPermWork
namespace PI.EmbPermWork
theorem _root_.solution (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) (hx : x ∈ M) :
    PI.EmbPermDefs.cj M ρ x = ρ ⟨x, hx⟩ := by
  simp only [PI.EmbPermDefs.cj, PI.EmbPermDefs.liftM, dif_pos hx]
end PI.EmbPermWork
