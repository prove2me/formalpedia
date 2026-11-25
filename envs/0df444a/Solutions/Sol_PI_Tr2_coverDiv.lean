-- Prove2me | solution 1 for PI.Tr2.coverDiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:30.988218+00:00
-- url     : https://prove2.me/submissions/aa26c02b-550c-4bec-a9c8-61679f9ea95f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_TransferenceCoverRad
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceCover
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CoveringRadius_CoverRad
import Theorems.Thm_transference_covering


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open PI PI.Tr2
namespace PI.Tr2
theorem _root_.solution : PI.TransferenceCoverDiv := by
  intro V _ _ _ M hd hspan κ hκ hdual x
  haveI := hd
  haveI : IsZLattice ℝ M := ⟨hspan⟩
  obtain ⟨l, hl, hle⟩ := transference_covering V M κ hκ (fun y hy0 hy => hdual y hy hy0) x
  refine ⟨l, hl, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  linarith
end PI.Tr2
