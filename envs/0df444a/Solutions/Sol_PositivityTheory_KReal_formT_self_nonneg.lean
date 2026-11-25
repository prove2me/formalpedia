-- Prove2me | solution 1 for PositivityTheory.KReal.formT_self_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:47.074464+00:00
-- url     : https://prove2.me/submissions/6cd436f9-482d-4815-b61e-18d9dda7ed76

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.KReal
theorem _root_.solution (a : (J → I) → V) : 0 ≤ (formT a a).re := by
  unfold PositivityTheory.KReal.formT
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun w _ => by
    have h := inner_self_nonneg (𝕜 := ℂ) (x := a w)
    rwa [RCLike.re_to_complex] at h
end PositivityTheory.KReal
