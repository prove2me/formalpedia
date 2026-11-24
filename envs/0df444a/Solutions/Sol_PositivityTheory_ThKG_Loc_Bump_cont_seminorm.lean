-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.cont_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:43.053185+00:00
-- url     : https://prove2.me/submissions/97dea37c-6e1a-4c95-853f-818d194f71f0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal
variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (k n : ℕ) : Continuous (SchwartzMap.seminorm ℂ k n : 𝓢(V, ℂ) → ℝ) :=
  (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)
end PositivityTheory.ThKG.Loc.Bump
