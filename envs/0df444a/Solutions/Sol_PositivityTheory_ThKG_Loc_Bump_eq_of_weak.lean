-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.eq_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:17.874695+00:00
-- url     : https://prove2.me/submissions/02246465-5cc1-4e98-912d-540059fd2f68

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
theorem _root_.solution {f g : 𝓢(V, ℂ)} (h : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, T f = T g) : f = g :=
  SchwartzMap.ext fun x => h (evAt x)
end PositivityTheory.ThKG.Loc.Bump
