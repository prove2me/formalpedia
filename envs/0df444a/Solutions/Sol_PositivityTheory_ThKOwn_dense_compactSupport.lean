-- Prove2me | solution 1 for PositivityTheory.ThKOwn.dense_compactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:33.814486+00:00
-- url     : https://prove2.me/submissions/f2ebc4c9-0e96-47c4-9221-4cf88679d37b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_DenseC
import Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_dense_hasCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open scoped SchwartzMap
namespace PositivityTheory.ThKOwn
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    Dense {f : 𝓢(V, ℂ) | HasCompactSupport (f : V → ℂ)} := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFunL
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e.symm
  have hPQ : ∀ f, P (Q f) = f := fun f => by ext x; simp [P, Q]
  have hr : DenseRange P := Function.Surjective.denseRange fun f => ⟨Q f, hPQ f⟩
  refine (hr.dense_image P.continuous (GlobalTheory.CompanionTheory.DiracComb.dense_hasCompactSupport _)).mono ?_
  rintro _ ⟨f, hf, rfl⟩
  exact HasCompactSupport.comp_homeomorph hf e.toHomeomorph
end PositivityTheory.ThKOwn
