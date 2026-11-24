-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SchwartzBaire_iteratedFDeriv_sub_apply__4bfc50ada7a9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:06.087252+00:00
-- url     : https://prove2.me/submissions/c01d66eb-e3c7-4532-978e-dec4ae033b7b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchwartzBaire
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory.CompanionTheory.SchwartzBaire
theorem _root_.solution (f g : 𝓢(E, F)) (l : ℕ) (x : E) :
    iteratedFDeriv ℝ l (⇑(f - g)) x = iteratedFDeriv ℝ l f x - iteratedFDeriv ℝ l g x := by
  have h : (⇑(f - g) : E → F) = ⇑f - ⇑g := by
    ext x
    simp
  rw [h]
  exact iteratedFDeriv_sub_apply (f.smooth l).contDiffAt (g.smooth l).contDiffAt
end GlobalTheory.CompanionTheory.SchwartzBaire
