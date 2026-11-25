-- Prove2me | solution 1 for PositivityTheory.RgJS.AbsoluteRigidity.rel_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:13.033874+00:00
-- url     : https://prove2.me/submissions/20fde672-a6cc-4aa7-9e59-9485e6ef64ca

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_AbsoluteRigidityLemma_AbsoluteRigidityOfCommon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.AbsoluteRigidity
variable {W : Type} {q : W → ℕ} {X : Type} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ}
namespace PositivityTheory.RgJS.AbsoluteRigidity
theorem _root_.solution (hq : ∀ w, 2 ≤ q w) {ι κ : Type} [Fintype ι] [Fintype κ] {x : ι → X × ℝ} {y : κ → X × ℝ}
    (h : Rel q A x y) (τ : ℝ) : Rel q A (sh τ ∘ x) (sh τ ∘ y) := by
  intro w k
  have hq0 : (q w : ℂ) ≠ 0 := by
    have := hq w
    exact_mod_cast (by omega : q w ≠ 0)
  have e : ∀ (a : ℂ) (t : ℝ), (a * (q w : ℂ) ^ (-((t - τ : ℝ) : ℂ))) ^ k =
      ((q w : ℂ) ^ (τ : ℂ)) ^ k * (a * (q w : ℂ) ^ (-(t : ℂ))) ^ k := by
    intro a t
    rw [← mul_pow]
    congr 1
    rw [show (q w : ℂ) ^ (τ : ℂ) * (a * (q w : ℂ) ^ (-(t : ℂ))) = a * ((q w : ℂ) ^ (τ : ℂ) * (q w : ℂ) ^ (-(t : ℂ))) by ring,
      ← Complex.cpow_add _ _ hq0]
    congr 2
    push_cast
    ring
  have h1 := congrArg (fun z => ((q w : ℂ) ^ (τ : ℂ)) ^ k * z) (h w k)
  simp only [Finset.mul_sum] at h1
  simp only [Function.comp_apply, sh, e]
  exact h1
end PositivityTheory.RgJS.AbsoluteRigidity
