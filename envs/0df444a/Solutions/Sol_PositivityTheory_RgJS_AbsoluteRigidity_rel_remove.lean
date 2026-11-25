-- Prove2me | solution 1 for PositivityTheory.RgJS.AbsoluteRigidity.rel_remove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:10.109739+00:00
-- url     : https://prove2.me/submissions/171da6dd-ac5f-402f-b3f5-88f228fe3c80

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
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {x : ι → X × ℝ}
    {y : κ → X × ℝ} (h : Rel q A x y) (i : ι) (j : κ) (hij : x i = y j) :
    Rel q A (fun i' : {i' // i' ≠ i} => x i') (fun j' : {j' // j' ≠ j} => y j') := by
  intro w k
  have h1 := h w k
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne _ j, hij] at h1
  exact add_left_cancel h1
end PositivityTheory.RgJS.AbsoluteRigidity
