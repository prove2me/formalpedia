-- Prove2me | solution 1 for PositivityTheory.RgJS.AbsoluteRigidity.rel_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:15.648355+00:00
-- url     : https://prove2.me/submissions/d12f5e4e-76f5-44c4-a5dd-b357e02ca1ef

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
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] {x : ι → X × ℝ} {y : κ → X × ℝ}
    (h : Rel q A x y) : Rel q A y x := fun w k => (h w k).symm
end PositivityTheory.RgJS.AbsoluteRigidity
