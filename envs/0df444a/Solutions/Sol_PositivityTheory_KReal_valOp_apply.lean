-- Prove2me | solution 1 for PositivityTheory.KReal.valOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:48.551668+00:00
-- url     : https://prove2.me/submissions/9b6ee992-df65-4e14-b2f7-ee9fa1d5d97a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA

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
variable {I : Type} [Fintype I] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.KReal
theorem _root_.solution (A : Module.End ℂ V) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    valOp A Θ i = A (Θ i) := rfl
end PositivityTheory.KReal
