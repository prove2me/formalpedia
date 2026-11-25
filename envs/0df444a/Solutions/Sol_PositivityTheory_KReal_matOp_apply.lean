-- Prove2me | solution 1 for PositivityTheory.KReal.matOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:49.642961+00:00
-- url     : https://prove2.me/submissions/76199ce3-d0f2-4d00-acfd-54b16e366a4e

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
theorem _root_.solution (m : Matrix I I ℂ) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    matOp m Θ i = ∑ j, m i j • Θ j := rfl
end PositivityTheory.KReal
