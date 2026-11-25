-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CEq.detD_eq_Dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:36.175708+00:00
-- url     : https://prove2.me/submissions/42a3abcf-3e00-49a0-a278-0e3be6048f0b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq

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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.LVs.CEq
theorem _root_.solution (F : Matrix κ κ ℂ → ℂ) : detD F = Dg (Fintype.equivFin κ) F := rfl
end PositivityTheory.Rg.Sw.LVs.CEq
