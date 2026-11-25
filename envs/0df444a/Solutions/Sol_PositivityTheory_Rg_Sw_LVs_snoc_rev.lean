-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.snoc_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:34.292705+00:00
-- url     : https://prove2.me/submissions/09563314-0ca2-4527-8a1f-b75220070da2

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {N : ℕ} (W : Fin (N + 1) → M2 n) :
    (Fin.snoc (fun i : Fin N => W (Fin.rev i).succ) (W 0) : Fin (N + 1) → M2 n) = fun i => W (Fin.rev i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc, Fin.rev_castSucc]
end PositivityTheory.Rg.Sw.LVs
