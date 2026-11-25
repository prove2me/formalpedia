-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.prod_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:01.968641+00:00
-- url     : https://prove2.me/submissions/d0f52bf6-89d4-4932-9695-42374d73cabd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCHeights
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (j : ℕ) (c c' : ℂ) :
    (∏ r : Fin n, if r ∈ blkA (n := n) j then c else c') = c ^ (blkA (n := n) j).card * c' ^ (blkB (n := n) j).card := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  · congr 1
    ext x
    simp
  · congr 1
    ext x
    simp [blkB]
end PositivityTheory.Rg.Sw.LVs.TC
