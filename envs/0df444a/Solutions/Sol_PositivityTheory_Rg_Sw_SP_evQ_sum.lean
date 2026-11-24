-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.evQ_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:41.59286+00:00
-- url     : https://prove2.me/submissions/a8c82d15-6188-4e4d-89ad-ec11181e0c73

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s z : ℂ) {ι : Type} (t : Finset ι) (P : ι → Fm n) (B : MC n) :
    evQ s z (∑ i ∈ t, P i) B = ∑ i ∈ t, evQ s z (P i) B := by
  simp [evQ, map_sum]
end PositivityTheory.Rg.Sw.SP
