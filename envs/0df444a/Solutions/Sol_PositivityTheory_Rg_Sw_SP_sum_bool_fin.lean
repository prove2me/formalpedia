-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.sum_bool_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:24.449547+00:00
-- url     : https://prove2.me/submissions/70d0ea62-c70a-4b65-bcff-62852b5e8b76

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC

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
theorem _root_.solution (F : Bool × Fin n × Fin n → ℂ) :
    ∑ kk, F kk = ∑ a : Fin n, ∑ d : Fin n, F (false, a, d) + ∑ a : Fin n, ∑ d : Fin n, F (true, a, d) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type]
  ring
end PositivityTheory.Rg.Sw.SP
