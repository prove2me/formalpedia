-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.fQ_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:44.154667+00:00
-- url     : https://prove2.me/submissions/5bf085e1-be5b-441e-abdc-6c17c29b2037

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_sum


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s z : ℂ) (m : ℕ) {ι : Type} (t : Finset ι) (a : ι → ℂ) (P : ι → Fm n) (B : MC n) :
    fQ s z m (∑ i ∈ t, a i • P i) B = ∑ i ∈ t, a i * fQ s z m (P i) B := by
  simp only [fQ, evQ_sum, evQ_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end PositivityTheory.Rg.Sw.SP
