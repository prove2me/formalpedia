-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.evQ_derPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:42.197224+00:00
-- url     : https://prove2.me/submissions/1bb32817-b4fa-47ee-92a7-2bf2d269c910

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_CC
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_yv
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_derPart_apply


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
theorem _root_.solution (s z : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (derPart s b k l Q) B = ∑ a : Fin n, ∑ d : Fin n,
      -(cB s b) * (vals s B (b, a, k) * vals s B (b, l, d) * evQ s z (MvPolynomial.pderiv (b, a, d) Q) B) := by
  rw [derPart_apply, evQ_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [evQ_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [evQ_mul, evQ_CC, evQ_mul, evQ_mul, evQ_yv, evQ_yv]
end PositivityTheory.Rg.Sw.SP
