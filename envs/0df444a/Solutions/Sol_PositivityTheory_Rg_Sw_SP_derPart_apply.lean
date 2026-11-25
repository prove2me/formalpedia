-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.derPart_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:51:05.179214+00:00
-- url     : https://prove2.me/submissions/5e8011a2-bec0-4c45-90c4-6afcf78c9c03

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_smulC

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
theorem _root_.solution (s : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    derPart s b k l Q = ∑ a : Fin n, ∑ d : Fin n, MvPolynomial.C (Polynomial.C (-(cB s b))) *
      (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) Q) := by
  rw [derPart, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, smulC]
  rfl
end PositivityTheory.Rg.Sw.SP
