-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.det_ne_zero_of_inG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:32.198677+00:00
-- url     : https://prove2.me/submissions/5eff0f28-0036-4699-8a78-57f9264b67dc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Imports
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarDir
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivEqZeroOfVanish
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_JJ_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {y : M2 n} (hy : InG y) : y.det ≠ 0 := by
  intro h
  have hJ : (JJ n).det ≠ 0 := by
    intro hJ
    have := congrArg Matrix.det (JJ_sq (n := n))
    rw [det_mul, hJ, mul_zero, det_neg, det_one] at this
    simp at this
  have := congrArg Matrix.det hy
  rw [det_mul, det_mul, h, mul_zero] at this
  exact hJ this.symm
end PositivityTheory.Rg.Sw.LVs
