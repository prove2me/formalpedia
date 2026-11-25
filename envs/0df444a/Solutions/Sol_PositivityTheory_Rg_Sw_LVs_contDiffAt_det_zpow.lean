-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.contDiffAt_det_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:21.221663+00:00
-- url     : https://prove2.me/submissions/1cf4946c-cdc2-4a86-945b-810dfe2aadc0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiff_det_one_add

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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (M : Matrix ι ι ℂ) (t : ℤ) {k : WithTop ℕ∞} :
    ContDiffAt ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S).det ^ t) 0 := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg t
  · simp only [zpow_natCast]
    exact ((contDiff_det_one_add M).pow m).contDiffAt
  · simp only [_root_.zpow_neg, zpow_natCast]
    refine (((contDiff_det_one_add M).pow m).contDiffAt).inv ?_
    simp
end PositivityTheory.Rg.Sw.LVs
