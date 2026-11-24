-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.analyticAt_fsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:48.042821+00:00
-- url     : https://prove2.me/submissions/f7bdc46d-e040-4f0a-84d2-54af67d79925

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerColumnSum
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_piF
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_H
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_fderiv_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.phiL_apply
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.piL_apply



set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (t : ℤ) (c : Fin N) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) (h : (1 + piF X0).det ≠ 0) :
    AnalyticAt ℂ (fsum t c) X0 := by
  have hE : ∀ k : Fin N, AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ =>
      X k 0 * fderiv ℂ (H N t) (piF X) (Matrix.single k c 1)) X0 := by
    intro k
    refine (analyticAt_entry k 0 X0).mul ?_
    exact (analyticAt_fderiv_apply (H N t) (piF X0) (Matrix.single k c 1)
      (analyticAt_H N t _ h)).comp (analyticAt_piF X0)
  have hs := (Finset.analyticAt_sum Finset.univ (fun k _ => hE k)).neg
  convert hs using 1
  funext X
  simp [fsum, Finset.sum_apply]
end PositivityTheory.Rg.Sw.LVs.CK
