-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.iconst_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:15.680471+00:00
-- url     : https://prove2.me/submissions/a344652a-1db6-477e-93ca-1035284e8918

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
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
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (G : F → ℂ) (x : F) (a : ℂ)
    (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) :
    iteratedFDeriv ℂ n (fun y => a * G y) x u = a * iteratedFDeriv ℂ n G x u := by
  have h := iteratedFDeriv_const_smul_apply' (a := a) (i := n) (hG.contDiffAt (n := n))
  simp only [smul_eq_mul] at h
  rw [h, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
end PositivityTheory.Rg.Sw.LVs.CK
