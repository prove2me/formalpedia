-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.iterated_derivative_corner_case_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:17.291716+00:00
-- url     : https://prove2.me/submissions/b4950e4a-1d5a-4dde-a3d9-8d15712f54fa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_determinant_power_zero_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_fderiv_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_ev_piF
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_iconst_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_icompL
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiF_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiF_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piF_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piF_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiF_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piF_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_H
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_determinant_power_corner_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiF_single
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piF_single_succ
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.piL_apply



set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (t : ℤ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      (t : ℂ) * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by
  have hA : AnalyticAt ℂ (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int (N + 1) t)
  have h1 := icompL (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) phiF phiF_add
    phiF_smul 0 0 phiF_zero hA N (fun k => Matrix.single k (e k).succ 1)
    (fun k => Matrix.single k.succ (e k).succ 1) (fun k => phiF_single k (e k).succ)
  rw [← h1]
  have hpi : piF = ⇑(piL N) := funext fun X => (piL_apply X).symm
  have hB : AnalyticAt ℂ (H N t ∘ piF) 0 := by
    rw [hpi]
    refine (analyticAt_H N t (piL N 0) ?_).comp ((piL N).analyticAt 0)
    rw [piL_apply, piF_zero, add_zero, det_one]
    exact one_ne_zero
  have hev : (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) ∘ phiF =ᶠ[𝓝 0]
      fun X => (t : ℂ) * (H N t ∘ piF) X := by
    filter_upwards [ev_piF N] with X hX
    exact fderiv_determinant_power_corner_int t X hX
  rw [(Filter.EventuallyEq.iteratedFDeriv ℂ hev N).eq_of_nhds, iconst_mul _ 0 _ hB]
  congr 1
  exact icompL (H N t) piF piF_add piF_smul 0 0 piF_zero (analyticAt_determinant_power_zero_int N t) N _ _
    (fun k => piF_single_succ k (e k))
end PositivityTheory.Rg.Sw.LVs.CK
