-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.term_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:24.97509+00:00
-- url     : https://prove2.me/submissions/771389ae-fd59-4de0-8e59-5f0ee671d6a7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedDerivativeColumnCaseInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyK
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_determinant_power_zero_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_ipeel0
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
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (t : ℤ) (N : ℕ) (p : Fin (N + 1)) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ (N + 1) (H (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (p, e) k) 1) =
      iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 p 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (p, e) k.succ) 1) := by
  rw [ipeel0 (H (N + 1) t) 0 (analyticAt_determinant_power_zero_int (N + 1) t) N]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  rfl
end PositivityTheory.Rg.Sw.LVs.CK
