-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.capelli_determinant_integer_rising
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:19.386681+00:00
-- url     : https://prove2.me/submissions/694ca6db-ca75-4f16-8a75-03bc6236d15e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedDerivativeColumnCaseInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyK
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_rec_step
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_determinant_power_zero_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_detD_fin
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
theorem _root_.solution (t : ℤ) : ∀ N : ℕ, detD (H N t) = ∏ i ∈ Finset.range N, ((t : ℂ) + i)
  | 0 => by
    rw [detD_fin 0 _ (analyticAt_determinant_power_zero_int 0 t)]
    simp [H, iteratedFDeriv_zero_apply]
  | N + 1 => by
    rw [rec_step, solution t N, Finset.prod_range_succ]
    ring
end PositivityTheory.Rg.Sw.LVs.CK
