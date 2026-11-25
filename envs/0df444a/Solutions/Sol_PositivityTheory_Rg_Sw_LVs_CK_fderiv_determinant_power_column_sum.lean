-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.fderiv_determinant_power_column_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:57.494347+00:00
-- url     : https://prove2.me/submissions/35073644-7246-4ed0-96a4-351636b70c13

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerColumnSum
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_colQ_expand
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_determinant_power_column_int
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
theorem _root_.solution (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) (c : Fin N) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsum t c X := by
  rw [fderiv_determinant_power_column_int t X hX c, colQ_expand, map_sum, fsum]
  simp only [map_smul, smul_eq_mul]
end PositivityTheory.Rg.Sw.LVs.CK
