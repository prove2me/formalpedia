-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.dK_xZx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:56.837404+00:00
-- url     : https://prove2.me/submissions/5ad2dba2-790f-432b-ab83-607cc3608c36

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_reK_add_imK
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_reK_conj
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_imK_conj
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_fderiv_xZx_skew

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (Z x e : M2 n) (i j : Fin n ⊕ Fin n) :
    dK (fun y : M2 n => (y * Z * yᴴ) i j) x e = (e * (x * Z * xᴴ) - (x * Z * xᴴ) * e) i j := by
  rw [dK, fderiv_xZx_skew Z x _ (reK_conj e), fderiv_xZx_skew Z x _ (imK_conj e)]
  conv_rhs => rw [← reK_add_imK e]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.LVs.II
