-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.MI.contDiff_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:28.602449+00:00
-- url     : https://prove2.me/submissions/11a31752-5b19-45ef-807e-499a21fe79c5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_MatInv
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.MI
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt.MI
theorem _root_.solution : ContDiff ℝ ∞ (fun x : M2 n => x.det) := by
  have : (fun x : M2 n => x.det) = fun x => ∑ σ : Equiv.Perm (Fin n ⊕ Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i := by
    funext x; rw [Matrix.det_apply]; simp [Units.smul_def, zsmul_eq_mul]
  rw [this]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => contDiff_entry _ _
end PositivityTheory.Rg.Sw.HSt.MI
