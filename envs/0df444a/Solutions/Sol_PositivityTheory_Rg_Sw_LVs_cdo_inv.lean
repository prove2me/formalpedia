-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cdo_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:25.956147+00:00
-- url     : https://prove2.me/submissions/8c6b40a2-0b7a-4b32-a307-ebdedcd1fa51

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_det

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set E} {M : E → Matrix ι ι ℂ}
    (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) (h0 : ∀ x ∈ s, (M x).det ≠ 0) :
    ∀ i j, ContDiffOn ℂ ∞ (fun x => (M x)⁻¹ i j) s := by
  intro i j
  have e : ∀ x, (M x)⁻¹ i j = ((M x).det)⁻¹ * ((M x).updateRow j (Pi.single i 1)).det := by
    intro x
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  simp only [e]
  refine ((cdo_det hM).inv h0).mul (cdo_det fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hM a b
end PositivityTheory.Rg.Sw.LVs
