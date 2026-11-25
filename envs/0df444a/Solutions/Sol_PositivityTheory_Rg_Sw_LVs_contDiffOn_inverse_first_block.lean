-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.contDiffOn_inverse_first_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:35.513078+00:00
-- url     : https://prove2.me/submissions/91d51727-91fe-4320-92cf-ae0d6dd16e67

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_id

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
theorem _root_.solution (s : Set (M2 n)) (hs : ∀ x ∈ s, IsUnit x.det) : ∀ i j, ContDiffOn ℂ ∞ (fun x => ub1 x i j) s := by
  intro i j
  have hinv := cdo_inv (cdo_id s) fun x hx => (hs x hx).ne_zero
  simp only [ub1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.of_apply, smul_eq_mul]
  exact (hinv _ _).add (contDiffOn_const.mul (hinv _ _))
end PositivityTheory.Rg.Sw.LVs
