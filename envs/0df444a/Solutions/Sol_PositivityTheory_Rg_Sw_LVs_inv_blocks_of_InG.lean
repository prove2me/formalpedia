-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.inv_blocks_of_InG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:28.761291+00:00
-- url     : https://prove2.me/submissions/365e08fd-222d-46ff-9a0c-db40f491d8a1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inv_eq_of_InG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {x : M2 n} (hx : InG x) :
    x⁻¹ = Matrix.fromBlocks (x.toBlocks₂₂)ᴴ (-(x.toBlocks₁₂)ᴴ) (-(x.toBlocks₂₁)ᴴ) (x.toBlocks₁₁)ᴴ := by
  rw [inv_eq_of_InG hx]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks x]
  simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
end PositivityTheory.Rg.Sw.LVs
