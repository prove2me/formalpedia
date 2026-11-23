-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_b314fdf1b50d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:22.579803+00:00
-- url     : https://prove2.me/submissions/f79dfdb0-e74b-40f7-8563-e1c20951d4fe

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp
end PositivityTheory.Rg.Sw.LVs
