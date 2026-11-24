-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___127afe6e25e5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:59.456802+00:00
-- url     : https://prove2.me/submissions/b679425f-3b6f-4f94-8bc7-7dc71f8b98bc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_b314fdf1b50d

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
theorem _root_.solution (x : M2 n) : (x * Cm n).toBlocks₂₂ = u2 x := by
  rw [toBlocks₂₂_mul, u2, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one]
end PositivityTheory.Rg.Sw.LVs
