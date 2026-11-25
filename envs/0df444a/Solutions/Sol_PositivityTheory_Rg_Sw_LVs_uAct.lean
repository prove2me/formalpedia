-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.uAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:32.800019+00:00
-- url     : https://prove2.me/submissions/df6b58b8-271a-41c6-a7d5-5fe32c256f17

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cm_inv
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_03bb7bc462ab
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_b314fdf1b50d
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___89a26790be15
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___127afe6e25e5
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_first_cayley_block_mul_inverse_cayley
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_second_cayley_block_mul_inverse_cayley

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
theorem _root_.solution : UAct := by
  intro n x P Q R S
  simp only [mX, cm_inv, ← Matrix.mul_assoc]
  rw [first_cayley_block_mul_inverse_cayley, second_cayley_block_mul_inverse_cayley, toBlocks₂₁_mul (x * Cm n) (fromBlocks P Q R S),
    toBlocks₂₂_mul (x * Cm n) (fromBlocks P Q R S), mul_cm₂₁, mul_cm₂₂]
  simp
end PositivityTheory.Rg.Sw.LVs
