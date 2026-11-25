-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.djSec_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:23.214916+00:00
-- url     : https://prove2.me/submissions/8ff2f1eb-4c76-4fee-b075-c618cfb3faf7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_minorOn_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_detD_const_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_card_blkA
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_card_blkB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_scalar_section_mul_block_unipotent

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
theorem _root_.solution (hC : Cayley) : DjSec := by
  intro n j p q x hj h1 h2
  have hin : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
      (f0 p q x * (∏ i ∈ Finset.range (n - j), (-(p : ℂ) + i)) * minorOn (blkB j) (wM x)⁻¹) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-q) := by
    intro T
    simp_rw [scalar_section_mul_block_unipotent h1 h2 T]
    rw [detD_const_mul, hC, card_blkB hj, minorOn_eq]
    push_cast
    ring
  simp_rw [hin]
  rw [detD_const_mul, hC, card_blkA hj]
  simp only [minorOn_eq]
  push_cast
  ring
end PositivityTheory.Rg.Sw.LVs
