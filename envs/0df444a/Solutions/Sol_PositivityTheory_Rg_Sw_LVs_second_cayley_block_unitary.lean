-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.second_cayley_block_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:48.572776+00:00
-- url     : https://prove2.me/submissions/a34fd814-1983-416e-855d-69dc37596ee7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_second_cayley_block_mul_conjTranspose_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_lower_mul_conjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u2 k * (u2 k)ᴴ = 1 := by
  rw [second_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]
end PositivityTheory.Rg.Sw.LVs
