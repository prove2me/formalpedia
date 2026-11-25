-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.KAKB.cayley_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:26.192299+00:00
-- url     : https://prove2.me/submissions/be2030d8-a797-4b89-b2bc-74093ce1534a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_CayleyMulConjTranspose
import Theorems.Thm_PositivityTheory_Rg_Sw_KAKB_cayley_conjTranspose_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Matrix
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.KAKB
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.KAKB
theorem _root_.solution : C0 n * (C0 n)ᴴ = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module
end PositivityTheory.Rg.Sw.KAKB
