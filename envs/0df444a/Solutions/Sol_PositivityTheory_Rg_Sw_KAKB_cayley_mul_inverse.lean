-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.KAKB.cayley_mul_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:28.581175+00:00
-- url     : https://prove2.me/submissions/e731028d-6a78-46dc-9646-ae6cb8fa2e5f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_CayleyMulConjTranspose
import Theorems.Thm_PositivityTheory_Rg_Sw_KAKB_cayley_mul_conjTranspose

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
theorem _root_.solution : C0 n * C1 n = 1 := by
  rw [C1, Matrix.mul_smul, cayley_mul_conjTranspose, smul_smul]; norm_num
end PositivityTheory.Rg.Sw.KAKB
