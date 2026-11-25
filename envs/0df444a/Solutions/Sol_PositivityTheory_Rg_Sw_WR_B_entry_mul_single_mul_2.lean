-- Prove2me | solution 2 for PositivityTheory.Rg.Sw.WR.B.entry_mul_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:51.843402+00:00
-- url     : https://prove2.me/submissions/cc1b6adb-e78a-4bdc-bd5c-1c4e156a09d0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_B_mul_single_apply__f54afcee4867

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (a b k l : Fin n) :
    (M * Matrix.single l k (1 : ℂ) * M) a b = M a l * M k b := by
  rw [Matrix.mul_apply]
  simp only [mul_single_apply', ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end PositivityTheory.Rg.Sw.WR.B
