-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_WR_B_mul_single_apply__f54afcee4867
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:13.247793+00:00
-- url     : https://prove2.me/submissions/9153a70e-f9b8-4a74-a6a4-dcb199b871ff

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (a c k l : Fin n) :
    (M * Matrix.single l k (1 : ℂ)) a c = if k = c then M a l else 0 := by
  simp only [Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single l]
  · by_cases h : k = c <;> simp [h]
  · intro d _ hd; simp [Ne.symm hd]
  · simp
end PositivityTheory.Rg.Sw.WR.B
