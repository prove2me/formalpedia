-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.trace_mul_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:23.631359+00:00
-- url     : https://prove2.me/submissions/dd00846a-791b-4455-90a2-859680e5d000

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : (M * Matrix.single l k (1 : ℂ)).trace = M k l := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hi]
  · simp
end PositivityTheory.Rg.Sw.WR.B
