-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_det_bigMat_b6eb18f561cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:18.73692+00:00
-- url     : https://prove2.me/submissions/9d216aaa-5027-40e7-84f1-6f7dbd4398a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PTwinFdegNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_det_blkMat_467515454fff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open MvPolynomial Matrix Equiv
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
theorem _root_.solution (j : ℕ) (hj : j ≤ N) : (bigMat (Ψ := Ψ) (N := N) j).det = fibV j hj := by
  have h : bigMat (Ψ := Ψ) (N := N) j =
      (blockDiagonal fun τ => blkMat (Ψ := Ψ) (N := N) j τ).submatrix (Equiv.prodComm Ψ (Fin N))
        (Equiv.prodComm Ψ (Fin N)) := by
    refine Matrix.ext fun x l => ?_
    obtain ⟨x1, x2⟩ := x
    obtain ⟨l1, l2⟩ := l
    simp only [bigMat, blkMat, of_apply, submatrix_apply, Equiv.prodComm_apply, blockDiagonal_apply, Prod.fst_swap,
      Prod.snd_swap]
    by_cases h1 : x1 = l1
    · subst h1
      simp
    · simp [h1]
  rw [h, det_submatrix_equiv_self, det_blockDiagonal, fibV]
  exact Finset.prod_congr rfl fun τ _ => det_blkMat j hj τ
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
