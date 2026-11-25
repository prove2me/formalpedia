-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_det_blkMat_467515454fff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:12.73596+00:00
-- url     : https://prove2.me/submissions/c52af596-1828-4f4f-a3d9-3b67dd263eed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PTwinFdegNeZero

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
omit [Fintype Ψ] [DecidableEq Ψ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
theorem _root_.solution (j : ℕ) (hj : j ≤ N) (τ : Ψ) :
    (blkMat (Ψ := Ψ) (N := N) j τ).det = altRho j (yv j hj τ) * altRho (N - j) (zv j τ) := by
  let e : Fin j ⊕ Fin (N - j) ≃ Fin N := finSumFinEquiv.trans (finCongr (by omega))
  rw [← det_submatrix_equiv_self e, ← Matrix.fromBlocks_toBlocks ((blkMat j τ).submatrix e e)]
  have h21 : ((blkMat (Ψ := Ψ) (N := N) j τ).submatrix e e).toBlocks₂₁ = 0 := by
    ext a b
    simp [toBlocks₂₁, blkMat, e]
  rw [h21, det_fromBlocks_zero₂₁]
  congr 1
  · unfold altRho
    congr 1
    refine Matrix.ext fun a b => ?_
    simp [toBlocks₁₁, blkMat, e, yv, colExp]
    rfl
  · unfold altRho
    congr 1
    refine Matrix.ext fun a b => ?_
    simp [toBlocks₂₂, blkMat, e, zv, colExp]
    rw [show N - 1 - (j + (b : ℕ)) = N - j - 1 - b by omega]
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
