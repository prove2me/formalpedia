-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_rename_det_bigMat_f476cd7e2f26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:03:46.49538+00:00
-- url     : https://prove2.me/submissions/ad0fd508-cafb-4f0a-8bf3-d52cef0b1404

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
theorem _root_.solution (j : ℕ) (w : Perm (Ψ × Fin N)) (hw : w ∈ G0 j) :
    rename w (bigMat (Ψ := Ψ) (N := N) j).det = ((Perm.sign w : ℤ) : ℚ) • (bigMat j).det := by
  have hw' : ∀ x, (w x).1 = x.1 ∧ (((w x).2 : ℕ) < j ↔ (x.2 : ℕ) < j) := (Finset.mem_filter.mp hw).2
  rw [AlgHom.map_det]
  have h : (rename w : Rts Ψ N →ₐ[ℚ] Rts Ψ N).mapMatrix (bigMat j) = (bigMat j).submatrix w id := by
    refine Matrix.ext fun x l => ?_
    have e : ((w x).1 = l.1 ∧ (((w x).2 : ℕ) < j ↔ (l.2 : ℕ) < j)) ↔
        (x.1 = l.1 ∧ ((x.2 : ℕ) < j ↔ (l.2 : ℕ) < j)) := by rw [(hw' x).1, (hw' x).2]
    simp only [AlgHom.mapMatrix_apply, map_apply, bigMat, of_apply, submatrix_apply, id, e]
    split_ifs <;> simp
  rw [h, det_permute, MvPolynomial.smul_eq_C_mul]
  congr 1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
