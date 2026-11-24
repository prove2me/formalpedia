-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_apply_d25b8e844fff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:00.973404+00:00
-- url     : https://prove2.me/submissions/f78cac58-3552-4f77-8dbe-5ac8f27e0403

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
theorem _root_.solution (j : ℕ) (σ : Perm (Ψ × Fin N)) (l : Ψ × Fin N) :
    (∑ l', Finsupp.single (σ l') (colExp j N l'.2)) (σ l) = colExp j N l.2 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, σ.injective.eq_iff]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
