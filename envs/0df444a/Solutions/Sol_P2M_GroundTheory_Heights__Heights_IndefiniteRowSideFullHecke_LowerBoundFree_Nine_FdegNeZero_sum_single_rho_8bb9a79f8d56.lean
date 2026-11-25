-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_rho_8bb9a79f8d56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:03:49.216391+00:00
-- url     : https://prove2.me/submissions/45290c34-47a6-40b2-9fef-471fa7d76181

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PTwinFdegNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_rho_apply_0a0148cd7cde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_apply_d25b8e844fff

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
theorem _root_.solution (j : ℕ) (hj : j ≤ N) :
    (∑ l, Finsupp.single (rho (Ψ := Ψ) j hj l) (colExp j N l.2)) = delta0 j := by
  refine Finsupp.ext fun x => ?_
  obtain ⟨l, rfl⟩ := (rho (Ψ := Ψ) j hj).surjective x
  rw [sum_single_apply]
  simp only [delta0, Finsupp.coe_equivFunOnFinite_symm, rho_apply, rev, colExp]
  split_ifs <;> omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
