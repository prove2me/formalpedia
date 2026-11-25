-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_prod_bigMat_of_9a5918927180
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:15.242499+00:00
-- url     : https://prove2.me/submissions/347aa726-e92a-4ab7-bbcf-e988f783170f

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
theorem _root_.solution (j : ℕ) (σ : Perm (Ψ × Fin N))
    (hσ : ∀ l, (σ l).1 = l.1 ∧ (((σ l).2 : ℕ) < j ↔ (l.2 : ℕ) < j)) :
    ∏ l, bigMat (Ψ := Ψ) (N := N) j (σ l) l = monomial (∑ l, Finsupp.single (σ l) (colExp j N l.2)) 1 := by
  rw [monomial_sum_one]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [bigMat, (hσ l).1, (hσ l).2, X_pow_eq_monomial]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
