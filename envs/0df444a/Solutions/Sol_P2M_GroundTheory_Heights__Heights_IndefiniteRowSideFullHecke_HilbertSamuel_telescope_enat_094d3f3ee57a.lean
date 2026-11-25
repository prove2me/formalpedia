-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_telescope_enat_094d3f3ee57a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:39.868092+00:00
-- url     : https://prove2.me/submissions/29a22032-6834-4dae-87f1-d5fd25a94f16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ∞) (c : Fin n → ℕ∞),
    (∀ j : Fin n, f j.castSucc = c j + f j.succ) → f 0 = ∑ j, c j + f (Fin.last n)
  | 0, f, c, _ => by simp
  | n + 1, f, c, h => by
    have ih : f (Fin.succ 0) = ∑ j : Fin n, c j.succ + f (Fin.last n).succ :=
      solution n (fun k => f k.succ) (fun j => c j.succ) (fun j => h j.succ)
    calc f 0 = c 0 + f (Fin.succ 0) := by simpa using h 0
      _ = ∑ j, c j + f (Fin.last (n + 1)) := by
        rw [ih, Fin.succ_last, Fin.sum_univ_succ, add_assoc]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
