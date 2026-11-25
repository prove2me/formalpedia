-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_isOpen_logCover_5a352f02a4d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:30.238541+00:00
-- url     : https://prove2.me/submissions/ac6f9dc6-2376-406a-ba0b-4be45e9c3af6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by
  have h1 : IsOpen {w : Fin n → ℂ | ∀ i : Fin a, (w (Fin.castLE h i)).re < 0} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const
  have h2 : IsOpen {w : Fin n → ℂ | ∀ k : Fin n, a ≤ k.val → ‖w k‖ < 1} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun k => ?_
    by_cases hk : a ≤ k.val
    · simp only [hk, Set.iInter_true]
      exact isOpen_lt (f := fun w : Fin n → ℂ => ‖w k‖) (by fun_prop) continuous_const
    · simp [hk]
  exact h1.inter h2
end GroundTheory.Heights₂.Heights.Regular
