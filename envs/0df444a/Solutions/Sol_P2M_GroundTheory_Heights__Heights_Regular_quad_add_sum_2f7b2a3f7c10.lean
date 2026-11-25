-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_quad_add_sum_2f7b2a3f7c10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:43.602466+00:00
-- url     : https://prove2.me/submissions/21fbf1d5-8e2b-4c67-ac8e-45bd0e84a475

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds

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
open Metric Matrix Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {g a : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (l : Fin a → ℝ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    v ⬝ᵥ (A + ∑ i, l i • B i) *ᵥ v = v ⬝ᵥ A *ᵥ v + ∑ i, l i * (v ⬝ᵥ B i *ᵥ v) := by
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
end GroundTheory.Heights₂.Heights.Regular
