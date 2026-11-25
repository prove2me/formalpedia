-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_quad_sum_15bed5d07f6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:39.122523+00:00
-- url     : https://prove2.me/submissions/c2c9d5f1-b21d-4cfb-9735-f4ab759c8432

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((∑ j ∈ s, A j) *ᵥ x) = ∑ j ∈ s, x ⬝ᵥ (A j *ᵥ x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, dotProduct_add, ih]
end GroundTheory.Heights₂.Heights.MCBounds
