-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_quad_smul_092261aee0d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:47.637935+00:00
-- url     : https://prove2.me/submissions/7ec9898f-8f57-4030-afa0-307cd15e7802

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
theorem _root_.solution {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) (t : ℝ) (v : Fin g → ℝ) :
    (t • v) ⬝ᵥ M *ᵥ (t • v) = t ^ 2 * (v ⬝ᵥ M *ᵥ v) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
end GroundTheory.Heights₂.Heights.Regular
