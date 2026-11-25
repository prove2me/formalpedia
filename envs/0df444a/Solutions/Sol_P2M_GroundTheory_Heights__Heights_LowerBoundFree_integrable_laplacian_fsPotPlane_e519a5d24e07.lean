-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_integrable_laplacian_fsPotPlane_e519a5d24e07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:34.559879+00:00
-- url     : https://prove2.me/submissions/7d5e81a3-9e9c-411a-b978-d17e746bf6e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_laplacian_fsPotPlane_429c59d53f91

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution : Integrable (Δ fsPotPlane) := by
  have h : Δ fsPotPlane = fun y : ℂ => 2 * ((1 : ℝ) + ‖y‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
    funext y
    rw [laplacian_fsPotPlane, show -(4 : ℝ) / 2 = -((2 : ℕ) : ℝ) by norm_num,
      rpow_neg (by positivity), rpow_natCast, div_eq_mul_inv]
  rw [h]
  exact (integrable_rpow_neg_one_add_norm_sq (by simp [Complex.finrank_real_complex]; norm_num)).const_mul 2
end GroundTheory.Heights₂.Heights.LowerBoundFree
