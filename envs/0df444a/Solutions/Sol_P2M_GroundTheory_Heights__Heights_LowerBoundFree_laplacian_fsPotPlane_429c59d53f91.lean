-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_laplacian_fsPotPlane_429c59d53f91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:08.792497+00:00
-- url     : https://prove2.me/submissions/e406c528-6ca7-453f-bdee-2890257b58c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_fderiv_fderiv_fsPotPlane_apply_633f92b0ff36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_partial_f6bd2ae7e203

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
theorem _root_.solution (y : ℂ) : Δ fsPotPlane y = 2 / (1 + ‖y‖ ^ 2) ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_fsPotPlane_apply, fderiv_fderiv_fsPotPlane_apply,
    (hasFDerivAt_partial y 1).fderiv, (hasFDerivAt_partial y Complex.I).fderiv]
  have hn : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hp : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  simp [Complex.inner]
  rw [hn] at hp ⊢
  field_simp
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree
