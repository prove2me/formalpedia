-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AlternantRowRule_intersectionNumber_baseChange_d9cfcb79419a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:47.699961+00:00
-- url     : https://prove2.me/submissions/43d3686b-8790-4480-a74e-cfc433bb412c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltRow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_prod_pow_add_single_6c948aa5d4ea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace AlternantRowRule
theorem _root_.solution : AlternantRowRule.Statement := by
  intro r q μ
  simp only [alternant, Matrix.det_apply, Matrix.of_apply, psum]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp_rw [KAlt.prod_pow_add_single, ← Finset.smul_sum, ← Finset.sum_mul]
  rw [Equiv.sum_comp σ (fun j => (X j : MvPolynomial (Fin r) ℚ) ^ q), mul_smul_comm]
end AlternantRowRule
end GroundTheory.Heights₂.Heights
