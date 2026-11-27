-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PowerUnitCount_proof_7557d65e2812
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:31.319017+00:00
-- url     : https://prove2.me/submissions/a53feec3-012c-44bb-b3b0-4a7cd75048b0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsPowerUnitCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPowerUnitCount
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_powerUnitCount_of_root_23151f316edc
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology Matrix Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PowerUnitCount
theorem _root_.solution : PowerUnitCount.Statement := by
  intro d m O F H s hO hs hs0 hF hH hHs hbij
  have hFa : ∀ j, AnalyticAt ℂ (fun τ => F τ j) s := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood (d + 1) O _ hO (differentiableOn_pi.mp hF j) s hs
  have hHa : AnalyticAt ℂ H s := ReciprocityTheory.AnForm.Osgood.osgood (d + 1) O H hO hH s hs
  by_cases hm : m = 0
  · exact powerUnitCount_of_root (k := fun _ => 1) hs0 hFa hHa.continuousAt hHs analyticAt_const
      one_ne_zero (fun h => (h hm).elim) hbij
  · have hroot : ∀ x : ℂ, (x ^ ((m : ℂ)⁻¹)) ^ m = x := fun x => Complex.cpow_nat_inv_pow x hm
    refine powerUnitCount_of_root (k := fun τ => H s ^ ((m : ℂ)⁻¹) * ((H s)⁻¹ * H τ) ^ ((m : ℂ)⁻¹))
      hs0 hFa hHa.continuousAt hHs ?_ ?_ ?_ hbij
    · refine analyticAt_const.mul ((analyticAt_const.mul hHa).cpow analyticAt_const ?_)
      show (H s)⁻¹ * H s ∈ Complex.slitPlane
      rw [inv_mul_cancel₀ hHs]
      exact Complex.one_mem_slitPlane
    · intro h
      rw [inv_mul_cancel₀ hHs, Complex.one_cpow, mul_one] at h
      apply hHs
      rw [← hroot (H s), h, zero_pow hm]
    · intro _ τ
      rw [mul_pow, hroot, hroot, mul_inv_cancel_left₀ hHs]
end PowerUnitCount
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
