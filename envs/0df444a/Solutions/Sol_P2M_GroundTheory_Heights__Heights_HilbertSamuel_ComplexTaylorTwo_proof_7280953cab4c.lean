-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComplexTaylorTwo_proof_7280953cab4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:44.446609+00:00
-- url     : https://prove2.me/submissions/93d573d3-0137-4e4f-81cc-1d42f7568c9e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexTaylor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComplexTaylorTwo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_taylor_two_isLittleO_1ad3385e6223
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_complexLinearCoeffs_dot_68aaf7064e75
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_dot_complexQuadMatrix_d68800a2e786
import Theorems.Thm_ReciprocityTheory_AnForm_M_re_star_dot_hessC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace ComplexTaylorTwo
theorem _root_.solution : ComplexTaylorTwo.Statement := by
  intro D ψ y₀ hψ
  refine ⟨complexLinearCoeffs (fderiv ℝ ψ y₀), complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀), ?_⟩
  refine (taylor_two_isLittleO hψ).congr_left fun z => ?_
  have h1 := re_complexLinearCoeffs_dot (fderiv ℝ ψ y₀) z
  have h2 := re_dot_complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀) z
  have h3 := ReciprocityTheory.AnForm.M.re_star_dot_hessC ψ y₀ (star z)
  rw [star_star] at h3
  rw [Complex.add_re, h1, h2, h3]
  unfold levi
  ring
end ComplexTaylorTwo
end GroundTheory.Heights₂.Heights.HilbertSamuel
