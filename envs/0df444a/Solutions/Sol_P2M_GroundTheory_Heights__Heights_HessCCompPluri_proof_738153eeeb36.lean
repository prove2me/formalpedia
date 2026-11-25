-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HessCCompPluri_proof_738153eeeb36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:29:09.288321+00:00
-- url     : https://prove2.me/submissions/6bde282c-e0b4-4c69-8f56-3b153eb28291

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHessCCompPluri
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHessCCompPluri
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HessCCompPluri_fderiv_fderiv_comp_apply_52a7820e256e

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
open ReciprocityTheory.AnForm Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace HessCCompPluri
theorem _root_.solution : HessCCompPluri.Statement := by
  intro D F L z hF hL h0
  have hQ : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2 / 2) (L z) :=
    ((contDiff_id.pow 2).div_const 2).contDiffAt
  have hd1 : deriv (fun t : ℝ => t ^ 2 / 2) = fun t => t := by
    funext t
    rw [((hasDerivAt_pow 2 t).div_const 2).deriv]
    norm_num
  have key := HessCCompPluri.fderiv_fderiv_comp_apply hF hL
  have keyQ := HessCCompPluri.fderiv_fderiv_comp_apply hQ hL
  simp only [hd1, deriv_id'', one_mul] at keyQ
  ext i j
  have hij := congrFun (congrFun h0 i) j
  simp only [hessC, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  simp only [key, keyQ]
  push_cast at hij ⊢
  linear_combination (((deriv F (L z) : ℝ) : ℂ) - ((deriv (deriv F) (L z) : ℝ) : ℂ) * ((L z : ℝ) : ℂ)) * hij
end HessCCompPluri
end GroundTheory.Heights₂.Heights
