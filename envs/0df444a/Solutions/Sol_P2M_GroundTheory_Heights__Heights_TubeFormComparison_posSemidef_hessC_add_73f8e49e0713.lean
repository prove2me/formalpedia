-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_add_73f8e49e0713
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:58.429437+00:00
-- url     : https://prove2.me/submissions/d9bd2b0b-92f1-465f-adc9-bd536326dd4f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_euclPot_8b94f23095e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_euclPot_ff6b1ef3877d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_norm_sq_le_sum_655fe36f7161
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add__d2d06fbdee79
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_add__c2c0858c9e7b
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul


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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison
namespace GroundTheory.Heights₂.Heights.TubeFormComparison
theorem _root_.solution {N : ℕ} {f : (Fin N → ℂ) → ℝ} {x : Fin N → ℂ} (hf : ContDiffAt ℝ 2 f x)
    {c : ℝ} (hc : 0 ≤ c) (hl : ∀ w, -c * ‖w‖ ^ 2 ≤ levi f x w) :
    (hessC f x + (c : ℂ) • 1).PosSemidef := by
  have hE' : ContDiffAt ℝ 2 (euclPot : (Fin N → ℂ) → ℝ) x :=
    ((contDiff_euclPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hE : ContDiffAt ℝ 2 (fun w => c * euclPot w) x := contDiffAt_const.mul hE'
  have e : hessC f x + (c : ℂ) • 1 = hessC (fun w => f w + c * euclPot w) x := by
    rw [ReciprocityTheory.AnForm.M.hessC_add' f _ x hf hE, ReciprocityTheory.AnForm.M.hessC_const_mul', hessC_euclPot]
  rw [e]
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ x (hf.add hE) fun w => ?_
  rw [levi_add_smul c hf hE' w, levi_euclPot]
  have h1 := hl w
  have h2 := norm_sq_le_sum w
  nlinarith
end GroundTheory.Heights₂.Heights.TubeFormComparison
