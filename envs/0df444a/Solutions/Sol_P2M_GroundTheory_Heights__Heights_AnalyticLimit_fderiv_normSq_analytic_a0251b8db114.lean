-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_normSq_analytic_a0251b8db114
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:10.020953+00:00
-- url     : https://prove2.me/submissions/5cf6c54d-e8a2-426a-9281-732f78a0493f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_comp_real_2280461a8adc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_re_analytic_f165eb17d640
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_im_analytic_7493638fe9a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_contDiffAt_re_analytic_701086e03a5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_contDiffAt_im_analytic_85ef43de592a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_sq_norm_eq_re_im_995b20f7781c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_hasDerivAt_sq__f72e6668d75d
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => ‖S z‖ ^ 2) y v =
      2 * ((S y).re * (fderiv ℂ S y v).re + (S y).im * (fderiv ℂ S y v).im) := by
  have hre := contDiffAt_re_analytic hS
  have him := contDiffAt_im_analytic hS
  have e : (fun z => ‖S z‖ ^ 2) = fun z => (S z).re ^ 2 + (S z).im ^ 2 :=
    funext fun z => by rw [sq_norm_eq_re_im, one_mul]
  have d1 : DifferentiableAt ℝ (fun z => (S z).re ^ 2) y :=
    (hre.differentiableAt (by norm_num)).pow 2
  have d2 : DifferentiableAt ℝ (fun z => (S z).im ^ 2) y :=
    (him.differentiableAt (by norm_num)).pow 2
  rw [e, fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply,
    fderiv_comp_real (G := fun x : ℝ => x ^ 2) (hre.differentiableAt (by norm_num))
      (hasDerivAt_sq' _),
    fderiv_comp_real (G := fun x : ℝ => x ^ 2) (him.differentiableAt (by norm_num))
      (hasDerivAt_sq' _), fderiv_re_analytic hS, fderiv_im_analytic hS]
  ring
end GroundTheory.Heights₂.Heights.AnalyticLimit
