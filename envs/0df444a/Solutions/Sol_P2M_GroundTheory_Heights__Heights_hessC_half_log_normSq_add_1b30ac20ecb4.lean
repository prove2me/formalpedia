-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hessC_half_log_normSq_add_1b30ac20ecb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:21.981467+00:00
-- url     : https://prove2.me/submissions/90deae1e-e92f-47d5-8a24-1bbe454ad67c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHessCCompPluri
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOffZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffGradient_proof_81aaa98bdfc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HessCCompPluri_proof_738153eeeb36
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_congr__aa19fc468bd1
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_log_norm


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {D : ℕ} (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ)
    (hh : AnalyticAt ℂ h y) (hy : h y ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y =
      ((ε / (2 * (‖h y‖ ^ 2 + ε) ^ 2) : ℝ) : ℂ) • hessC (fun w => ‖h w‖ ^ 2) y := by
  set L : (Fin D → ℂ) → ℝ := fun w => Real.log ‖h w‖ with hLdef
  set F : ℝ → ℝ := fun t => Real.log (Real.exp (2 * t) + ε) / 2 with hFdef
  set G : ℝ → ℝ := fun t => Real.exp (2 * t) with hGdef
  have hhc : ContDiffAt ℝ 2 h y := (hh.contDiffAt (n := 2)).restrict_scalars ℝ
  have hLc : ContDiffAt ℝ 2 L y := (hhc.norm ℝ hy).log (norm_ne_zero_iff.2 hy)
  have hL0 : hessC L y = 0 := ReciprocityTheory.AnForm.A.hessC_log_norm h y hh hy
  have he : ∀ t, HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul 2).exp
  have hFc : ContDiff ℝ 2 F :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add contDiff_const).log
      (fun t => by simp only [Function.comp_apply, id]; positivity) |>.div_const 2
  have hGc : ContDiff ℝ 2 G := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hF := HessCCompPluri.proof D F L y hFc.contDiffAt hLc hL0
  have hG := HessCCompPluri.proof D G L y hGc.contDiffAt hLc hL0
  have hdF : deriv F = fun t => Real.exp (2 * t) / (Real.exp (2 * t) + ε) := by
    funext t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    refine (((he t).add_const ε).log hp |>.div_const 2).deriv.trans ?_
    field_simp
  have hddF : ∀ t, deriv (deriv F) t = 2 * ε * Real.exp (2 * t) / (Real.exp (2 * t) + ε) ^ 2 := by
    intro t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    rw [hdF]
    refine ((he t).div ((he t).add_const ε) hp).deriv.trans ?_
    field_simp
    ring
  have hdG : deriv G = fun t => Real.exp (2 * t) * 2 := funext fun t => (he t).deriv
  have hddG : ∀ t, deriv (deriv G) t = Real.exp (2 * t) * 2 * 2 := fun t => by
    rw [hdG]
    exact ((he t).mul_const 2).deriv
  have hexp : ∀ w, h w ≠ 0 → Real.exp (2 * L w) = ‖h w‖ ^ 2 := fun w hw => by
    rw [hLdef, show 2 * Real.log ‖h w‖ = Real.log (‖h w‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  have hev : ∀ᶠ w in 𝓝 y, h w ≠ 0 := hh.continuousAt.eventually_ne hy
  have eF : hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y = hessC (fun w => F (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hFdef, hexp w hw])
  have eG : hessC (fun w => ‖h w‖ ^ 2) y = hessC (fun w => G (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hGdef, hexp w hw])
  rw [eF, eG, hF, hG, hddF, hddG, hexp y hy, smul_smul]
  congr 1
  have ha : 0 < ‖h y‖ ^ 2 := by positivity
  push_cast
  field_simp
end GroundTheory.Heights₂.Heights
