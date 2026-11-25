-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_hessC_log_comp_d38474af266b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:12.304082+00:00
-- url     : https://prove2.me/submissions/6438137c-ea2f-4cd3-9e9d-b4047f8649f1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_hessC_comp_real_1b578ed93f88


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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLogPow
theorem _root_.solution {p : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hp : ContDiffAt ℝ 2 p y) (hpos : 0 < p y) :
    hessC (Real.log ∘ p) y =
      (((p y)⁻¹ : ℝ) : ℂ) • hessC p y + ((-((p y) ^ 2)⁻¹ : ℝ) : ℂ) • gradMat p p y := by
  set c := p y / 2 with hc
  have hc0 : 0 < c := by positivity
  set h : ℝ → ℝ := fun t => c / 2 + Real.smoothTransition ((t - c / 2) / (c / 2)) * (t - c / 2) with hh
  have hhpos : ∀ t, 0 < h t := by
    intro t
    by_cases ht : t ≤ c / 2
    · have : (t - c / 2) / (c / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      simp only [hh, Real.smoothTransition.zero_of_nonpos this, zero_mul, add_zero]; positivity
    · have := Real.smoothTransition.nonneg ((t - c / 2) / (c / 2))
      have : 0 ≤ Real.smoothTransition ((t - c / 2) / (c / 2)) * (t - c / 2) :=
        mul_nonneg this (by linarith)
      simp only [hh]; linarith
  have hhc : ContDiff ℝ 2 h := by
    have hs : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff (n := 2)
    exact contDiff_const.add ((hs.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
      (contDiff_id.sub contDiff_const))
  set F : ℝ → ℝ := Real.log ∘ h with hF
  have hFc : ContDiff ℝ 2 F := hhc.log fun t => (hhpos t).ne'
  have hFeq : F =ᶠ[𝓝 (p y)] Real.log := by
    filter_upwards [Ioi_mem_nhds (show c < p y by rw [hc]; linarith)] with t ht
    have h1 : 1 ≤ (t - c / 2) / (c / 2) := by
      rw [le_div_iff₀ (by positivity)]; simp only [Set.mem_Ioi] at ht; linarith
    simp only [hF, hh, Function.comp_apply, Real.smoothTransition.one_of_one_le h1, one_mul]
    ring_nf
  have hgerm : Real.log ∘ p =ᶠ[𝓝 y] F ∘ p :=
    ((hp.continuousAt.tendsto.eventually hFeq).mono fun x hx => hx.symm)
  have hgerm2 : hessC (Real.log ∘ p) y = hessC (F ∘ p) y := by
    unfold hessC
    rw [hgerm.fderiv.fderiv_eq]
  have hd1 : deriv F (p y) = (p y)⁻¹ := by rw [hFeq.deriv_eq, Real.deriv_log]
  have hd2 : deriv (deriv F) (p y) = -((p y) ^ 2)⁻¹ := by
    rw [hFeq.deriv.deriv_eq, Real.deriv_log', deriv_inv]
  rw [hgerm2, MaDensChain.hessC_comp_real F p y hFc hp, hd1, hd2]
end GroundTheory.Heights₂.Heights.MaDensLogPow
