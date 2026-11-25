-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.rot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:51.903201+00:00
-- url     : https://prove2.me/submissions/dc763a9e-60a2-45ad-9299-6ce62c05a98a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousGramX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_map_smul_volume
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_evX_smul_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_gs_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_gramX_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_continuous_gramX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_continuous_evX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_continuous_gs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution : Rot := by
  intro m n ε c t hc b hb d hd hd0
  set N := d.sum fun _ e => e with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hd0
    ext k
    have := (Finset.sum_eq_zero_iff.mp h) k
    by_cases hk : k ∈ d.support
    · simpa using this hk
    · simpa using hk
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  set ζ : ℂ := Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) with hζdef
  have hζ : ‖ζ‖ = 1 := by rw [hζdef, Complex.norm_exp_ofReal_mul_I]
  have hζN : ζ ^ N = -1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (((Real.pi / N : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  let F : (Fin m → Fin n → ℂ) → ℂ := fun x =>
    evX (monomial d 1) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
  have hcont : Continuous F :=
    ((GI.continuous_evX _).mul (GI.continuous_gs c)).mul (Complex.continuous_exp.comp
      (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace)))
  have hcomp : (fun x => F (ζ • x)) = fun x => ζ ^ N * F x := by
    funext x
    simp only [F, evX_smul_mono ζ d hd, gs_smul c ζ hζ, gramX_smul ε ζ hζ]
    ring
  have hint : ∫ x, F (ζ • x) = ∫ x, F x := by
    rw [← integral_map (μ := volume) (φ := fun x : Fin m → Fin n → ℂ => ζ • x)
      (continuous_const_smul ζ).measurable.aemeasurable
      (by rw [map_smul_volume ζ hζ]; exact hcont.aestronglyMeasurable), map_smul_volume ζ hζ]
  have h2 : ∫ x, F x = -∫ x, F x := by
    conv_lhs => rw [← hint, hcomp, integral_const_mul, hζN, neg_one_mul]
  show ∫ x, F x = 0
  linear_combination (1 / 2 : ℂ) * h2
end PositivityTheory.Rg.Sw.WR.G
