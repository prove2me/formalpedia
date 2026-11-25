-- Prove2me | solution 1 for PositivityTheory.CW.EigenGainPolynomial.fc_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:42.632461+00:00
-- url     : https://prove2.me/submissions/ac1619b1-8e85-4802-925e-29edd5bfe150

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisFormSumOfGain
import Theorems.Thm_PositivityTheory_CW_EigenGainPolynomial_re_inner_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenGainPolynomial
namespace PositivityTheory.CW.EigenGainPolynomial
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (ν k0 k1 k2 k4 : ℝ) (w : V) :
    (inner ℂ w (fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) w)).re =
      k0 * ‖w‖ ^ 2 + k1 * (inner ℂ w (fc b μ (fun x => x - ν) w)).re
        + k2 * ‖fc b μ (fun x => x - ν) w‖ ^ 2
        + k4 * ‖fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) w)‖ ^ 2 := by
  have e1 : ∀ (k : ℝ) (f : ℝ → ℝ), fc b μ (fun x => k * f x) = (k : ℂ) • fc b μ f := by
    intro k f
    calc fc b μ (fun x => k * f x) = fc b μ (fun _ => k) * fc b μ f := hmul (fun _ => k) f
      _ = (k : ℂ) • fc b μ f := by rw [hconst, smul_mul_assoc, one_mul]
  have hT2 : fc b μ (fun x => (x - ν) * (x - ν)) = fc b μ (fun x => x - ν) * fc b μ (fun x => x - ν) :=
    hmul (fun x => x - ν) (fun x => x - ν)
  have hT4 : fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) =
      fc b μ (fun x => (x - ν) * (x - ν)) * fc b μ (fun x => (x - ν) * (x - ν)) :=
    hmul (fun x => (x - ν) * (x - ν)) (fun x => (x - ν) * (x - ν))
  have hF : fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) =
      (k0 : ℂ) • 1 + (k1 : ℂ) • fc b μ (fun x => x - ν) + (k2 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν))
        + (k4 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) := by
    rw [hadd (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν)))
        (fun x => k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))),
      hadd (fun x => k0 + k1 * (x - ν)) (fun x => k2 * ((x - ν) * (x - ν))),
      hadd (fun _ => k0) (fun x => k1 * (x - ν)), hconst,
      e1 k1 (fun x => x - ν), e1 k2 (fun x => (x - ν) * (x - ν)),
      e1 k4 (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν)))]
  rw [hF, hT4, hT2]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply,
    inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul]
  have r2 : ∀ u : V, inner ℂ u (fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) u)) =
      inner ℂ (fc b μ (fun x => x - ν) u) (fc b μ (fun x => x - ν) u) := fun u => (hsym _ _ _).symm
  have r4 := (hsym (fun x => x - ν) w _).symm.trans (r2 (fc b μ (fun x => x - ν) w))
  rw [r4, r2]
  simp only [re_inner_self]
end PositivityTheory.CW.EigenGainPolynomial
