-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.entire_laplace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:45.423133+00:00
-- url     : https://prove2.me/submissions/6f729878-8496-415c-861a-6fc503836651

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrableRexpLin
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integrable_rexp_lin
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_abs_le_exp_abs
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_exp_abs_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution {ι : Type} [Fintype ι] (c : ℝ) (hc : 0 < c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (ξ : EuclideanSpace ℝ ι) :
    Differentiable ℂ (fun z : ℂ => ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
  intro z₀
  set C : ℝ := SchwartzMap.seminorm ℝ 0 0 h with hC
  have hCb : ∀ u, ‖h u‖ ≤ C := fun u => SchwartzMap.norm_le_seminorm ℝ h u
  set a : ℝ := ‖z₀‖ + 2 with ha
  let bound : EuclideanSpace ℝ ι → ℝ := fun u =>
    C * (Real.exp (-(c * ‖u‖ ^ 2) + a * ⟪ξ, u⟫_ℝ) + Real.exp (-(c * ‖u‖ ^ 2) + (-a) * ⟪ξ, u⟫_ℝ))
  have hbound : Integrable bound :=
    ((integrable_rexp_lin c hc a ξ).add (integrable_rexp_lin c hc (-a) ξ)).const_mul C

  have hest : ∀ u (z : ℂ), ‖z‖ ≤ ‖z₀‖ + 1 →
      ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * (|⟪ξ, u⟫_ℝ| * Real.exp (‖z‖ * |⟪ξ, u⟫_ℝ|)) ≤ bound u := by
    intro u z hz
    set s := ⟪ξ, u⟫_ℝ
    have h1 : |s| * Real.exp (‖z‖ * |s|) ≤ Real.exp (a * |s|) := by
      calc |s| * Real.exp (‖z‖ * |s|) ≤ Real.exp |s| * Real.exp ((‖z₀‖ + 1) * |s|) := by
            gcongr
            · exact abs_le_exp_abs s
          _ = Real.exp (a * |s|) := by rw [← Real.exp_add, ha]; ring_nf
    have h2 := exp_abs_le a s
    have hE : 0 ≤ Real.exp (-(c * ‖u‖ ^ 2)) := (Real.exp_pos _).le
    calc ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * (|s| * Real.exp (‖z‖ * |s|))
        ≤ C * Real.exp (-(c * ‖u‖ ^ 2)) * (Real.exp (a * s) + Real.exp (-(a * s))) := by
          gcongr
          · exact hCb u
          · exact h1.trans h2
      _ = bound u := by
          simp only [bound, Real.exp_add]
          rw [show (-a) * s = -(a * s) by ring]
          ring
  have hnormF' : ∀ u (z : ℂ), ‖h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * (((⟪ξ, u⟫_ℝ : ℝ) : ℂ) *
      Complex.exp (z * ⟪ξ, u⟫_ℝ))‖ ≤ ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * (|⟪ξ, u⟫_ℝ| * Real.exp (‖z‖ * |⟪ξ, u⟫_ℝ|)) := by
    intro u z
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    gcongr
    calc (z * ((⟪ξ, u⟫_ℝ : ℝ) : ℂ)).re = z.re * ⟪ξ, u⟫_ℝ := by simp
      _ ≤ |z.re * ⟪ξ, u⟫_ℝ| := le_abs_self _
      _ = |z.re| * |⟪ξ, u⟫_ℝ| := abs_mul _ _
      _ ≤ ‖z‖ * |⟪ξ, u⟫_ℝ| := by gcongr; exact Complex.abs_re_le_norm z
  have hnormF : ∀ u, ‖h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * Complex.exp (z₀ * ⟪ξ, u⟫_ℝ)‖ ≤ bound u := by
    intro u
    set s := ⟪ξ, u⟫_ℝ
    have e1 : ‖h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * Complex.exp (z₀ * s)‖ ≤
        ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * Real.exp (‖z₀‖ * |s|) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
      gcongr
      calc (z₀ * ((s : ℝ) : ℂ)).re = z₀.re * s := by simp
        _ ≤ |z₀.re * s| := le_abs_self _
        _ = |z₀.re| * |s| := abs_mul _ _
        _ ≤ ‖z₀‖ * |s| := by gcongr; exact Complex.abs_re_le_norm z₀
    refine e1.trans ?_
    have hE : 0 ≤ Real.exp (-(c * ‖u‖ ^ 2)) := (Real.exp_pos _).le
    have h3 : Real.exp (‖z₀‖ * |s|) ≤ Real.exp (a * s) + Real.exp (-(a * s)) :=
      (Real.exp_le_exp.2 (by gcongr; rw [ha]; linarith)).trans (exp_abs_le a s)
    calc ‖h u‖ * Real.exp (-(c * ‖u‖ ^ 2)) * Real.exp (‖z₀‖ * |s|)
        ≤ C * Real.exp (-(c * ‖u‖ ^ 2)) * (Real.exp (a * s) + Real.exp (-(a * s))) := by
          gcongr
          exact hCb u
      _ = bound u := by
          simp only [bound, Real.exp_add]
          rw [show (-a) * s = -(a * s) by ring]
          ring
  have hcont : ∀ z : ℂ, Continuous (fun u : EuclideanSpace ℝ ι =>
      h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
    intro z
    have : Continuous (fun u : EuclideanSpace ℝ ι => ⟪ξ, u⟫_ℝ) := continuous_const.inner continuous_id
    fun_prop
  have hcont' : Continuous (fun u : EuclideanSpace ℝ ι =>
      h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * (((⟪ξ, u⟫_ℝ : ℝ) : ℂ) * Complex.exp (z₀ * ⟪ξ, u⟫_ℝ))) := by
    have : Continuous (fun u : EuclideanSpace ℝ ι => ⟪ξ, u⟫_ℝ) := continuous_const.inner continuous_id
    fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (z : ℂ) (u : EuclideanSpace ℝ ι) => h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * Complex.exp (z * ⟪ξ, u⟫_ℝ))
    (F' := fun (z : ℂ) (u : EuclideanSpace ℝ ι) =>
      h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) * (((⟪ξ, u⟫_ℝ : ℝ) : ℂ) * Complex.exp (z * ⟪ξ, u⟫_ℝ)))
    (x₀ := z₀) (bound := bound) (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable)
    (hbound.mono' (hcont z₀).aestronglyMeasurable (Filter.Eventually.of_forall hnormF))
    hcont'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u z hz => (hnormF' u z).trans (hest u z (by
      have := Metric.mem_ball.1 hz
      have h1 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      rw [dist_eq_norm] at this
      linarith)))
    hbound
    (Filter.Eventually.of_forall fun u z _ => by
      have hd : HasDerivAt (fun z : ℂ => Complex.exp (z * ⟪ξ, u⟫_ℝ))
          (Complex.exp (z * ⟪ξ, u⟫_ℝ) * (1 * ((⟪ξ, u⟫_ℝ : ℝ) : ℂ))) z :=
        ((hasDerivAt_id z).mul_const _).cexp
      refine (hd.const_mul (h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ))).congr_deriv ?_
      ring)
  exact key.2.differentiableAt
end PositivityTheory.SiegelWeilFormula.KFPB
