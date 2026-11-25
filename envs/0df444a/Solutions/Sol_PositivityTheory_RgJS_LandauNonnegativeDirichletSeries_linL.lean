-- Prove2me | solution 1 for PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.linL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:55.05212+00:00
-- url     : https://prove2.me/submissions/d7f35e32-a3ac-4c51-950f-28b08289bf7e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL
import Theorems.Thm_PositivityTheory_RgJS_LandauNonnegativeDirichletSeries_hasSum_iteratedDeriv
import Theorems.Thm_PositivityTheory_RgJS_LandauNonnegativeDirichletSeries_propagate
import Theorems.Thm_PositivityTheory_RgJS_LandauNonnegativeDirichletSeries_re_neg_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
namespace PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
theorem _root_.solution (I : Type) (c l : I → ℝ) (σ₀ σ₁ : ℝ) (F : ℂ → ℂ) (hc : ∀ i, 0 ≤ c i) (hl : ∀ i, 0 ≤ l i)
    (hF : ∀ σ : ℝ, σ₀ < σ → AnalyticAt ℂ F σ)
    (hS : ∀ σ : ℝ, σ₁ < σ → Summable fun i => c i * Real.exp (-(l i * σ)))
    (hE : ∀ σ : ℝ, σ₁ < σ → F σ = ∑' i, ((c i * Real.exp (-(l i * σ)) : ℝ) : ℂ)) :
    ∀ σ : ℝ, σ₀ < σ → Summable fun i => c i * Real.exp (-(l i * σ)) := by
  have mono : ∀ σ τ : ℝ, σ ≤ τ → Summable (fun i => c i * Real.exp (-(l i * σ))) →
      Summable fun i => c i * Real.exp (-(l i * τ)) :=
    fun σ τ h hs => hs.of_nonneg_of_le (fun i => mul_nonneg (hc i) (Real.exp_pos _).le)
      (fun i => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (hc i))
  intro σ hσ
  by_contra hns
  set A := {τ : ℝ | σ₀ < τ ∧ Summable fun i => c i * Real.exp (-(l i * τ))} with hA
  have hAne : (max σ₀ σ₁ + 1) ∈ A :=
    ⟨by linarith [le_max_left σ₀ σ₁], hS _ (by linarith [le_max_right σ₀ σ₁])⟩
  have hAbdd : BddBelow A := ⟨σ₀, fun τ hτ => hτ.1.le⟩
  set β := sInf A with hβdef
  have hβσ : σ ≤ β := le_csInf ⟨_, hAne⟩ fun τ hτ => by
    by_contra h
    push_neg at h
    exact hns (mono τ σ h.le hτ.2)
  have hβ0 : σ₀ < β := lt_of_lt_of_le hσ hβσ
  obtain ⟨r, hr, hFr⟩ := (hF β hβ0).exists_ball_analyticOnNhd
  set ε := min (r / 4) ((β - σ₀) / 2) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεr : ε ≤ r / 4 := min_le_left _ _
  have hεβ : ε ≤ (β - σ₀) / 2 := min_le_right _ _
  set s0 : ℝ := β + ε with hs0
  obtain ⟨β', hβ'A, hβ's⟩ := exists_lt_of_csInf_lt ⟨_, hAne⟩ (show β < s0 by linarith)
  have hββ' : β ≤ β' := csInf_le hAbdd hβ'A
  set G : ℂ → ℂ := fun s => ∑' i, (c i : ℂ) * Complex.exp (-(l i : ℂ) * s) with hG
  have hbd : ∀ i (s : ℂ), β' < s.re → ‖(c i : ℂ) * Complex.exp (-(l i : ℂ) * s)‖ ≤ c i * Real.exp (-(l i * β')) := by
    intro i s hs
    rw [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg (hc i), re_neg_mul]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (hc i)
  have hGsum : ∀ s : ℂ, β' < s.re → HasSum (fun i => (c i : ℂ) * Complex.exp (-(l i : ℂ) * s)) (G s) :=
    fun s hs => (Summable.of_norm (hβ'A.2.of_nonneg_of_le (fun i => norm_nonneg _) fun i => hbd i s hs)).hasSum
  have hU : IsOpen {s : ℂ | β' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGd : DifferentiableOn ℂ G {s : ℂ | β' < s.re} :=
    differentiableOn_tsum_of_summable_norm hβ'A.2 (fun i => by fun_prop) hU (fun i w hw => hbd i w hw)
  have hGa : ∀ τ : ℝ, β' < τ → AnalyticAt ℂ G τ := fun τ hτ =>
    hGd.analyticAt (hU.mem_nhds (by simpa using hτ))
  have hFG : ∀ τ : ℝ, σ₁ < τ → F τ = G τ := by
    intro τ hτ
    rw [hE τ hτ, hG]
    congr 1
    funext i
    push_cast
    ring_nf
  have hev : F =ᶠ[𝓝 ((s0 : ℝ) : ℂ)] G :=
    propagate F G β' σ₁ (fun τ hτ => hF τ (by linarith)) hGa hFG s0 hβ's
  have hFd : DifferentiableOn ℂ F (Metric.ball ((s0 : ℝ) : ℂ) (3 * r / 4)) := by
    intro w hw
    refine (hFr w ?_).differentiableAt.differentiableWithinAt
    rw [Metric.mem_ball] at hw ⊢
    have : dist w (β : ℂ) ≤ dist w ((s0 : ℝ) : ℂ) + dist ((s0 : ℝ) : ℂ) (β : ℂ) := dist_triangle _ _ _
    have h2 : dist ((s0 : ℝ) : ℂ) (β : ℂ) = ε := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hs0]
      rw [show β + ε - β = ε by ring, abs_of_pos hε]
    linarith
  set z : ℝ := β - ε with hz
  have hzb : ((z : ℝ) : ℂ) ∈ Metric.ball ((s0 : ℝ) : ℂ) (3 * r / 4) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hz, hs0,
      show β - ε - (β + ε) = -(2 * ε) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hT := Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball hFd hzb)
  have hder : ∀ n : ℕ, HasSum (fun i => (c i : ℂ) * (-(l i : ℂ)) ^ n * Complex.exp (-(l i : ℂ) * ((s0 : ℝ) : ℂ)))
      (iteratedDeriv n F ((s0 : ℝ) : ℂ)) := by
    intro n
    rw [hev.iteratedDeriv_eq n]
    exact hasSum_iteratedDeriv c l G hc hl β' hGsum n _ (by simpa using hβ's)
  have hj : ∀ i, HasSum (fun n : ℕ => c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial))
      (c i * Real.exp (-(l i * z))) := by
    intro i
    have h1 := (NormedSpace.expSeries_div_hasSum_exp (2 * ε * l i)).mul_left (c i * Real.exp (-(l i * s0)))
    rw [← Real.exp_eq_exp_ℝ] at h1
    have e : c i * Real.exp (-(l i * z)) = c i * Real.exp (-(l i * s0)) * Real.exp (2 * ε * l i) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      rw [hz, hs0]; ring
    rw [e]
    exact h1
  have hzA : Summable fun i => c i * Real.exp (-(l i * z)) := by
    refine summable_of_sum_le (fun i => mul_nonneg (hc i) (Real.exp_pos _).le) (c := (F z).re) (fun S => ?_)
    refine hasSum_le (fun n => ?_) (hasSum_sum (fun i _ => hj i)) hT
    have h2 := Complex.hasSum_re ((hder n).mul_left ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n))
    have e : ∀ i, ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n *
        ((c i : ℂ) * (-(l i : ℂ)) ^ n * Complex.exp (-(l i : ℂ) * ((s0 : ℝ) : ℂ)))).re =
        c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial) := by
      intro i
      rw [← Complex.ofReal_re (c i * Real.exp (-(l i * s0)) * ((2 * ε * l i) ^ n / n.factorial))]
      congr 1
      have hzs : ((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ) = ((-(2 * ε) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_sub, hz, hs0]; congr 1; ring
      rw [hzs]
      push_cast
      have : ((-(2 * (ε : ℂ))) ^ n) * (-(l i : ℂ)) ^ n = (2 * (ε : ℂ) * (l i : ℂ)) ^ n := by
        rw [← mul_pow]; congr 1; ring
      rw [show Complex.exp (-(l i : ℂ) * (s0 : ℂ)) = Complex.exp (-((l i : ℂ) * (s0 : ℂ))) by ring_nf]
      linear_combination (↑(n.factorial : ℕ) : ℂ)⁻¹ * (c i : ℂ) * Complex.exp (-((l i : ℂ) * (s0 : ℂ))) * this
    simp only [e] at h2
    have h4 := sum_le_hasSum S (fun i _ => by have := hc i; have := hl i; positivity) h2
    have e2 : (((n.factorial : ℂ)⁻¹ • (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n • iteratedDeriv n F ((s0 : ℝ) : ℂ))).re =
        ((n.factorial : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((s0 : ℝ) : ℂ)) ^ n * iteratedDeriv n F ((s0 : ℝ) : ℂ)).re := by
      simp only [smul_eq_mul, mul_assoc]
    rw [e2]
    exact h4
  have hzA' : z ∈ A := ⟨by linarith, hzA⟩
  have := csInf_le hAbdd hzA'
  linarith
end PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
