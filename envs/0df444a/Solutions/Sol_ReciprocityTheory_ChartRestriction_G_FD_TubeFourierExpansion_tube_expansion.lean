-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.tube_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:03:34.694318+00:00
-- url     : https://prove2.me/submissions/b2e8165d-2bd3-46ae-88c0-7d9fd8fe6f7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeFourierExpansion_fourCoeff_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeFourierExpansion_mul_sign_abs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeFourierExpansion_abs_sign_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeSummability_summable_exp_abs
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_four_bound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_four_indep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_four_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
open Complex MeasureTheory Metric ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
theorem _root_.solution (Ω : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (h0 : (0 : Fin n → ℝ) ∈ Ω) (hd : DifferentiableOn ℂ h (tube n Ω))
    (hp : ∀ s ∈ tube n Ω, ∀ m : Fin n → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (u : Fin n → ℂ) (hu : u ∈ tube n Ω) :
    Summable (fun k : Fin n → ℤ =>
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖) ∧
    HasSum (fun k : Fin n → ℤ => fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j))
      (h u) := by
  classical
  obtain ⟨x0, y0, hux, hy0Ω⟩ : ∃ x0 y0 : Fin n → ℝ,
      (∀ j, u j = (x0 j : ℂ) + (y0 j : ℂ) * I) ∧ y0 ∈ Ω :=
    ⟨fun j => (u j).re, fun j => (u j).im, fun j => (Complex.re_add_im (u j)).symm, hu⟩
  have hpre : IsPreconnected Ω := hc.isPreconnected

  have hind : ∀ b ∈ Ω, ∀ k, fourCoeff h 0 k = fourCoeff h b k :=
    fun b hb k => four_indep n Ω h hΩ hpre hd hp 0 h0 b hb k
  have htube : ∀ x b : Fin n → ℝ, b ∈ Ω → (fun j => (x j : ℂ) + (b j : ℂ) * I) ∈ tube n Ω := by
    intro x b hb
    simp only [tube, Set.mem_setOf_eq]
    simpa using hb

  have hslice : ∀ b ∈ Ω, ∃ C, ∀ x : Fin n → ℝ, ‖h (fun j => (x j : ℂ) + (b j : ℂ) * I)‖ ≤ C := by
    intro b hb
    have hcont : ContinuousOn (fun x : Fin n → ℝ => h (fun j => (x j : ℂ) + (b j : ℂ) * I))
        (Set.Icc 0 1) := by
      refine hd.continuousOn.comp (Continuous.continuousOn ?_) (fun x _ => htube x b hb)
      exact continuous_pi fun j => (Complex.continuous_ofReal.comp (continuous_apply j)).add
        continuous_const
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine ⟨C, fun x => ?_⟩
    have hxm : (fun j => x j - (⌊x j⌋ : ℝ)) ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := Int.floor_le (x j)
        show (0 : ℝ) ≤ x j - (⌊x j⌋ : ℝ)
        linarith
      · have := Int.lt_floor_add_one (x j)
        show x j - (⌊x j⌋ : ℝ) ≤ 1
        linarith
    have hper := hp _ (htube (fun j => x j - (⌊x j⌋ : ℝ)) b hb) (fun j => ⌊x j⌋)
    have heq : ((fun j => (((x j - (⌊x j⌋ : ℝ)) : ℝ) : ℂ) + (b j : ℂ) * I) +
        fun j => ((⌊x j⌋ : ℤ) : ℂ)) = fun j => (x j : ℂ) + (b j : ℂ) * I := by
      funext j
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [heq] at hper
    rw [hper]
    exact hC _ hxm

  have hcoef : ∀ b ∈ Ω, ∃ C, ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k‖ ≤ C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) := by
    intro b hb
    obtain ⟨C, hC⟩ := hslice b hb
    refine ⟨C, fun k => ?_⟩
    have hB := four_bound n h b k C hC
    rw [hind b hb k]
    have hmul : Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * b j) *
        Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      congr 1
      ring
    calc ‖fourCoeff h b k‖
        = ‖fourCoeff h b k‖ * Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * b j) *
            Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) := by rw [mul_assoc, hmul, mul_one]
      _ ≤ C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) :=
          mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le

  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ y0 hy0Ω
  have hbσ : ∀ k : Fin n → ℤ, (fun j => y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) ∈ Ω := by
    intro k
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    rw [Real.dist_eq, show y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ) - y0 j =
      -(ε / 2 * (((k j).sign : ℤ) : ℝ)) by ring, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < ε / 2)]
    have := abs_sign_le (k j)
    nlinarith
  have hcoefσ : ∀ σ : Fin n → ℤ, ∃ C, 0 ≤ C ∧
      ((fun j => y0 j - ε / 2 * ((σ j : ℤ) : ℝ)) ∈ Ω → ∀ k : Fin n → ℤ,
        ‖fourCoeff h 0 k‖ ≤
          C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * (y0 j - ε / 2 * ((σ j : ℤ) : ℝ)))) := by
    intro σ
    by_cases hσ : (fun j => y0 j - ε / 2 * ((σ j : ℤ) : ℝ)) ∈ Ω
    · obtain ⟨C, hC⟩ := hcoef _ hσ
      exact ⟨max C 0, le_max_right _ _, fun _ k =>
        (hC k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hσ⟩
  choose Cf hCf0 hCf using hcoefσ
  have hsignS : ∀ k : Fin n → ℤ,
      (fun j => (k j).sign) ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)) := by
    intro k
    rw [Fintype.mem_piFinset]
    intro j
    rcases Int.sign_trichotomy (k j) with h' | h' | h' <;> simp [h']
  have hCK : ∀ k : Fin n → ℤ, Cf (fun j => (k j).sign) ≤
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)), Cf σ :=
    fun k => Finset.single_le_sum (fun σ _ => hCf0 σ) (hsignS k)
  have hexpo : ∀ k : Fin n → ℤ,
      2 * Real.pi * ∑ j, (k j : ℝ) * (y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) +
        -2 * Real.pi * ∑ j, (k j : ℝ) * y0 j = -(Real.pi * ε) * ∑ j, |(k j : ℝ)| := by
    intro k
    have e : ∑ j, (k j : ℝ) * (y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) =
        ∑ j, (k j : ℝ) * y0 j - ε / 2 * ∑ j, |(k j : ℝ)| := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_sign_abs (k j)]
      ring
    rw [e]
    ring

  have hsumu : ∀ k : Fin n → ℤ, ∑ j, (k j : ℂ) * u j =
      ((∑ j, (k j : ℝ) * x0 j : ℝ) : ℂ) + ((∑ j, (k j : ℝ) * y0 j : ℝ) : ℂ) * I := by
    intro k
    simp only [hux]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hexpu : ∀ A B : ℝ, cexp (2 * Real.pi * I * ((A : ℂ) + (B : ℂ) * I)) =
      ((Real.exp (-2 * Real.pi * B) : ℝ) : ℂ) * cexp (((2 * Real.pi * A : ℝ) : ℂ) * I) := by
    intro A B
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * B) * Complex.I_sq
  have hterm : ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖ =
        ‖fourCoeff h 0 k‖ * Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) := by
    intro k
    rw [hsumu k, hexpu, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hbound : ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖ ≤
        (∑ σ ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)), Cf σ) *
          Real.exp (-(Real.pi * ε) * ∑ j, |(k j : ℝ)|) := by
    intro k
    rw [hterm k]
    refine le_trans (mul_le_mul_of_nonneg_right (hCf _ (hbσ k) k) (Real.exp_pos _).le) ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul (hCK k) (le_of_eq ?_) (Real.exp_pos _).le (le_trans (hCf0 _) (hCK k))
    congr 1
    exact hexpo k
  have hsumm : Summable (fun k : Fin n → ℤ =>
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound
      ((summable_exp_abs (Real.pi * ε) (by positivity) n).mul_left _)
  refine ⟨hsumm, ?_⟩

  have hΩ'o : IsOpen ((fun b => b + y0) ⁻¹' Ω) := hΩ.preimage (continuous_id.add continuous_const)
  have h0' : (0 : Fin n → ℝ) ∈ (fun b => b + y0) ⁻¹' Ω := by simpa using hy0Ω
  have hmaps : ∀ t ∈ tube n ((fun b => b + y0) ⁻¹' Ω),
      t + (fun j => (y0 j : ℂ) * I) ∈ tube n Ω := by
    intro t ht
    simp only [tube, Set.mem_setOf_eq, Set.mem_preimage] at ht ⊢
    convert ht using 1
    funext j
    simp
  have hdg : DifferentiableOn ℂ (fun t => h (t + fun j => (y0 j : ℂ) * I))
      (tube n ((fun b => b + y0) ⁻¹' Ω)) :=
    hd.comp (differentiable_id.add_const _).differentiableOn (fun t ht => hmaps t ht)
  have hpg : ∀ s ∈ tube n ((fun b => b + y0) ⁻¹' Ω), ∀ m : Fin n → ℤ,
      h (s + (fun k => (m k : ℂ)) + fun j => (y0 j : ℂ) * I) = h (s + fun j => (y0 j : ℂ) * I) := by
    intro s hs m
    rw [add_right_comm]
    exact hp _ (hmaps s hs) m
  have hcoefg : ∀ k, fourCoeff (fun t => h (t + fun j => (y0 j : ℂ) * I)) 0 k =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * fourCoeff h 0 k := by
    intro k
    rw [fourCoeff_shift h y0 k, hind y0 hy0Ω k]
  have hsummg : Summable (fun k => ‖fourCoeff (fun t => h (t + fun j => (y0 j : ℂ) * I)) 0 k‖) := by
    refine hsumm.congr (fun k => ?_)
    rw [hterm k, hcoefg k, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      mul_comm]
  have hs := four_sum n ((fun b => b + y0) ⁻¹' Ω) (fun t => h (t + fun j => (y0 j : ℂ) * I))
    hΩ'o hdg hpg h0' hsummg x0
  convert hs using 1
  · funext k
    rw [hcoefg k, hsumu k, hexpu]
    have e : ((2 * Real.pi * (∑ j, (k j : ℝ) * x0 j) : ℝ) : ℂ) * I =
        2 * Real.pi * I * ∑ j, (k j : ℂ) * (x0 j : ℂ) := by
      push_cast
      ring
    rw [e]
    ring
  · show h u = h ((fun k => (x0 k : ℂ)) + fun j => (y0 j : ℂ) * I)
    congr 1
    funext j
    rw [hux j]
    rfl
end ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
