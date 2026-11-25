-- Prove2me | solution 1 for QH.g_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:22.511013+00:00
-- url     : https://prove2.me/submissions/9c632b3b-c42f-433e-bc49-a54a7c8ac732

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmoothedRemainderRealIntegralFormula
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PsiZeroIntegral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HasDerivAtLogSquareAntiderivative
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ShortIntervalImpliesProgressionsStatement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SizeEstimates
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_GIntegral
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_smoothedRemainderIntegralFormula
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_smoothedRemainderRealIntegralFormula
import Theorems.Thm_Formalism_HermitianLattices_GL2a2_log_deriv_series
import Theorems.Thm_Formalism_HermitianLattices_GL2a2_psi_zero_integral_constant
import Theorems.Thm_Formalism_ZeroFreeDirichlet_siegelWalfisz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
section
open Filter Topology ArithmeticFunction MeasureTheory
private lemma dom_integrableOn {a : ℝ} (ha : 1 < a) : IntegrableOn dom (Set.Ioi a) := by
  have key : ∀ x ∈ Set.Ioi a, HasDerivAt (fun t => -(Real.log t)⁻¹) (dom x) x := by
    intro x hx
    have hx1 : 1 < x := lt_trans ha hx
    have hx0 : 0 < x := by linarith
    have hl : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have h : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-x⁻¹ / Real.log x ^ 2)) x :=
      ((Real.hasDerivAt_log hx0.ne').inv hl).neg
    refine h.congr_deriv ?_
    show _ = 1 / (x * Real.log x ^ 2)
    field_simp
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun t => -(Real.log t)⁻¹) (l := 0) ?_ key ?_ ?_
  · exact (((Real.continuousAt_log (by linarith)).inv₀ (Real.log_pos ha).ne').neg).continuousWithinAt
  · intro x hx
    have hx1 : 1 < x := lt_trans ha hx
    have : 0 < Real.log x := Real.log_pos hx1
    show 0 ≤ 1 / (x * Real.log x ^ 2)
    positivity
  · have := Real.tendsto_log_atTop.inv_tendsto_atTop.neg
    simpa using this
private lemma exp_sqrt_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / c ^ 4 / Real.log x ^ 2 := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hs : 0 < c * Real.sqrt (Real.log x) := mul_pos hc (Real.sqrt_pos.mpr hL)
  have h4 : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hL.le]
  have hexp := Real.pow_div_factorial_le_exp _ hs.le 4
  rw [h4] at hexp
  have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  rw [neg_mul, Real.exp_neg, div_div, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  exact hexp
private lemma psi0_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ K x₁ : ℝ, 1 < x₁ ∧ ∀ t : ℝ, x₁ ≤ t → ‖PI.psi0 χ t‖ ≤ K * t / Real.log t ^ 2 := by
  obtain ⟨c, C, hc, hSW⟩ := Formalism.ZeroFreeDirichlet.siegelWalfisz 1 one_pos
  refine ⟨C * (24 / c ^ 4), max 2 (Real.exp N), lt_of_lt_of_le one_lt_two (le_max_left _ _), ?_⟩
  intro t ht
  have h2 : 2 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have hq : (N : ℝ) ≤ Real.log t ^ (1:ℝ) := by
    rw [Real.rpow_one]
    have he := le_trans (le_max_right _ _) ht
    calc (N:ℝ) = Real.log (Real.exp N) := (Real.log_exp _).symm
      _ ≤ Real.log t := Real.log_le_log (Real.exp_pos _) he
  have hb : ‖PI.psi0 χ t‖ ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    have hb0 := hSW N χ t h2 hq
    by_cases hc : χ = 1
    · simpa [PI.psi0, Formalism.ZeroFreeDirichlet.psiChi, hc] using hb0
    · simpa [PI.psi0, Formalism.ZeroFreeDirichlet.psiChi, hc] using hb0
  have he := exp_sqrt_le hc (x := t) (by linarith)
  have hC : 0 ≤ C := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg ht0) (Real.exp_pos (-c * Real.sqrt (Real.log t)))
    linarith [norm_nonneg (PI.psi0 χ t)]
  calc _ ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) := hb
    _ ≤ C * t * (24 / c ^ 4 / Real.log t ^ 2) := mul_le_mul_of_nonneg_left he (mul_nonneg hC ht0.le)
    _ = C * (24 / c ^ 4) * t / Real.log t ^ 2 := by ring
private lemma psi_zero_div_sq_integrable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => PI.psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y) := by
  obtain ⟨K, x₁, hx₁, hK⟩ := psi0_bound χ
  have hX1 : 1 < max x₁ y := lt_of_lt_of_le hx₁ (le_max_left _ _)
  have h1 : Measurable (fun u : ℝ => ∑ n ∈ Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) :=
    (measurable_from_nat (f := fun m : ℕ => ∑ n ∈ Icc 1 m, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N))).comp
      Nat.measurable_floor
  have hm : Measurable (PI.psi0 χ) := by
    by_cases hc : χ = 1
    · have e : PI.psi0 χ = fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) - (u : ℂ) := by
        funext u
        simp [PI.psi0, hc]
      rw [e]
      exact h1.sub Complex.measurable_ofReal
    · have e : PI.psi0 χ = fun u : ℝ => ∑ n ∈ Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N) := by
        funext u
        simp [PI.psi0, hc]
      rw [e]
      exact h1
  have hmeas : Measurable (fun u : ℝ => PI.psi0 χ u / (u : ℂ) ^ 2) :=
    hm.div (Complex.measurable_ofReal.pow_const 2)
  have hsplit : Set.Ioi y ⊆ Set.Ioc y (max x₁ y) ∪ Set.Ioi (max x₁ y) := by
    intro u hu
    by_cases h : u ≤ max x₁ y
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr (lt_of_not_ge h)
  refine IntegrableOn.mono_set ?_ hsplit
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := (∑ n ∈ Icc 1 ⌊max x₁ y⌋₊, vonMangoldt n) + max x₁ y)
      (by simp [Real.volume_Ioc]) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu1 : 1 ≤ u := le_trans hy hu.1.le
    have hsum : ‖∑ n ∈ Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)‖ ≤
        ∑ n ∈ Icc 1 ⌊max x₁ y⌋₊, vonMangoldt n := by
      calc _ ≤ ∑ n ∈ Icc 1 ⌊u⌋₊, ‖((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Icc 1 ⌊u⌋₊, vonMangoldt n := by
          apply Finset.sum_le_sum
          intro n _
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
          exact mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)
        _ ≤ ∑ n ∈ Icc 1 ⌊max x₁ y⌋₊, vonMangoldt n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc_right (Nat.floor_le_floor hu.2)
          · intros
            exact vonMangoldt_nonneg
    have hden : 1 ≤ ‖(u:ℂ)^2‖ := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      nlinarith
    rw [norm_div]
    calc ‖PI.psi0 χ u‖ / ‖(u:ℂ)^2‖ ≤ ‖PI.psi0 χ u‖ := div_le_self (norm_nonneg _) hden
      _ ≤ _ := by
        unfold PI.psi0
        refine (norm_sub_le _ _).trans (add_le_add hsum ?_)
        split_ifs with hc
        · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          exact hu.2
        · rw [norm_zero]
          linarith [le_max_right x₁ y]
  · have hdom := (dom_integrableOn hX1).const_mul K
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu' : x₁ ≤ u := le_trans (le_max_left _ _) (le_of_lt hu)
    have hu1 : 1 < u := lt_of_lt_of_le hx₁ hu'
    have hu0 : 0 < u := by linarith
    have hlog : Real.log u ≠ 0 := (Real.log_pos hu1).ne'
    have hb := hK u hu'
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    calc ‖PI.psi0 χ u‖ / u ^ 2 ≤ (K * u / Real.log u ^ 2) / u ^ 2 :=
          div_le_div_of_nonneg_right hb (by positivity)
      _ = K * dom u := by
          show _ = K * (1 / (u * Real.log u ^ 2))
          field_simp
private lemma gChi_ne {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) (y : ℝ) :
    G0 χ y = Formalism.HermitianLattices.GL2PrimeSums.Gchi (aChi χ) (-(logDerivLAtOne χ)) y := by
  unfold G0
  rw [if_neg h]
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.Gchi Formalism.HermitianLattices.GL2PrimeSums.Gchi aChi
  ring
private lemma gChi_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ = 1) (y : ℝ) :
    G0 χ y = ((Formalism.HermitianLattices.GL2PrimeSums.Gone (fun n => vonMangoldt n) y : ℝ) : ℂ) := by
  unfold G0
  rw [if_pos h]
  rfl
private lemma series_aChi {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) :
    Tendsto (fun M : ℕ => ∑ n ∈ Icc 1 M, aChi χ n / (n : ℂ)) atTop (𝓝 (-(logDerivLAtOne χ))) :=
  Formalism.HermitianLattices.GL2a2.log_deriv_series N χ h
private lemma one_apply_of_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (h : χ = 1)
    (n : ℕ) : χ (n : ZMod N) = 1 := by
  subst h
  have hN : N = 1 := by
    have := hp
    unfold DirichletCharacter.IsPrimitive at this
    rw [DirichletCharacter.conductor_one] at this
    exact this.symm
  subst hN
  exact MulChar.one_apply (isUnit_of_subsingleton _)
private theorem l21a {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) (y : ℝ) (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => PI.psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y) ∧
      G0 χ y = -(y : ℂ) * ∫ u in Set.Ioi y, PI.psi0 χ u / (u : ℂ) ^ 2 := by
  have hint := psi_zero_div_sq_integrable χ y hy
  refine ⟨hint, ?_⟩
  have hlim : Tendsto (fun U => ∫ u in y..U, PI.psi0 χ u / (u:ℂ)^2) atTop
      (𝓝 (∫ u in Set.Ioi y, PI.psi0 χ u / (u:ℂ)^2)) :=
    intervalIntegral_tendsto_integral_Ioi y hint tendsto_id
  by_cases h : χ = 1
  · obtain ⟨I, hI, hG⟩ := Formalism.HermitianLattices.GL2PrimeSums.smoothedRemainderRealIntegralFormula (fun n => vonMangoldt n)
      Formalism.HermitianLattices.GL2a2.psi_zero_integral_constant y hy
    have hone := one_apply_of_primitive hp h
    have hfun : (fun u : ℝ => PI.psi0 χ u / (u:ℂ)^2) =
        fun u => (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => vonMangoldt n) u - u) / u ^ 2 : ℝ) : ℂ) := by
      funext u
      simp only [PI.psi0, if_pos h, hone, mul_one, Formalism.HermitianLattices.GL2PrimeSums.psumR]
      push_cast
      ring
    have hlim2 : Tendsto (fun U => ∫ u in y..U, PI.psi0 χ u / (u:ℂ)^2) atTop (𝓝 (I : ℂ)) := by
      rw [hfun]
      simp_rw [intervalIntegral.integral_ofReal]
      exact (Complex.continuous_ofReal.tendsto _).comp hI
    rw [tendsto_nhds_unique hlim hlim2, gChi_one h, hG]
    push_cast
    ring
  · obtain ⟨I, hI, hG⟩ := Formalism.HermitianLattices.GL2PrimeSums.smoothedRemainderIntegralFormula (aChi χ) (-(logDerivLAtOne χ)) (series_aChi h) y hy
    have hfun : (fun u : ℝ => Formalism.HermitianLattices.GL2PrimeSums.psum (aChi χ) u / (u:ℂ)^2) =
        fun u => PI.psi0 χ u / (u:ℂ)^2 := by
      funext u
      simp [Formalism.HermitianLattices.GL2PrimeSums.psum, PI.psi0, aChi, h]
    rw [hfun] at hI
    rw [tendsto_nhds_unique hlim hI, gChi_ne h, hG]
end
end QH
end

set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ y : ℝ, 1 ≤ y →
      G0 χ y = -(y : ℂ) * ∫ u in Set.Ioi y, PI.psi0 χ u / (u : ℂ) ^ 2 := by
  intro N _ χ hp y hy
  exact (l21a χ hp y hy).2
end QH
