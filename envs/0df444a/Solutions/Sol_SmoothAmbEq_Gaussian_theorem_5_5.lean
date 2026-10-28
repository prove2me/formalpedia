-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.theorem_5_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:08:55.747588+00:00
-- url     : https://prove2.me/submissions/144fcfd6-b27a-44fb-82f1-cdf0ff7b4048
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate
import Theorems.Thm_SmoothAmbEq_Gaussian_step_1_martingale
import Theorems.Thm_SmoothAmbEq_Gaussian_theorem_5_5_equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

open SmoothAmbEq.Gaussian

theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    IsEquilibrium M P W (piStar M c) ∧
    ∀ z : ℝ, ∀ t ∈ Icc 0 M.T, ∀ x β : ℝ, ∀ X : ℝ → Ω → ℝ,
      IsInsideWealth M P W (piStar M c) z t x β X →
        Integrable (fun ω => M.U (X M.T ω)) P ∧ ∫ ω, M.U (X M.T ω) ∂P = gz M c z t x β := by
  refine ⟨theorem_5_5_equilibrium M a ha hα c hc P W hW, ?_⟩
  intro z t ht x β X hX
  obtain ⟨hint, hmeq⟩ := step_1_martingale M a ha hα c hc P W hW z t x β ht X hX
  obtain ⟨-, -, -, -, -, -, -, h1T, h2T, h3T, h4T, h5T, h6T⟩ := hc
  have hTmem : M.T ∈ Icc t M.T := ⟨ht.2, le_rfl⟩
  have htmem : t ∈ Icc t M.T := ⟨le_rfl, ht.2⟩
  -- (5.15): at the horizon the candidate is the utility
  have hterm : (fun ω => gz M c z M.T (X M.T ω) (betaZ M W z t β M.T ω))
      = fun ω => M.U (X M.T ω) := by
    funext ω
    simp [gz, fz, Model.U, h1T, h2T, h3T, h4T, h5T, h6T]
  -- the start: `β^z_t = β` and `X_t = x` a.s.
  have hbeta : ∀ ω, betaZ M W z t β t ω = β := by
    intro ω
    have hz : M.ζ t ≠ 0 := by
      unfold Model.ζ
      have := M.hσ; have := M.hσ₀
      have : 0 < M.σ ^ 2 + t * M.σ₀ ^ 2 := by have := ht.1; positivity
      positivity
    simp only [betaZ, sub_self, mul_zero, zero_div, add_zero]
    field_simp
  obtain ⟨-, -, -, I, hI, hXeq⟩ := hX
  have hI0 : ∀ᵐ ω ∂P, I 0 ω = 0 := by
    obtain ⟨an, -, -, -, hconv⟩ := hI.2 0
    have hzero : (fun n => EthierKurtz.itoStepSum (shiftBM W t) 0 n (an n)) =
        fun _ _ => (0 : ℝ) := by
      funext n ω
      simp [EthierKurtz.itoStepSum]
    rw [hzero] at hconv
    have h0 : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => (0 : ℝ)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
        (ae_of_all _ fun _ => tendsto_const_nhds)
    exact tendstoInMeasure_ae_unique hconv h0
  have hXt : ∀ᵐ ω ∂P, X t ω = x := by
    filter_upwards [hXeq t htmem, hI0] with ω hω hω0
    rw [hω]
    simp [hω0]
  have hstart : (fun ω => gz M c z t (X t ω) (betaZ M W z t β t ω)) =ᵐ[P]
      fun _ => gz M c z t x β := by
    filter_upwards [hXt] with ω hω
    rw [hω, hbeta]
  have hInt := (hint M.T hTmem).1
  simp only at hInt
  rw [hterm] at hInt
  refine ⟨hInt, ?_⟩
  have heq := hmeq t M.T le_rfl ht.2 le_rfl univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at heq
  rw [hterm] at heq
  rw [heq, integral_congr_ae hstart]
  simp
