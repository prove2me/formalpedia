-- Prove2me | solution 1 for RLPBidPrice.Unbiased.lemma1_glasserman
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T09:30:44.269872+00:00
-- url     : https://prove2.me/submissions/8ebd8088-8d1d-4d6c-ba65-5aa8be05e95f

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open MeasureTheory Matrix Filter Topology

open RLPBidPrice.Unbiased in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ → Ω → ℝ) (θ₀ : ℝ)
    (hmeas : ∀ θ, AEStronglyMeasurable (X θ) P)
    (hint : Integrable (X θ₀) P)
    (K : ℝ) (hK : 0 ≤ K)
    (hlip : ∀ ω θ h, 0 ≤ h → |X (θ + h) ω - X θ ω| ≤ K * h)
    (hdiff : ∀ᵐ ω ∂P, DifferentiableAt ℝ (fun θ => X θ ω) θ₀) :
    HasDerivAt (fun θ => ∫ ω, X θ ω ∂P) (∫ ω, deriv (fun θ => X θ ω) θ₀ ∂P) θ₀ := by
  -- two-sided Lipschitz bound
  have hlip2 : ∀ ω a b, dist (X a ω) (X b ω) ≤ K * dist a b := by
    intro ω a b
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total a b with hab | hab
    · have := hlip ω a (b - a) (by linarith)
      rw [add_sub_cancel] at this
      rw [abs_sub_comm, abs_of_nonpos (by linarith : a - b ≤ 0)]
      linarith
    · have := hlip ω b (a - b) (by linarith)
      rw [add_sub_cancel] at this
      rw [abs_of_nonneg (by linarith : 0 ≤ a - b)]
      exact this
  have hL : ∀ ω, LipschitzOnWith (Real.nnabs K) (fun θ => X θ ω) Set.univ := by
    intro ω
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have : ((Real.nnabs K : NNReal) : ℝ) = K := by simp [abs_of_nonneg hK]
    rw [this]; exact hlip2 ω a b
  -- measurability of the pathwise derivative, as an a.e. limit of difference quotients
  set u : ℕ → ℝ := fun k => θ₀ + 1 / ((k : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝[≠] θ₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add θ₀
      simpa [u] using this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u]
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hF'_meas : AEStronglyMeasurable (fun ω => deriv (fun θ => X θ ω) θ₀) P := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun k ω => slope (fun θ => X θ ω) θ₀ (u k)) (fun k => ?_) ?_
    · show AEStronglyMeasurable (fun ω => (u k - θ₀)⁻¹ • (X (u k) ω - X θ₀ ω)) P
      exact ((hmeas (u k)).sub (hmeas θ₀)).const_smul ((u k - θ₀)⁻¹ : ℝ)
    · filter_upwards [hdiff] with ω hω
      exact (hasDerivAt_iff_tendsto_slope.mp hω.hasDerivAt).comp hu
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := P) (F := X) (x₀ := θ₀)
    (bound := fun _ => K) Filter.univ_mem (Eventually.of_forall hmeas) hint hF'_meas
    (Eventually.of_forall hL) (integrable_const K)
    (hdiff.mono fun ω hω => hω.hasDerivAt)
  exact key.2
