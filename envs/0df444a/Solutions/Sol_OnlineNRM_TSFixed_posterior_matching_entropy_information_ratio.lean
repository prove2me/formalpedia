-- Prove2me | solution 1 for OnlineNRM.TSFixed.posterior_matching_entropy_information_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:31:54.988404+00:00
-- url     : https://prove2.me/submissions/66388b81-0113-47ca-baf5-12fb060b3605
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
import Theorems.Thm_ProbabilityTheory_finite_oracle_covariance_energy_le_entropy_drop
import Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_finite_oracle_experiment
import Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_gap_covariance_identity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N K : ℕ} (hK : 1 ≤ K)
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (xsel : Θ → Fin K → ℝ) (t : ℕ)
    (hθ : Measurable θ) (hθs : ∀ s, Measurable (θs s))
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s))
    (hx : Measurable xsel)
    (hx0 : ∀ ρ k, 0 ≤ xsel ρ k)
    (hx1 : ∀ ρ, ∑ k : Fin K, xsel ρ k ≤ 1)
    (hsample : ∀ C : Set Θ, MeasurableSet C →
      condProb P (pastSigma θ θs A D t) (θs t ⁻¹' C) =ᵐ[P]
        condProb P (histSigma A D t) (θ ⁻¹' C))
    (hoffer : ∀ k : Fin K,
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance) (A t ⁻¹' {some k}) =ᵐ[P]
        fun ω => xsel (θs t ω) k)
    (hdemand : ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance ⊔
          MeasurableSpace.comap (A t) inferInstance) (D t ⁻¹' B) =ᵐ[P]
        fun ω => (demandLaw F (θ ω) (A t ω) B).toReal) :
    (∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
      lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P) ^ 2 ≤
      (pmax p dbar) ^ 2 * (((K : ℝ) + 1) / 2) *
        (finitePosteriorEntropy P (histSigma A D t)
        (fun ω a => oracleActionWeights xsel (θ ω) a) -
          finitePosteriorEntropy P (histSigma A D (t + 1))
        (fun ω a => oracleActionWeights xsel (θ ω) a)) := by
  classical
  let w : Ω → Option (Fin K) → ℝ :=
    fun ω a => oracleActionWeights xsel (θ ω) a
  let r : Ω → Option (Fin K) → ℝ :=
    fun ω a => oracleMeanReward p F (θ ω) a
  let c : Option (Fin K) → ℝ :=
    weightedOracleCovariance P (histSigma A D t) w r
  have hexp := posterior_matching_finite_oracle_experiment hK p dbar hp F hF
    P θ θs A D xsel t hθ hθs hA hD hx hx0 hx1 hsample hoffer hdemand
  have henergy : (∑ a : Option (Fin K), (c a) ^ 2) ≤
      (pmax p dbar) ^ 2 / 2 *
        (finitePosteriorEntropy P (histSigma A D t) w -
          finitePosteriorEntropy P (histSigma A D (t + 1)) w) :=
    finite_oracle_covariance_energy_le_entropy_drop (mΩ := inferInstance) P
      (histSigma A D t) (pastSigma θ θs A D t) (histSigma A D (t + 1))
      w r (A t) (observedPriceReward p (A t) (D t)) (pmax p dbar) hexp
  have hgap := posterior_matching_gap_covariance_identity hK p dbar hp F hF
    P θ θs A D xsel t hθ hθs hA hD hx hx0 hx1 hsample
  rw [hgap]
  change (∑ a : Option (Fin K), c a) ^ 2 ≤
    (pmax p dbar) ^ 2 * (((K : ℝ) + 1) / 2) *
      (finitePosteriorEntropy P (histSigma A D t) w -
        finitePosteriorEntropy P (histSigma A D (t + 1)) w)
  calc
    (∑ a : Option (Fin K), c a) ^ 2 ≤
        (Fintype.card (Option (Fin K)) : ℝ) *
          ∑ a : Option (Fin K), (c a) ^ 2 := by
      simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := c))
    _ ≤ (Fintype.card (Option (Fin K)) : ℝ) *
        ((pmax p dbar) ^ 2 / 2 *
          (finitePosteriorEntropy P (histSigma A D t) w -
            finitePosteriorEntropy P (histSigma A D (t + 1)) w)) :=
      mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg _)
    _ = (pmax p dbar) ^ 2 * (((K : ℝ) + 1) / 2) *
        (finitePosteriorEntropy P (histSigma A D t) w -
          finitePosteriorEntropy P (histSigma A D (t + 1)) w) := by
      simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      ring
