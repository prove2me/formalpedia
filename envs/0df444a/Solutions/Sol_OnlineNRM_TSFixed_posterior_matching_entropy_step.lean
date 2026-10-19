-- Prove2me | solution 1 for OnlineNRM.TSFixed.posterior_matching_entropy_step
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T15:01:13.950355+00:00
-- url     : https://prove2.me/submissions/33f2750b-22ad-44df-8a77-98a73c2d3aba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
import Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_entropy_monotone
import Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_entropy_information_ratio

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
    0 ≤ (finitePosteriorEntropy P (histSigma A D t)
        (fun ω a => oracleActionWeights xsel (θ ω) a) -
      finitePosteriorEntropy P (histSigma A D (t + 1))
        (fun ω a => oracleActionWeights xsel (θ ω) a)) ∧
    (∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
      lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P) ^ 2 ≤
      (pmax p dbar) ^ 2 * (((K : ℝ) + 1) / 2) *
        (finitePosteriorEntropy P (histSigma A D t)
        (fun ω a => oracleActionWeights xsel (θ ω) a) -
          finitePosteriorEntropy P (histSigma A D (t + 1))
            (fun ω a => oracleActionWeights xsel (θ ω) a)) := by
  constructor
  · exact OnlineNRM.TSFixed.posterior_matching_entropy_monotone
      (P := P) (θ := θ) (A := A) (D := D) (xsel := xsel) (t := t)
      hθ hx hx0 hx1
  · exact OnlineNRM.TSFixed.posterior_matching_entropy_information_ratio
      (hK := hK) (p := p) (dbar := dbar) (hp := hp)
      (F := F) (hF := hF) (P := P) (θ := θ) (θs := θs)
      (A := A) (D := D) (xsel := xsel) (t := t)
      (hθ := hθ) (hθs := hθs) (hA := hA) (hD := hD)
      (hx := hx) (hx0 := hx0) (hx1 := hx1)
      (hsample := hsample) (hoffer := hoffer) (hdemand := hdemand)