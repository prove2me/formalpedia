-- Prove2me | solution 1 for SocialManip.Beliefs.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:07:45.70179+00:00
-- url     : https://prove2.me/submissions/265c3654-4877-4348-88d5-b876f46dfa34

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Theorems.Thm_SocialManip_Beliefs_BU_converges_ae
import Theorems.Thm_SocialManip_Beliefs_belief_recursion_limit

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open SocialManip.Beliefs

theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Finset (Fin n)) (θ : Fin n → ℝ) (α : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ) (q lam lamStar : ℝ) (y yhat y' : State) (x : Fin n → Bool)
    (hq : 0 < q ∧ q < 1) (hp : ∀ i, 1 / 2 ≤ p i ∧ p i < 1)
    (hlam : 0 < lam) (hlamStar : 0 < lamStar)
    (hθ : ∀ i ∉ B, 0 ≤ θ i) (hα : ∀ i ∉ B, ∀ j, 0 ≤ α i j)
    (hrow : ∀ i ∉ B, θ i + ∑ j, α i j = 1)
    (s : Fin n → ℕ → Ω → State) (hsm : ∀ i τ, Measurable (s i τ))
    (hind : ∀ i, iIndepFun (fun τ => s i τ) P)
    (hlaw : ∀ i τ, P {ω | s i τ ω = State.S} =
      ENNReal.ofReal (signalProbS (p i) lam lamStar y yhat (x i)))
    (hA1i : ∀ i, p i < (lamStar + lam) / (2 * lam))
    (adj : Fin n → Fin n → Prop) (hadj : ∀ i ∉ B, ∀ j, adj i j ↔ 0 < α i j)
    (hA1ii : ∀ i j, i ≠ j → Relation.TransGen adj i j)
    (hA1iii : ∀ i ∉ B, (0 < θ i ↔ 1 / 2 < p i))
    (hA1iv : ∃ i, 1 / 2 < p i) :
    ∃ c : Fin n → ℝ, ∀ᵐ ω ∂P,
      (∀ i, i ∉ B → Tendsto (fun t => BU (p i) q (fun τ => s i τ ω) t y') atTop (𝓝 (c i))) ∧
      ∀ π₀ : Fin n → ℝ, (∀ i ∉ B, 0 ≤ π₀ i ∧ π₀ i ≤ 1) →
        Tendsto (fun t => belief B θ α p q (fun i τ => s i τ ω) y y' π₀ t) atTop
          (𝓝 ((1 - W B α)⁻¹ *ᵥ fun i => thetaVec B θ i * (if i ∈ B then truth y y' else c i))) := by
  have hBU : ∀ i, ∃ c : ℝ, ∀ᵐ ω ∂P,
      Tendsto (fun t => BU (p i) q (fun τ => s i τ ω) t y') atTop (𝓝 c) := fun i =>
    BU_converges_ae P (p i) q lam lamStar y yhat y' (x i) hq (hp i) hlam hlamStar (hA1i i)
      (fun τ => s i τ) (hsm i) (hind i) (hlaw i)
  choose c hc using hBU
  refine ⟨c, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i,
      Tendsto (fun t => BU (p i) q (fun τ => s i τ ω) t y') atTop (𝓝 (c i)) :=
    ae_all_iff.mpr hc
  filter_upwards [hall] with ω hω
  refine ⟨fun i _ => hω i, fun π₀ _ => ?_⟩
  set u : ℕ → Fin n → ℝ := fun t i =>
    if i ∈ B then truth y y' else θ i * BU (p i) q (fun τ => s i τ ω) t y' with hu
  set uInf : Fin n → ℝ := fun i => thetaVec B θ i * (if i ∈ B then truth y y' else c i)
    with huInf
  have hlimu : Tendsto u atTop (𝓝 uInf) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hi : i ∈ B
    · simp only [hu, huInf, thetaVec, hi, if_true, one_mul]
      exact tendsto_const_nhds
    · simp only [hu, huInf, thetaVec, hi, if_false]
      exact (hω i).const_mul (θ i)
  have hrec : ∀ t, belief B θ α p q (fun i τ => s i τ ω) y y' π₀ (t + 1) =
      u (t + 1) + W B α *ᵥ belief B θ α p q (fun i τ => s i τ ω) y y' π₀ t := by
    intro t
    funext i
    by_cases hi : i ∈ B
    · simp [belief, hu, hi, Matrix.mulVec, dotProduct, W]
    · simp [belief, hu, hi, Matrix.mulVec, dotProduct, W]
  obtain ⟨πInf, hlim, _, hπInf⟩ := belief_recursion_limit B θ α p hp hθ hα hrow adj hadj
    hA1ii hA1iii hA1iv u uInf hlimu _ hrec
  rw [hπInf] at hlim
  exact hlim
