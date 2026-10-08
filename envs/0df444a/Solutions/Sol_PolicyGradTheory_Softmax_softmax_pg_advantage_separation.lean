-- Prove2me | solution 1 for PolicyGradTheory.Softmax.softmax_pg_advantage_separation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:25:16.568932+00:00
-- url     : https://prove2.me/submissions/39c17a86-e53d-46d9-bb00-f3da2f35ec9d

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm

set_option autoImplicit false

open FoundationsML.ReinforcementLearning Filter Topology PolicyGradTheory.Softmax in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hηle : η ≤ (1 - γ) ^ 2 / 5)
    (Vinf : S → ℝ) (Qinf : S → A → ℝ)
    (hV : ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 (Vinf s)))
    (hQ : ∀ s a, Tendsto (fun t => QFunction (softmaxPolicy (θ t)) P r γ s a) atTop (𝓝 (Qinf s a)))
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔle : ∀ s a, Qinf s a ≠ Vinf s → Δ ≤ |Qinf s a - Vinf s|) :
    ∃ T1 : ℕ, ∀ t, T1 < t → ∀ s a,
      (Qinf s a < Vinf s → PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a < -(Δ / 4)) ∧
      (Vinf s < Qinf s a → Δ / 4 < PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a) := by
  have hlim : ∀ s a, Tendsto (fun t => PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a)
      atTop (𝓝 (Qinf s a - Vinf s)) := fun s a => by
    unfold PolicyGradTheory.ProjGA.advantage
    exact (hQ s a).sub (hV s)
  have hev : ∀ᶠ t in atTop, ∀ s a,
      |PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a - (Qinf s a - Vinf s)| < Δ / 4 := by
    rw [eventually_all]; intro s; rw [eventually_all]; intro a
    exact ((Metric.tendsto_nhds.mp (hlim s a)) (Δ / 4) (by positivity)).mono
      (fun t ht => by rwa [Real.dist_eq] at ht)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun t ht s a => ?_⟩
  have h := hN t ht.le s a
  rw [abs_lt] at h
  constructor
  · intro hlt
    have h2 := hΔle s a hlt.ne
    rw [abs_of_neg (by linarith)] at h2
    linarith
  · intro hlt
    have h2 := hΔle s a hlt.ne'
    rw [abs_of_pos (by linarith)] at h2
    linarith
