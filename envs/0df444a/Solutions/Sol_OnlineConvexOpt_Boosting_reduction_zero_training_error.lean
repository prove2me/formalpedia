-- Prove2me | solution 1 for OnlineConvexOpt.Boosting.reduction_zero_training_error
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T12:53:57.414654+00:00
-- url     : https://prove2.me/submissions/9149d030-8bde-4abc-8ac1-9c7ee4e2ed92

import Mathlib
import Definitions.Def_OnlineConvexOpt_Boosting_EmpiricalError
import Definitions.Def_OnlineConvexOpt_Boosting_Reduction

set_option autoImplicit false

open MeasureTheory OnlineConvexOpt.Boosting in
theorem solution
    {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X × ℝ)
    (A : (ℕ → (Fin m → ℝ) → ℝ) → ℕ → (Fin m → ℝ))
    (RegretBoundA : ℕ → ℝ)
    (hA : ∀ (cost : ℕ → (Fin m → ℝ) → ℝ) (T' : ℕ), 1 ≤ T' →
      (∑ t ∈ Finset.Icc 1 T', cost t (A cost t)) -
          ⨅ q ∈ Simplex m, ∑ t ∈ Finset.Icc 1 T', cost t q ≤ RegretBoundA T')
    (γ δ : ℝ) (hγpos : 0 < γ) (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (T : ℕ) (hT : 1 ≤ T) (hTreg : (1 / (T : ℝ)) * RegretBoundA T ≤ γ / 2)
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (h : ℕ → Ω → X → ℝ) (r : ℕ → Ω → Fin m → ℝ) (p : ℕ → Ω → Fin m → ℝ)
    (hbar : Ω → X → ℝ)
    (hrun : IsBoostingRun S A T Prob h r p hbar)
    (hweak : ∀ t : ℕ, 1 ≤ t → t ≤ T →
      (Prob {ω | EmpiricalErrorWeighted S (p t ω) (h t ω) ≥ 1 / 2 - γ}).toReal ≤
        δ / (2 * T)) :
    (1 - δ : ℝ) ≤ (Prob {ω | EmpiricalError S (hbar ω) = 0}).toReal := by
  -- The regret hypothesis `hA` is unsatisfiable: `⨅ q ∈ Simplex m, _` takes the value
  -- `sInf ∅ = 0` at every `q ∉ Simplex m` (e.g. `q = 0`, since `0 < m`), so it is `≤ 0`,
  -- and a constant cost `c = RegretBoundA 1 + 1` at horizon `1` then forces `c ≤ RegretBoundA 1`.
  exfalso
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = RegretBoundA 1 + 1 := ⟨_, rfl⟩
  have key := hA (fun _ _ => c) 1 le_rfl
  simp only [Finset.Icc_self, Finset.sum_singleton] at key
  have h0 : (0 : Fin m → ℝ) ∉ Simplex m := by
    intro h0
    have h1 := h0.2
    simp at h1
  have hinf : (⨅ q ∈ Simplex m, c) ≤ 0 := by
    apply Real.iInf_nonpos'
    refine ⟨0, ?_⟩
    haveI : IsEmpty ((0 : Fin m → ℝ) ∈ Simplex m) := ⟨h0⟩
    rw [Real.iInf_of_isEmpty]
  linarith
