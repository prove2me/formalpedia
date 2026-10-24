-- Prove2me | solution 1 for PandoraBO.Private20261023.dual_convex_and_attains_minimum
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:29:36.920741+00:00
-- url     : https://prove2.me/submissions/3c029256-29d9-4406-a7da-7261049e854a

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_abstract_dual_convex_and_attains
import Theorems.Thm_PandoraBO_Private20261023_policy_expectation_bounds_and_slater
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

namespace PandoraBO.Private20261023.DualEnvelopeReduction

theorem value_range_bddAbove {ι : Type*} (R C : ι → ℝ)
    (r c : ℝ) (hbounds : ∀ i, |R i| ≤ r ∧ |C i| ≤ c) (t : ℝ) :
    BddAbove (Set.range (fun i => R i - t * C i)) := by
  refine ⟨r + |t| * c, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hr : R i ≤ r := (le_abs_self _).trans (hbounds i).1
  have htc : |t * C i| ≤ |t| * c := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbounds i).2 (abs_nonneg t)
  have hc : -(t * C i) ≤ |t| * c := (neg_le_abs _).trans htc
  linarith only [hr, hc]

end PandoraBO.Private20261023.DualEnvelopeReduction

/-- Exact mission target, reduced to the abstract convex-envelope theorem and
the expectation/integrability foundations. Its dependencies are explicit. -/
theorem solution {n : ℕ} (M : PandoraBO.Instance n)
    (B : ℝ) (hslater : ∃ i : PandoraBO.Box n, M.cost i < B) :
    (∀ x y a : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ a → a ≤ 1 →
      PandoraBO.dualValue M B (a * x + (1 - a) * y) ≤
        a * PandoraBO.dualValue M B x + (1 - a) * PandoraBO.dualValue M B y) ∧
    ∃ multiplier : ℝ, PandoraBO.dualMinimizer M B multiplier := by
  obtain ⟨⟨r, c, _, _, hbounds⟩, honebox⟩ :=
    PandoraBO.Private20261023.policy_expectation_bounds_and_slater M
  obtain ⟨i, hi⟩ := hslater
  obtain ⟨π, hπ⟩ := honebox i
  have hstrict : ∃ π : PandoraBO.Policy n, PandoraBO.expectedCost M π < B :=
    ⟨π, by rwa [hπ]⟩
  have hset (t : ℝ) :
      {v : ℝ | ∃ π : PandoraBO.Policy n, v = PandoraBO.value M t π} =
        Set.range (fun π : PandoraBO.Policy n =>
          PandoraBO.expectedReward M π - t * PandoraBO.expectedCost M π) := by
    ext v
    constructor
    · rintro ⟨π, rfl⟩
      exact ⟨π, rfl⟩
    · rintro ⟨π, rfl⟩
      exact ⟨π, rfl⟩
  have hdual (t : ℝ) : PandoraBO.dualValue M B t =
      sSup (Set.range (fun π : PandoraBO.Policy n =>
        PandoraBO.expectedReward M π - t * PandoraBO.expectedCost M π)) + t * B := by
    simp only [PandoraBO.dualValue, PandoraBO.optimalValue, hset]
  obtain ⟨hconvex, t, ht, hmin⟩ :=
    PandoraBO.Private20261023.abstract_dual_convex_and_attains
      (PandoraBO.expectedReward M) (PandoraBO.expectedCost M) B
      (PandoraBO.Private20261023.DualEnvelopeReduction.value_range_bddAbove
        _ _ r c hbounds) hstrict
  constructor
  · intro x y a _ _ ha ha₁
    simpa only [hdual] using hconvex x y a ha ha₁
  · refine ⟨t, ht, fun u hu => ?_⟩
    simpa only [hdual] using hmin u hu
