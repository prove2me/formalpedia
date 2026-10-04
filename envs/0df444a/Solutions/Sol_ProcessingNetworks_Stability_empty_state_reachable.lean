-- Prove2me | solution 1 for ProcessingNetworks.Stability.empty_state_reachable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:07:51.156981+00:00
-- url     : https://prove2.me/submissions/1112eeb2-762a-4385-8c8f-914553b1a0d4

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation

open ProcessingNetworks.Stability MeasureTheory ProbabilityTheory
open scoped NNReal

theorem solution {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J : ℕ} {N0 : Fin J → ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (hbase : BaselineAssumptions I J N0 E lam v φ m Γ Psi)
    (M : MarkovRepresentation Xstate I J N Z)
    (hsupp : ∀ x : Xstate, ℙ {ω | M.X 0 ω = x} ≠ 0)
    (hZN : ∀ (t : ℝ) (ω : Ω), Z t ω = 0 → N t ω = 0)
    (xstar : Xstate) (hxstar : M.f xstar = (0, 0))
    (hxstar_unique : ∀ x, M.f x = (0, 0) → x = xstar)
    (h318 : ∀ x : Xstate, ∃ t : ℝ, 0 < t ∧
      (ℙ[|{ω | M.X 0 ω = x}])[|{ω | ∀ i, E i t ω = E i 0 ω}] {ω | Z t ω = 0} > 0) :
    ∀ x : Xstate, ∃ t : ℝ, 0 < t ∧ (ℙ[|{ω | M.X 0 ω = x}]) {ω | M.X t ω = xstar} > 0 := by
  intro x
  obtain ⟨t, ht, hpos⟩ := h318 x
  refine ⟨t, ht, ?_⟩
  set μ := ℙ[|{ω | M.X 0 ω = x}]
  set B := {ω : Ω | ∀ i, E i t ω = E i 0 ω}
  have hsub : {ω | Z t ω = 0} ⊆ {ω | M.X t ω = xstar} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    apply hxstar_unique
    rw [← M.sample_path_eq t ω, hω, hZN t ω hω]
  have h1 : μ.restrict B {ω | Z t ω = 0} ≠ 0 := by
    intro h0
    rw [ProbabilityTheory.cond, Measure.smul_apply, h0, smul_zero] at hpos
    exact lt_irrefl _ hpos
  have h2 : μ.restrict B {ω | Z t ω = 0} ≤ μ {ω | M.X t ω = xstar} :=
    (Measure.restrict_apply_le _ _).trans (measure_mono hsub)
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr h1) h2


