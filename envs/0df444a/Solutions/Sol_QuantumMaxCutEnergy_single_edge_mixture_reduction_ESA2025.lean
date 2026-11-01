-- Prove2me | solution 1 for QuantumMaxCutEnergy.single_edge_mixture_reduction_ESA2025
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T00:56:45.698316+00:00
-- url     : https://prove2.me/submissions/7fb2fbe5-c5d8-4c41-a4e1-98863d4cafe9

import Mathlib

/-!
Finite, division-free form of Lemma 10 of Apte, Lee, Marwaha, Parekh, and Sud,
"Improved Algorithms for Quantum MaxCut via Partially Entangled Matchings",
ESA 2025, pp. 101:11--101:12, DOI 10.4230/LIPIcs.ESA.2025.101.

Only the published conference version is used. The lemma below is a finite
weighted averaging argument; it makes no claim to implement an SDP or to
establish the paper's complete approximation algorithm.
-/

open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedESA2025

/-- If a fixed distribution over candidates gives the required bound on each
edge, some candidate gives that bound on the whole instance. -/
theorem single_edge_mixture_reduction
    {E A : Type*} (edges : Finset E) (candidates : Finset A)
    (w b : E → ℝ) (gain : A → E → ℝ) (μ : A → ℝ) (opt α : ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hμ : ∀ a ∈ candidates, 0 ≤ μ a)
    (hμsum : ∑ a ∈ candidates, μ a = 1)
    (hα : 0 ≤ α)
    (hopt : opt ≤ ∑ e ∈ edges, w e * b e)
    (hedge : ∀ e ∈ edges, α * b e ≤ ∑ a ∈ candidates, μ a * gain a e) :
    ∃ a ∈ candidates, α * opt ≤ ∑ e ∈ edges, w e * gain a e := by
  classical
  have hne : candidates.Nonempty := by
    by_contra h
    have hz : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hz, Finset.sum_empty] at hμsum
    norm_num at hμsum
  have havg : α * opt ≤
      ∑ a ∈ candidates, μ a * (∑ e ∈ edges, w e * gain a e) := by
    calc
      α * opt ≤ α * (∑ e ∈ edges, w e * b e) :=
        mul_le_mul_of_nonneg_left hopt hα
      _ = ∑ e ∈ edges, w e * (α * b e) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ ≤ ∑ e ∈ edges, w e * (∑ a ∈ candidates, μ a * gain a e) := by
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (hedge e he) (hw e he)
      _ = ∑ a ∈ candidates, μ a * (∑ e ∈ edges, w e * gain a e) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro e he
        ring
  obtain ⟨a, ha, hmax⟩ := candidates.exists_max_image
    (fun a => ∑ e ∈ edges, w e * gain a e) hne
  refine ⟨a, ha, havg.trans ?_⟩
  calc
    (∑ c ∈ candidates, μ c * (∑ e ∈ edges, w e * gain c e)) ≤
        ∑ c ∈ candidates, μ c * (∑ e ∈ edges, w e * gain a e) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hmax c hc) (hμ c hc)
    _ = ∑ e ∈ edges, w e * gain a e := by
      rw [← Finset.sum_mul, hμsum, one_mul]

/-- Positive edge denominators give the usual per-edge ratio formulation. -/
theorem single_edge_ratio_reduction
    {E A : Type*} (edges : Finset E) (candidates : Finset A)
    (w b : E → ℝ) (gain : A → E → ℝ) (μ : A → ℝ) (opt α : ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hb : ∀ e ∈ edges, 0 < b e)
    (hμ : ∀ a ∈ candidates, 0 ≤ μ a)
    (hμsum : ∑ a ∈ candidates, μ a = 1)
    (hα : 0 ≤ α)
    (hopt : opt ≤ ∑ e ∈ edges, w e * b e)
    (hedge : ∀ e ∈ edges, α ≤ (∑ a ∈ candidates, μ a * gain a e) / b e) :
    ∃ a ∈ candidates, α * opt ≤ ∑ e ∈ edges, w e * gain a e := by
  apply single_edge_mixture_reduction edges candidates w b gain μ opt α hw hμ hμsum hα hopt
  intro e he
  exact (le_div_iff₀ (hb e he)).mp (hedge e he)

/-- The selected candidate also satisfies any supplied feasibility upper bound. -/
theorem single_edge_feasible_estimate
    {E A : Type*} (edges : Finset E) (candidates : Finset A)
    (w b : E → ℝ) (gain : A → E → ℝ) (μ : A → ℝ) (opt α : ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hμ : ∀ a ∈ candidates, 0 ≤ μ a)
    (hμsum : ∑ a ∈ candidates, μ a = 1)
    (hα : 0 ≤ α)
    (hopt : opt ≤ ∑ e ∈ edges, w e * b e)
    (hedge : ∀ e ∈ edges, α * b e ≤ ∑ a ∈ candidates, μ a * gain a e)
    (hsound : ∀ a ∈ candidates, (∑ e ∈ edges, w e * gain a e) ≤ opt) :
    ∃ a ∈ candidates,
      α * opt ≤ (∑ e ∈ edges, w e * gain a e) ∧
        (∑ e ∈ edges, w e * gain a e) ≤ opt := by
  obtain ⟨a, ha, hratio⟩ :=
    single_edge_mixture_reduction edges candidates w b gain μ opt α hw hμ hμsum hα hopt hedge
  exact ⟨a, ha, hratio, hsound a ha⟩

#print axioms single_edge_mixture_reduction
#print axioms single_edge_ratio_reduction
#print axioms single_edge_feasible_estimate

end QuantumMaxCutEnergy.PublishedESA2025

theorem solution
    {E A : Type*} (edges : Finset E) (candidates : Finset A)
    (w b : E → ℝ) (gain : A → E → ℝ) (μ : A → ℝ) (opt α : ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hμ : ∀ a ∈ candidates, 0 ≤ μ a)
    (hμsum : ∑ a ∈ candidates, μ a = 1)
    (hα : 0 ≤ α)
    (hopt : opt ≤ ∑ e ∈ edges, w e * b e)
    (hedge : ∀ e ∈ edges, α * b e ≤ ∑ a ∈ candidates, μ a * gain a e) :
    ∃ a ∈ candidates, α * opt ≤ ∑ e ∈ edges, w e * gain a e := by
  exact QuantumMaxCutEnergy.PublishedESA2025.single_edge_mixture_reduction
    edges candidates w b gain μ opt α hw hμ hμsum hα hopt hedge

#print axioms solution
