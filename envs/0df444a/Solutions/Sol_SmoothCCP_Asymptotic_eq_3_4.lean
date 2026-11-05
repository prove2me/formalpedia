-- Prove2me | solution 1 for SmoothCCP.Asymptotic.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:28:03.434958+00:00
-- url     : https://prove2.me/submissions/6015621c-2255-4f79-a911-267fa3d3a3eb

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Definitions.Def_SmoothCCP_Asymptotic_Optimization
import Theorems.Thm_SmoothCCP_Asymptotic_theorem_3_4

open MeasureTheory Filter Topology
open SmoothCCP.Feasibility SmoothCCP.Asymptotic

theorem solution
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (xbar : Fin n → ℝ) (hxbar : xbar ∈ optSet f (SmoothCCP.Feasibility.trueFeasible Pξ C X α))
    (hA33 : ∀ η > 0, ∃ x ∈ X, ‖x - xbar‖ ≤ η ∧ 1 - α < SmoothCCP.Feasibility.cdf Pξ C 0 x)
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε)) :
    ∀ᵐ ω ∂P, ∀ η > 0, ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
      ∃ x ∈ saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α,
        f x ≤ optVal f (SmoothCCP.Feasibility.trueFeasible Pξ C X α) + η := by
  -- the optimal value equals f xbar
  have hv : optVal f (trueFeasible Pξ C X α) = f xbar := by
    have hl : IsLeast (f '' trueFeasible Pξ C X α) (f xbar) :=
      ⟨⟨xbar, hxbar.1, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hxbar.2 y hy⟩
    exact hl.csInf_eq
  -- a sequence of strictly feasible points converging to xbar
  have hA33' : ∀ m : ℕ, ∃ x ∈ X, ‖x - xbar‖ ≤ 1 / ((m : ℝ) + 1) ∧
      1 - α < cdf Pξ C 0 x := fun m => hA33 _ (by positivity)
  choose xs hxsX hxsd hxsF using hA33'
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ,
      TendstoUniformlyOn
        (fun (p : ℕ × ℝ) (x : Fin n → ℝ) =>
          sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) 0 x)
        (fun x => cdf Pξ C 0 x) (atTop ×ˢ 𝓝[>] (0 : ℝ)) {xs m} := by
    rw [ae_all_iff]
    intro m
    exact theorem_3_4 Pξ P ξ hξmeas hξind hξlaw X hX C hA31 hA32meas hA32cont γ hγ {xs m}
      isCompact_singleton (Set.singleton_subset_iff.mpr (hxsX m))
  filter_upwards [hall] with ω hω
  intro η hη
  rw [hv]
  obtain ⟨ρ, hρ, hfρ⟩ := Metric.continuous_iff.mp hf xbar η hη
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hρ
  have hdist : dist (xs m) xbar < ρ := by
    rw [dist_eq_norm]; exact lt_of_le_of_lt (hxsd m) hm
  have hfx : f (xs m) ≤ f xbar + η := by
    have := hfρ (xs m) hdist
    rw [Real.dist_eq] at this
    linarith [le_abs_self (f (xs m) - f xbar)]
  have ht := (hω m).tendsto_at (Set.mem_singleton (xs m))
  have hev := ht.eventually (lt_mem_nhds (hxsF m))
  filter_upwards [hev] with p hp
  refine ⟨xs m, ⟨hxsX m, ?_⟩, hfx⟩
  simp only [neg_zero]
  exact hp.le
