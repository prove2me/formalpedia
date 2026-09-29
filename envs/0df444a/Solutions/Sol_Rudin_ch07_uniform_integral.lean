-- Prove2me | solution 1 for Rudin.ch07_uniform_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T01:02:40.038878+00:00
-- url     : https://prove2.me/submissions/402a4306-efe9-4952-aa9d-8d5af2222093

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_integrals_stable
import Theorems.Thm_Rudin_RSIntegrable_of_uniform_approximation

open Filter Topology

theorem solution (a b : ℝ) (hab : a ≤ b) (α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hint : ∀ n, Rudin.RSIntegrable a b (f n) α)
    (huc : TendstoUniformlyOn f g atTop (Set.Icc a b)) :
    Rudin.RSIntegrable a b g α ∧
      Tendsto (fun n => Rudin.RSIntegral a b (f n) α) atTop
        (nhds (Rudin.RSIntegral a b g α)) := by
  have hspan : 0 ≤ α b - α a := by
    exact sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  have happrox : ∀ ε > 0, ∃ n, ∀ x ∈ Set.Icc a b,
      |f n x - g x| ≤ ε := by
    intro ε hε
    obtain ⟨n, hn⟩ :=
      ((Metric.tendstoUniformlyOn_iff.mp huc) ε hε).exists
    refine ⟨n, ?_⟩
    intro x hx
    have h := hn x hx
    simpa [Real.dist_eq, abs_sub_comm] using h.le
  refine ⟨Rudin.RSIntegrable_of_uniform_approximation
    hab α hα f g hint happrox, ?_⟩
  apply Metric.tendsto_atTop.2
  intro δ hδ
  let Δ : ℝ := α b - α a
  let ε : ℝ := δ / (Δ + 1)
  have hΔ : 0 ≤ Δ := hspan
  have hden : 0 < Δ + 1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Metric.tendstoUniformlyOn_iff.mp huc) ε hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hpoint : ∀ x ∈ Set.Icc a b, |f n x - g x| ≤ ε := by
    intro x hx
    have h := hN n hn x hx
    simpa [Real.dist_eq, abs_sub_comm] using h.le
  have hu := (Rudin.integrals_stable hab α (f n) g hα hε.le hpoint).1
  have hratio : ε * Δ < δ := by
    calc
      ε * Δ = δ * Δ / (Δ + 1) := by
        dsimp [ε]
        ring
      _ < δ := by
        apply (div_lt_iff₀ hden).2
        nlinarith
  simpa only [Rudin.RSIntegral, Real.dist_eq] using lt_of_le_of_lt hu hratio
