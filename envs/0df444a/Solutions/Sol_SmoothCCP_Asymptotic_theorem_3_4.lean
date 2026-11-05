-- Prove2me | solution 1 for SmoothCCP.Asymptotic.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:28:02.560082+00:00
-- url     : https://prove2.me/submissions/d30a8ad5-186e-42df-b306-deac03405e9a

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Theorems.Thm_SmoothCCP_Asymptotic_sampleCdf_uniform_smoothCdf
import Theorems.Thm_SmoothCCP_Asymptotic_smoothCdf_uniform_cdf

open MeasureTheory Filter Topology
open SmoothCCP.Feasibility SmoothCCP.Asymptotic

theorem solution
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (X : Set (Fin n → ℝ)) (hX : IsClosed X) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε))
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUX : U ⊆ X) :
    ∀ᵐ ω ∂P,
      TendstoUniformlyOn
        (fun (p : ℕ × ℝ) (x : Fin n → ℝ) =>
          SmoothCCP.Feasibility.sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) 0 x)
        (fun x => SmoothCCP.Feasibility.cdf Pξ C 0 x) (atTop ×ˢ 𝓝[>] (0 : ℝ)) U := by
  have h1 := sampleCdf_uniform_smoothCdf Pξ P ξ hξmeas hξind hξlaw X hX C hA31 hA32meas
    hA32cont γ hγ U hU hUX
  have h2 := smoothCdf_uniform_cdf Pξ X hX C hA31 hA32meas hA32cont γ hγ U hU hUX
  filter_upwards [h1] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  obtain ⟨N0, hN0⟩ := hω (e / 2) (by positivity)
  have h2' := Metric.tendstoUniformlyOn_iff.mp h2 (e / 2) (by positivity)
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioc (0 : ℝ) 1 ∧
      ∀ x ∈ U, dist (cdf Pξ C 0 x) (smoothCdf Pξ C ε (γ ε) 0 x) < e / 2 :=
    Filter.Eventually.and (Ioc_mem_nhdsGT one_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioc (0 : ℝ) 1) h2'
  filter_upwards [(eventually_ge_atTop N0).prod_mk hε] with p hp x hx
  obtain ⟨hN, hεI, hε2⟩ := hp
  have a := hN0 p.1 hN p.2 hεI x hx
  have b := hε2 x hx
  rw [Real.dist_eq] at b ⊢
  have t := abs_sub_le (cdf Pξ C 0 x) (smoothCdf Pξ C p.2 (γ p.2) 0 x)
    (sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) 0 x)
  rw [abs_sub_comm (smoothCdf Pξ C p.2 (γ p.2) 0 x)] at t
  linarith
