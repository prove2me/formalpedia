-- Prove2me | solution 1 for TabooRegen.exp_moment_of_A7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T08:42:56.766553+00:00
-- url     : https://prove2.me/submissions/14829d95-d47f-4add-b40b-2b47f8e7fea4

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace TabooRegen.ExpMomA7

open TabooRegen TabooRegen.Model

lemma measurable_tau1 {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω) :
    Measurable fun ω => (M.τ 1 ω).toReal := by
  have h1 := M.measurable_T 1
  have h0 := M.measurable_T 0
  have : (fun ω => (M.τ 1 ω).toReal) = fun ω => (M.T 1 ω - M.T 0 ω).toReal := by
    funext ω
    simp [Model.τ, Model.Tm, prevTime]
  rw [this]
  exact (h1.sub h0).ennreal_toReal

lemma lintegral_Gtilde_exp {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω) (α ε : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (ε * x)) ∂(M.Gtilde α) = M.cycleMGF (α + ε) := by
  have hden : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (α * x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (ε * x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hθ : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp ((α + ε) * x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  rw [Model.Gtilde, lintegral_withDensity_eq_lintegral_mul _ hden hg]
  have hpt : ((fun x : ℝ => ENNReal.ofReal (Real.exp (α * x))) *
      fun x : ℝ => ENNReal.ofReal (Real.exp (ε * x))) =
      fun x : ℝ => ENNReal.ofReal (Real.exp ((α + ε) * x)) := by
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [hpt, Model.G, lintegral_map hθ (measurable_tau1 M), Model.cycleMGF]

end TabooRegen.ExpMomA7

open TabooRegen TabooRegen.Model in
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    {α : ℝ} (h1 : M.A1 α) (h7 : M.A7) :
    ∃ ε₀ > 0, ∫⁻ x, ENNReal.ofReal (Real.exp (ε₀ * x)) ∂(M.Gtilde α) < ⊤ := by
  have hα : ((α : ℝ) : EReal) ≤ M.κ₁ := by
    apply le_sSup
    exact ⟨α, by simp [h1.2], rfl⟩
  have hlt : M.κ₁ < M.κ₂ := h7
  obtain ⟨y, ⟨θ, hθ, rfl⟩, hyθ⟩ := lt_sSup_iff.mp hlt
  have hαθ : α < θ := by
    have : ((α : ℝ) : EReal) < (θ : EReal) := lt_of_le_of_lt hα hyθ
    exact_mod_cast this
  refine ⟨θ - α, sub_pos.mpr hαθ, ?_⟩
  rw [TabooRegen.ExpMomA7.lintegral_Gtilde_exp M α (θ - α)]
  have : α + (θ - α) = θ := by ring
  rw [this]
  exact hθ
