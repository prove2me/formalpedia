-- Prove2me | solution 1 for SmoothCCP.Asymptotic.eq_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:28:04.551412+00:00
-- url     : https://prove2.me/submissions/c7f3d94c-388a-468d-81a0-11ea86d14226

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Definitions.Def_SmoothCCP_Asymptotic_Optimization
import Theorems.Thm_SmoothCCP_Asymptotic_theorem_3_4

open MeasureTheory Filter Topology
open SmoothCCP.Feasibility SmoothCCP.Asymptotic

namespace Sol335Aux

theorem gam_continuous {ε : ℝ} {γ : ℝ → ℝ} (h : AdmissibleGamma ε γ) : Continuous (Gam ε γ) :=
  h.differentiable.continuous

theorem sampleCdf_continuous {n N : ℕ} {Ξ : Type} (C : (Fin n → ℝ) → Ξ → ℝ) {ε : ℝ}
    {γ : ℝ → ℝ} (h : AdmissibleGamma ε γ) (ξs : Fin N → Ξ)
    (hs : ∀ i, Continuous (fun x => C x (ξs i))) :
    Continuous (sampleCdf C ε γ ξs 0) := by
  unfold sampleCdf
  exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
    (gam_continuous h).comp ((hs i).sub continuous_const))

theorem ae_sample_cont {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i)) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (C : (Fin n → ℝ) → Ξ → ℝ) (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s)) :
    ∀ᵐ ω ∂P, ∀ i, Continuous (fun x => C x (ξ i ω)) := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ s ∂(P.map (ξ i)), Continuous (fun x => C x s) := by
    rw [hξlaw i]; exact hA32cont
  exact ae_of_ae_map (hξmeas i).aemeasurable h

theorem ev_pos : ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ), 0 < (p : ℕ × ℝ).2 :=
  (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)).prod_inr atTop

theorem ev_cont {n : ℕ} {Ξ : Type} (C : (Fin n → ℝ) → Ξ → ℝ) (γ : ℝ → ℝ → ℝ)
    (hγ : ∀ ε > 0, AdmissibleGamma ε (γ ε)) (s : ℕ → Ξ)
    (hs : ∀ i, Continuous (fun x => C x (s i))) :
    ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
      Continuous (sampleCdf C (p : ℕ × ℝ).2 (γ p.2) (fun i : Fin p.1 => s i) 0) := by
  filter_upwards [ev_pos] with p hp
  exact sampleCdf_continuous C (hγ _ hp) _ (fun i => hs i)

/-- A uniform limit of eventually continuous functions is continuous. -/
theorem cdf_continuousOn {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ)
    (C : (Fin n → ℝ) → Ξ → ℝ) (γ : ℝ → ℝ → ℝ)
    (hγ : ∀ ε > 0, AdmissibleGamma ε (γ ε)) (s : ℕ → Ξ)
    (hs : ∀ i, Continuous (fun x => C x (s i))) (U : Set (Fin n → ℝ))
    (hU : TendstoUniformlyOn
        (fun (p : ℕ × ℝ) (x : Fin n → ℝ) =>
          sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => s i) 0 x)
        (fun x => cdf Pξ C 0 x) (atTop ×ˢ 𝓝[>] (0 : ℝ)) U) :
    ContinuousOn (cdf Pξ C 0) U := by
  exact hU.continuousOn ((ev_cont C γ hγ s hs).mono (fun p hp => hp.continuousOn)).frequently

theorem optVal_eq {n : ℕ} {f : (Fin n → ℝ) → ℝ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ optSet f A) : optVal f A = f x := by
  have hl : IsLeast (f '' A) (f x) :=
    ⟨⟨x, hx.1, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hx.2 y hy⟩
  exact hl.csInf_eq

end Sol335Aux

open Sol335Aux

theorem solution
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (X : Set (Fin n → ℝ)) (hX : IsCompact X)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (xbar : Fin n → ℝ) (hxbar : xbar ∈ optSet f (SmoothCCP.Feasibility.trueFeasible Pξ C X α))
    (hA33 : ∀ η > 0, ∃ x ∈ X, ‖x - xbar‖ ≤ η ∧ 1 - α < SmoothCCP.Feasibility.cdf Pξ C 0 x)
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε)) :
    ∀ᵐ ω ∂P, ∀ η > 0, ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
      ∀ x ∈ saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α,
        optVal f (SmoothCCP.Feasibility.trueFeasible Pξ C X α) - η ≤ f x := by
  rw [optVal_eq hxbar]
  have hunif := theorem_3_4 Pξ P ξ hξmeas hξind hξlaw X hX.isClosed C hA31 hA32meas hA32cont
    γ hγ X hX subset_rfl
  filter_upwards [hunif, ae_sample_cont Pξ P ξ hξmeas hξlaw C hA32cont] with ω hω hs
  have hFc : ContinuousOn (cdf Pξ C 0) X := cdf_continuousOn Pξ C γ hγ _ hs X hω
  intro η hη
  set K := X ∩ {x | f x ≤ f xbar - η} with hKdef
  have hKc : IsCompact K := hX.inter_right (isClosed_le hf continuous_const)
  by_cases hK : K.Nonempty
  · obtain ⟨x0, hx0K, hmax⟩ := hKc.exists_isMaxOn hK (hFc.mono Set.inter_subset_left)
    have hlt : cdf Pξ C 0 x0 < 1 - α := by
      by_contra h
      push_neg at h
      have h1 := hxbar.2 x0 ⟨hx0K.1, h⟩
      have h2 : f x0 ≤ f xbar - η := hx0K.2
      linarith
    have hδ : 0 < 1 - α - cdf Pξ C 0 x0 := by linarith
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hω _ hδ] with p hp
    intro x hx
    by_contra hfx
    push_neg at hfx
    have hxK : x ∈ K := ⟨hx.1, hfx.le⟩
    have hle : cdf Pξ C 0 x ≤ cdf Pξ C 0 x0 := hmax hxK
    have hd := hp x hx.1
    have hx2 : 1 - α ≤ sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) 0 x := by
      have := hx.2; simpa only [neg_zero] using this
    rw [Real.dist_eq] at hd
    have := neg_abs_le (cdf Pξ C 0 x - sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) 0 x)
    linarith
  · refine Filter.Eventually.of_forall (fun p x hx => ?_)
    by_contra hfx
    push_neg at hfx
    exact hK ⟨x, hx.1, hfx.le⟩
