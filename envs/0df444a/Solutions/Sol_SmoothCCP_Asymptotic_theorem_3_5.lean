-- Prove2me | solution 1 for SmoothCCP.Asymptotic.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:28:05.804064+00:00
-- url     : https://prove2.me/submissions/0f0fc6b5-63dc-4835-81e8-8ea5f95418ff

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Definitions.Def_SmoothCCP_Asymptotic_Optimization
import Theorems.Thm_SmoothCCP_Asymptotic_theorem_3_4
import Theorems.Thm_SmoothCCP_Asymptotic_optSet_eventually_nonempty
import Theorems.Thm_SmoothCCP_Asymptotic_eq_3_3
import Theorems.Thm_SmoothCCP_Asymptotic_eq_3_4

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
    ∀ᵐ ω ∂P,
      (∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
        (optSet f (saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α)).Nonempty) ∧
      Tendsto (fun p : ℕ × ℝ =>
          optVal f (saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α))
        (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (optVal f (SmoothCCP.Feasibility.trueFeasible Pξ C X α))) ∧
      (∀ η > 0, ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
        ∀ x ∈ optSet f (saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α),
          Metric.infDist x (optSet f (SmoothCCP.Feasibility.trueFeasible Pξ C X α)) < η) := by
  have hv := optVal_eq hxbar
  have hne := optSet_eventually_nonempty Pξ P ξ hξmeas hξind hξlaw α hα0 hα1 X hX f hf C hA31
    hA32meas hA32cont xbar hxbar hA33 γ hγ
  have h33 := eq_3_3 Pξ P ξ hξmeas hξind hξlaw α hα0 hα1 X hX f hf C hA31
    hA32meas hA32cont xbar hxbar hA33 γ hγ
  have h34 := eq_3_4 Pξ P ξ hξmeas hξind hξlaw α hα0 hα1 X hX.isClosed f hf C hA31
    hA32meas hA32cont xbar hxbar hA33 γ hγ
  have hunif := theorem_3_4 Pξ P ξ hξmeas hξind hξlaw X hX.isClosed C hA31 hA32meas hA32cont
    γ hγ X hX subset_rfl
  filter_upwards [hne, h33, h34, hunif, ae_sample_cont Pξ P ξ hξmeas hξlaw C hA32cont]
    with ω hne h33 h34 hω hs
  rw [hv] at h33 h34
  have hFc : ContinuousOn (cdf Pξ C 0) X := cdf_continuousOn Pξ C γ hγ _ hs X hω
  refine ⟨hne, ?_, ?_⟩
  · rw [hv, Metric.tendsto_nhds]
    intro e he
    filter_upwards [hne, h33 (e / 2) (by positivity), h34 (e / 2) (by positivity)]
      with p hp h3 h4
    obtain ⟨xh, hxh⟩ := hp
    obtain ⟨x', hx', hfx'⟩ := h4
    rw [optVal_eq hxh, Real.dist_eq, abs_sub_lt_iff]
    have a1 := h3 xh hxh.1
    have a2 := hxh.2 x' hx'
    constructor <;> linarith
  · intro η hη
    set S := optSet f (trueFeasible Pξ C X α) with hSdef
    set K := X ∩ {x | η ≤ Metric.infDist x S} with hKdef
    have hKc : IsCompact K :=
      hX.inter_right (isClosed_le continuous_const (Metric.continuous_infDist_pt S))
    by_cases hK : K.Nonempty
    · set g : (Fin n → ℝ) → ℝ := fun x => max (1 - α - cdf Pξ C 0 x) (f x - f xbar) with hg
      have hgc : ContinuousOn g K := by
        have h1 : ContinuousOn (fun x => 1 - α - cdf Pξ C 0 x) K :=
          continuousOn_const.sub (hFc.mono Set.inter_subset_left)
        have h2 : ContinuousOn (fun x => f x - f xbar) K :=
          hf.continuousOn.sub continuousOn_const
        exact h1.sup h2
      obtain ⟨x0, hx0K, hmin⟩ := hKc.exists_isMinOn hK hgc
      have hpos : 0 < g x0 := by
        by_contra h
        push_neg at h
        have h1 : 1 - α - cdf Pξ C 0 x0 ≤ 0 := le_trans (le_max_left _ _) h
        have h2 : f x0 - f xbar ≤ 0 := le_trans (le_max_right _ _) h
        have hx0S : x0 ∈ S := by
          refine ⟨⟨hx0K.1, by linarith⟩, fun y hy => ?_⟩
          have := hxbar.2 y hy
          linarith
        have := hx0K.2
        simp only [Set.mem_setOf_eq, Metric.infDist_zero_of_mem hx0S] at this
        linarith
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hω _ hpos,
        h34 (g x0 / 2) (by positivity)] with p hp h4
      obtain ⟨x', hx', hfx'⟩ := h4
      intro x hx
      by_contra hd
      push_neg at hd
      have hxK : x ∈ K := ⟨hx.1.1, hd⟩
      have hle : g x0 ≤ g x := hmin hxK
      have hdist := hp x hx.1.1
      have hx2 : 1 - α ≤ sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) 0 x := by
        have := hx.1.2; simpa only [neg_zero] using this
      rw [Real.dist_eq] at hdist
      have hab := neg_abs_le
        (cdf Pξ C 0 x - sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) 0 x)
      have hfx := hx.2 x' hx'
      have : g x < g x0 := by
        rw [hg]
        apply max_lt
        · linarith
        · linarith
      linarith
    · refine Filter.Eventually.of_forall (fun p x hx => ?_)
      by_contra hd
      push_neg at hd
      exact hK ⟨x, hx.1.1, hd⟩
