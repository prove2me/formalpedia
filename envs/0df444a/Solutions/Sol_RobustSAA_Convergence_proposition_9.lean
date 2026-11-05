-- Prove2me | solution 1 for RobustSAA.Convergence.proposition_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:03:41.517628+00:00
-- url     : https://prove2.me/submissions/4e111ef6-dd3e-4c0c-bcac-d588df8a3712

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology
open RobustSAA.Convergence

namespace RSAAProp9Aux

/-- Equicontinuity (Assumption 1) gives closeness of `c(y;·)` to `c(x;·)` uniformly in `ξ`. -/
lemma unif_close {d dx : ℕ} {Ξ : Set (Pt d)} {X : Set (Pt dx)} {c : Pt dx → ↥Ξ → ℝ}
    (hA1 : Assumption1 X c) (x : Pt dx) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ ξ, |c y ξ - c x ξ| < ε := by
  have h := (equicontinuousOn_univ _).1 hA1 x
  rw [Metric.equicontinuousAt_iff_right] at h
  filter_upwards [h ε hε] with y hy ξ
  have := hy ξ
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this

/-- The true objective is continuous along sequences in `X`. -/
lemma trueObj_tendsto {d dx : ℕ} {Ξ : Set (Pt d)} {F : ProbabilityMeasure ↥Ξ} {X : Set (Pt dx)}
    {c : Pt dx → ↥Ξ → ℝ} (hS : Standing F X c) (hA1 : Assumption1 X c)
    {z : ℕ → Pt dx} {x : Pt dx} (hz : ∀ k, z k ∈ X) (hx : x ∈ X)
    (hlim : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun k => trueObj F c (z k)) atTop (𝓝 (trueObj F c x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 := hlim.eventually (unif_close hA1 x (half_pos hε))
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 h1
  refine ⟨k0, fun k hk => ?_⟩
  rw [Real.dist_eq]
  unfold trueObj
  rw [← integral_sub (hS.2 _ (hz k)).1 (hS.2 _ hx).1]
  have hb : ‖∫ ξ, (c (z k) ξ - c x ξ) ∂(F : Measure ↥Ξ)‖ ≤ ε / 2 * (F : Measure ↥Ξ).real Set.univ :=
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]; exact (hk0 k hk ξ).le)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at hb
  linarith

end RSAAProp9Aux

open RSAAProp9Aux

theorem solution {d dx : ℕ} {Ξ : Set (Pt d)} (F : ProbabilityMeasure ↥Ξ)
    (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ) (𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ))
    (hS : Standing F X c) (hA1 : Assumption1 X c)
    (hconv : ∀ (xs : ℕ → Pt dx) (x : Pt dx), x ∈ X → (∀ N, xs N ∈ X) →
      Tendsto xs atTop (𝓝 x) →
        Tendsto (fun N => worstCase (𝒢 N) (c (xs N))) atTop (𝓝 ((trueObj F c x : ℝ) : EReal))) :
    ObjConv F X c 𝒢 := by
  classical
  intro K hKX hK ε hε
  by_contra hbad
  rw [not_eventually] at hbad
  obtain ⟨ψ, hψ, hψP⟩ := extraction_of_frequently_atTop hbad
  have hex : ∀ n, ∃ x ∈ K, ¬ (worstCase (𝒢 (ψ n)) (c x) ≤ ((trueObj F c x + ε : ℝ) : EReal) ∧
      ((trueObj F c x - ε : ℝ) : EReal) ≤ worstCase (𝒢 (ψ n)) (c x)) := by
    intro n
    have := hψP n
    push Not at this ⊢
    obtain ⟨x, hx, h⟩ := this
    exact ⟨x, hx, h⟩
  choose xs hxsK hxsbad using hex
  obtain ⟨x, hxK, φ, hφ, hlim⟩ := hK.tendsto_subseq hxsK
  set θ : ℕ → ℕ := ψ ∘ φ with hθdef
  have hθ : StrictMono θ := hψ.comp hφ
  let ys : ℕ → Pt dx := fun N => if h : ∃ k, θ k = N then xs (φ h.choose) else x
  have hys_θ : ∀ k, ys (θ k) = xs (φ k) := by
    intro k
    have h : ∃ k', θ k' = θ k := ⟨k, rfl⟩
    simp only [ys, dif_pos h]
    rw [hθ.injective h.choose_spec]
  have hysX : ∀ N, ys N ∈ X := by
    intro N
    by_cases h : ∃ k, θ k = N
    · simp only [ys, dif_pos h]; exact hKX (hxsK _)
    · simp only [ys, dif_neg h]; exact hKX hxK
  have hys_lim : Tendsto ys atTop (𝓝 x) := by
    intro U hU
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 (hlim hU)
    rw [Filter.mem_map, mem_atTop_sets]
    refine ⟨θ k0, fun N hN => ?_⟩
    show ys N ∈ U
    by_cases h : ∃ k, θ k = N
    · simp only [ys, dif_pos h]
      apply hk0
      have := h.choose_spec
      rw [← this] at hN
      exact hθ.le_iff_le.1 hN
    · simp only [ys, dif_neg h]; exact mem_of_mem_nhds hU
  have hW := (hconv ys x (hKX hxK) hysX hys_lim).comp hθ.tendsto_atTop
  have hT := trueObj_tendsto hS hA1 (fun k => hKX (hxsK (φ k))) (hKX hxK) hlim
  have hev1 : ∀ᶠ k in atTop, worstCase (𝒢 (θ k)) (c (ys (θ k))) ∈
      Set.Ioo (((trueObj F c x - ε / 2 : ℝ)) : EReal) (((trueObj F c x + ε / 2 : ℝ)) : EReal) :=
    hW (Ioo_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith))
      (EReal.coe_lt_coe_iff.2 (by linarith)))
  have hev2 := (Metric.tendsto_atTop.1 hT) (ε / 2) (half_pos hε)
  obtain ⟨k, hk1, hk2⟩ := (hev1.and (eventually_atTop.2 hev2)).exists
  rw [hys_θ k] at hk1
  rw [Real.dist_eq, abs_lt] at hk2
  apply hxsbad (φ k)
  have hψφ : ψ (φ k) = θ k := rfl
  rw [hψφ]
  constructor
  · exact hk1.2.le.trans (EReal.coe_le_coe_iff.2 (by linarith [hk2.1, hk2.2]))
  · exact (EReal.coe_le_coe_iff.2 (by linarith [hk2.1, hk2.2])).trans hk1.1.le
