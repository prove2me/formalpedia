-- Prove2me | solution 1 for PrimalDualSubgrad.DA.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:10:28.37551+00:00
-- url     : https://prove2.me/submissions/25881a29-34a5-49ec-8e44-7d5f1bf67746

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting
open PrimalDualSubgrad.DA Filter Asymptotics
open scoped Topology
private theorem growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {d : E → ℝ} {σ : ℝ} (hsc : StrongConvexOn Q σ d)
    {xs x : E} (hs : xs ∈ Q) (hx : x ∈ Q)
    (hm : ∀ y ∈ Q, d xs ≤ d y) :
    d xs + σ / 2 * ‖x - xs‖ ^ 2 ≤ d x := by
  have hb : 0 ≤ d x - d xs := sub_nonneg.mpr (hm x hx)
  by_contra h
  let A := σ / 2 * ‖x - xs‖ ^ 2
  let B := d x - d xs
  have hBA : B < A := by dsimp [A, B]; linarith
  have hB : 0 ≤ B := hb
  have hA : 0 < A := lt_of_le_of_lt hB hBA
  let t := (A - B) / (2 * A)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hteq : t * (2 * A) = A - B := by dsimp [t]; field_simp
  have hc := hsc.2 hs hx (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  have hmem := hsc.1 hs hx (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  have hmin := hm _ hmem
  simp only [smul_eq_mul, norm_sub_rev xs x] at hc
  have hc' : 0 ≤ t * (B - (1 - t) * A) := by dsimp [A, B]; nlinarith [hc]
  have hb' : (1 - t) * A ≤ B := by nlinarith
  nlinarith

private lemma attained {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s : StrongDual ℝ E) :
    V P β s = s (π β s-P.x0)-β*P.d (π β s) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨π β s, (hπ β hβ s).1, rfl⟩, ?_⟩
  rintro _ ⟨x,hx,rfl⟩
  have hh := (hπ β hβ s).2 x hx
  simp only [map_sub]
  linarith

private lemma value_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s : StrongDual ℝ E) (x : E) (hx : x ∈ P.Q) :
    s (x-P.x0)-β*P.d x ≤ V P β s := by
  rw [attained P π hπ β hβ s]
  have hh := (hπ β hβ s).2 x hx
  simp only [map_sub]
  linarith

private lemma prox_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s : StrongDual ℝ E) (x : E) (hx : x ∈ P.Q) :
    -s (π β s)+β*P.d (π β s)+β*P.σ/2*‖x-π β s‖^2 ≤ -s x+β*P.d x := by
  have hs : StrongConvexOn P.Q (β*P.σ) (fun x => -s x+β*P.d x) := by
    refine ⟨P.convex_Q, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := mul_le_mul_of_nonneg_left (P.strongConvexOn_d.2 hx hy ha hb hab) hβ.le
    simp only [map_add, map_smul, smul_eq_mul] at hh ⊢
    nlinarith
  exact growth hs (hπ β hβ s).1 hx (hπ β hβ s).2

private lemma prox_lip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s t : StrongDual ℝ E) :
    ‖π β s-π β t‖ ≤ 1/(β*P.σ)*‖s-t‖ := by
  have h1 := prox_growth P π hπ β hβ s (π β t) (hπ β hβ t).1
  have h2 := prox_growth P π hπ β hβ t (π β s) (hπ β hβ s).1
  rw [norm_sub_rev (π β t) (π β s)] at h1
  have he : (s-t) (π β s-π β t) = s (π β s)-s (π β t)-t (π β s)+t (π β t) := by
    simp [map_sub]; ring
  have hb := (le_abs_self ((s-t) (π β s-π β t))).trans ((s-t).le_opNorm _)
  rw [he] at hb
  have hk : 0 < β*P.σ := mul_pos hβ P.σ_pos
  have hq : β*P.σ*‖π β s-π β t‖^2 ≤ ‖s-t‖*‖π β s-π β t‖ := by linarith
  have hc : β*P.σ*‖π β s-π β t‖ ≤ ‖s-t‖ := by
    by_cases hz : ‖π β s-π β t‖=0
    · simp [hz]
    · have hn : 0 < ‖π β s-π β t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  have hh : ‖π β s-π β t‖ ≤ ‖s-t‖/(β*P.σ) := (le_div_iff₀ hk).mpr (by simpa [mul_comm] using hc)
  simpa [div_eq_mul_inv, mul_comm] using hh

private lemma remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s t : StrongDual ℝ E) :
    ‖V P β (s+t)-V P β s-t (π β s-P.x0)‖ ≤ (1/(β*P.σ))*‖t‖^2 := by
  have h1 := value_le P π hπ β hβ (s+t) (π β s) (hπ β hβ s).1
  have h2 := value_le P π hπ β hβ s (π β (s+t)) (hπ β hβ (s+t)).1
  simp only [ContinuousLinearMap.add_apply] at h1
  have hn : 0 ≤ V P β (s+t)-V P β s-t (π β s-P.x0) := by
    rw [attained P π hπ β hβ s]; linarith
  rw [Real.norm_of_nonneg hn]
  have hu : V P β (s+t)-V P β s-t (π β s-P.x0) ≤ t (π β (s+t)-π β s) := by
    rw [attained P π hπ β hβ (s+t)]
    simp only [ContinuousLinearMap.add_apply, map_sub] at *
    linarith
  have hl := prox_lip P π hπ β hβ (s+t) s
  simp only [add_sub_cancel_left] at hl
  have hb := (le_abs_self (t (π β (s+t)-π β s))).trans (t.le_opNorm _)
  have hm := mul_le_mul_of_nonneg_left hl (norm_nonneg t)
  nlinarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ Set.univ (V P β) ∧
      (∀ s : StrongDual ℝ E,
        HasFDerivAt (V P β) (ContinuousLinearMap.apply ℝ ℝ (π β s - P.x0)) s) ∧
      (∀ s₁ s₂ : StrongDual ℝ E, ‖π β s₁ - π β s₂‖ ≤ 1 / (β * P.σ) * ‖s₁ - s₂‖) ∧
      (∀ s : StrongDual ℝ E, π β s ∈ P.Q) := by
  refine ⟨?_, ?_, prox_lip P π hπ β hβ, fun s => (hπ β hβ s).1⟩
  · refine ⟨convex_univ, ?_⟩
    intro s hs t ht a b ha hb hab
    let x := π β (a • s+b • t)
    have hx := (hπ β hβ (a • s+b • t)).1
    have h1 := mul_le_mul_of_nonneg_left (value_le P π hπ β hβ s x hx) ha
    have h2 := mul_le_mul_of_nonneg_left (value_le P π hπ β hβ t x hx) hb
    rw [attained P π hπ β hβ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at *
    dsimp [x] at h1 h2
    nlinarith [congrArg (fun r : ℝ => r*(β*P.d x)) hab]
  · intro s
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
    intro ε hε
    have hk : 0 < 1/(β*P.σ) := by positivity [P.σ_pos]
    have he : ∀ᶠ t : StrongDual ℝ E in 𝓝 0, dist t 0 < ε/(1/(β*P.σ)) :=
      Metric.eventually_nhds_iff.mpr ⟨ε/(1/(β*P.σ)), by positivity, fun t ht => ht⟩
    filter_upwards [he] with t ht
    simp only [dist_zero_right] at ht
    change ‖V P β (s+t)-V P β s-t (π β s-P.x0)‖ ≤ ε*‖t‖
    have hh := remainder P π hπ β hβ s t
    have hb : (1/(β*P.σ))*‖t‖ ≤ ε := by simpa [mul_comm] using (le_div_iff₀ hk).mp ht.le
    nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg t)]

#print axioms solution
