-- Prove2me | solution 1 for SoftRobust.Duality.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:51:03.098742+00:00
-- url     : https://prove2.me/submissions/78227fb8-ee1f-4329-84d9-509a3077810a

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model
import Theorems.Thm_SoftRobust_Duality_rhoQ_normalized_convex

open MeasureTheory
open scoped NNReal ENNReal

namespace SoftRobustSDAux

open SoftRobust.Duality

variable {Ω : Type*} [MeasurableSpace Ω]

/-- objective `g(ℚ) = E_ℚ[f] + α(ℚ)` (real part). -/
noncomputable def g (f : Ω → ℝ) (α : ProbabilityMeasure Ω → ℝ≥0∞) (Q : ProbabilityMeasure Ω) : ℝ :=
  (∫ ω, f ω ∂(Q : Measure Ω)) + (α Q).toReal

/-- feasible values at level `ε`. -/
def S (f : Ω → ℝ) (α : ProbabilityMeasure Ω → ℝ≥0∞) (ε : ℝ) : Set ℝ :=
  {r | ∃ Q : ProbabilityMeasure Ω, α Q ≤ ENNReal.ofReal ε ∧ r = g f α Q}

/-- perturbation (value) function. -/
noncomputable def v (f : Ω → ℝ) (α : ProbabilityMeasure Ω → ℝ≥0∞) (ε : ℝ) : ℝ :=
  sInf (S f α ε)

lemma integrable_of_bdd {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C)
    (μ : Measure Ω) [IsFiniteMeasure μ] : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using hC ω)

lemma int_ge {f : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) (Q : ProbabilityMeasure Ω) :
    -C ≤ ∫ ω, f ω ∂(Q : Measure Ω) := by
  have h := norm_integral_le_of_norm_le_const (μ := (Q : Measure Ω)) (C := C) (f := f)
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hC ω)
  simp only [probReal_univ, mul_one, Real.norm_eq_abs] at h
  linarith [neg_abs_le (∫ ω, f ω ∂(Q : Measure Ω))]

lemma S_nonempty {f : Ω → ℝ} {α : ProbabilityMeasure Ω → ℝ≥0∞} (hn : IsNormalizedPenalty α)
    (ε : ℝ) : (S f α ε).Nonempty := by
  obtain ⟨Q, hQ⟩ := hn
  exact ⟨_, Q, by simp [hQ], rfl⟩

lemma S_bdd {f : Ω → ℝ} {α : ProbabilityMeasure Ω → ℝ≥0∞} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C)
    (ε : ℝ) : BddBelow (S f α ε) := by
  refine ⟨-C, ?_⟩
  rintro r ⟨Q, -, rfl⟩
  have := int_ge hC Q
  unfold g
  linarith [ENNReal.toReal_nonneg (a := α Q)]

lemma v_le {f : Ω → ℝ} {α : ProbabilityMeasure Ω → ℝ≥0∞} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C)
    {ε : ℝ} {Q : ProbabilityMeasure Ω} (hQ : α Q ≤ ENNReal.ofReal ε) : v f α ε ≤ g f α Q :=
  csInf_le (S_bdd hC ε) ⟨Q, hQ, rfl⟩

lemma v_anti {f : Ω → ℝ} {α : ProbabilityMeasure Ω → ℝ≥0∞} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C)
    (hn : IsNormalizedPenalty α) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) : v f α ε₂ ≤ v f α ε₁ := by
  apply csInf_le_csInf (S_bdd hC ε₂) (S_nonempty hn ε₁)
  rintro r ⟨Q, hQ, rfl⟩
  exact ⟨Q, hQ.trans (ENNReal.ofReal_le_ofReal h), rfl⟩

lemma int_mix {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C)
    (t : ℝ≥0) (ht : t ≤ 1) (Q₁ Q₂ : ProbabilityMeasure Ω) :
    ∫ ω, f ω ∂((mix t ht Q₁ Q₂ : ProbabilityMeasure Ω) : Measure Ω) =
      (t : ℝ) * ∫ ω, f ω ∂(Q₁ : Measure Ω) + ((1 - t : ℝ≥0) : ℝ) * ∫ ω, f ω ∂(Q₂ : Measure Ω) := by
  rw [coe_mix, integral_add_measure, integral_smul_measure, integral_smul_measure]
  · simp only [ENNReal.coe_toReal, smul_eq_mul]
  · exact (integrable_of_bdd hf hC _).smul_measure (by simp)
  · exact (integrable_of_bdd hf hC _).smul_measure (by simp)

lemma v_convex {f : Ω → ℝ} (hf : Measurable f) {α : ProbabilityMeasure Ω → ℝ≥0∞} {C : ℝ}
    (hC : ∀ ω, |f ω| ≤ C) (hn : IsNormalizedPenalty α) (hc : IsConvexPenalty α) :
    ConvexOn ℝ (Set.Ici 0) (v f α) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_Ici] at hx hy
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨r₁, ⟨Q₁, hQ₁, rfl⟩, h₁⟩ :=
    exists_lt_of_csInf_lt (S_nonempty hn x) (show v f α x < v f α x + η by linarith)
  obtain ⟨r₂, ⟨Q₂, hQ₂, rfl⟩, h₂⟩ :=
    exists_lt_of_csInf_lt (S_nonempty hn y) (show v f α y < v f α y + η by linarith)
  set t : ℝ≥0 := ⟨a, ha⟩
  have ht : t ≤ 1 := by
    show a ≤ 1
    linarith
  have hbt : ((1 - t : ℝ≥0) : ℝ) = b := by
    rw [NNReal.coe_sub ht, NNReal.coe_one]; show 1 - a = b; linarith
  have hfin₁ : α Q₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQ₁
  have hfin₂ : α Q₂ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQ₂
  have hmix := hc t ht Q₁ Q₂
  have hrhs_ne : (t : ℝ≥0∞) * α Q₁ + ((1 - t : ℝ≥0) : ℝ≥0∞) * α Q₂ ≠ ⊤ := by
    apply ENNReal.add_ne_top.2
    exact ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hfin₁, ENNReal.mul_ne_top ENNReal.coe_ne_top hfin₂⟩
  have hrhs_toReal : ((t : ℝ≥0∞) * α Q₁ + ((1 - t : ℝ≥0) : ℝ≥0∞) * α Q₂).toReal =
      a * (α Q₁).toReal + b * (α Q₂).toReal := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin₁)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin₂), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.coe_toReal, ENNReal.coe_toReal, hbt]
    rfl
  have ha1 : (α Q₁).toReal ≤ x := ENNReal.toReal_le_of_le_ofReal hx hQ₁
  have ha2 : (α Q₂).toReal ≤ y := ENNReal.toReal_le_of_le_ofReal hy hQ₂
  have hmixfin : α (mix t ht Q₁ Q₂) ≠ ⊤ := ne_top_of_le_ne_top hrhs_ne hmix
  have hmix_toReal : (α (mix t ht Q₁ Q₂)).toReal ≤ a * (α Q₁).toReal + b * (α Q₂).toReal := by
    rw [← hrhs_toReal]; exact ENNReal.toReal_mono hrhs_ne hmix
  have hfeas : α (mix t ht Q₁ Q₂) ≤ ENNReal.ofReal (a * x + b * y) := by
    rw [← ENNReal.ofReal_toReal hmixfin]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hv := v_le hC hfeas
  have hgmix : g f α (mix t ht Q₁ Q₂) ≤ a * g f α Q₁ + b * g f α Q₂ := by
    unfold g
    rw [int_mix hf hC t ht Q₁ Q₂, hbt]
    have : ((t : ℝ)) = a := rfl
    rw [this]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h₁.le ha, mul_le_mul_of_nonneg_left h₂.le hb]

/-- subgradient of the convex nonincreasing value function at the interior point `δ > 0`. -/
lemma subgrad {φ : ℝ → ℝ} (hconv : ConvexOn ℝ (Set.Ici 0) φ)
    (hanti : ∀ ε₁ ε₂ : ℝ, ε₁ ≤ ε₂ → φ ε₂ ≤ φ ε₁) {δ : ℝ} (hδ : 0 < δ) :
    ∃ l₀ : ℝ, 0 ≤ l₀ ∧ ∀ ε : ℝ, 0 ≤ ε → φ δ - l₀ * (ε - δ) ≤ φ ε := by
  set T : Set ℝ := (fun e => (φ δ - φ e) / (δ - e)) '' Set.Ico 0 δ
  have hTne : T.Nonempty := ⟨_, 0, ⟨le_rfl, hδ⟩, rfl⟩
  have hTle : ∀ r ∈ T, r ≤ 0 := by
    rintro r ⟨e, ⟨he0, heδ⟩, rfl⟩
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [hanti e δ heδ.le]
    · linarith
  have hTbdd : BddAbove T := ⟨0, hTle⟩
  set s := sSup T
  refine ⟨-s, by linarith [csSup_le hTne hTle], ?_⟩
  intro ε hε
  rcases lt_trichotomy ε δ with h | h | h
  · have : (φ δ - φ ε) / (δ - ε) ≤ s := le_csSup hTbdd ⟨ε, ⟨hε, h⟩, rfl⟩
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith
  · subst h; simp
  · have hs : s ≤ (φ ε - φ δ) / (ε - δ) := by
      apply csSup_le hTne
      rintro r ⟨e, ⟨he0, heδ⟩, rfl⟩
      exact hconv.slope_mono_adjacent (Set.mem_Ici.2 he0) (Set.mem_Ici.2 hε) heδ h
    rw [le_div_iff₀ (by linarith)] at hs
    nlinarith

lemma ereal_term_top {I l : ℝ} (hl : 0 ≤ l) :
    ((I : ℝ) : EReal) + ((l + 1 : ℝ) : EReal) * ((⊤ : ℝ≥0∞) : EReal) = ⊤ := by
  rw [EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by linarith), EReal.coe_add_top]

lemma ereal_term_fin {I l : ℝ} {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    ((I : ℝ) : EReal) + ((l + 1 : ℝ) : EReal) * (a : EReal) = ((I + (l + 1) * a.toReal : ℝ) : EReal) := by
  rw [← EReal.coe_ennreal_toReal ha]
  norm_cast

/-- Generic strong duality. -/
theorem strong_duality_gen (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C)
    (α : ProbabilityMeasure Ω → ℝ≥0∞) (hc : IsConvexPenalty α) (hn : IsNormalizedPenalty α)
    (δ : ℝ) (hδ : 0 < δ) :
    IsGreatest
      ((fun l : ℝ => ((-(l * δ) : ℝ) : EReal) +
          ⨅ Q : ProbabilityMeasure Ω,
            ((∫ ω, f ω ∂(Q : Measure Ω) : ℝ) : EReal) +
              ((l + 1 : ℝ) : EReal) * (α Q : EReal)) '' Set.Ici 0)
      (⨅ (Q : ProbabilityMeasure Ω) (_ : α Q ≤ ENNReal.ofReal δ),
        ((∫ ω, f ω ∂(Q : Measure Ω) : ℝ) : EReal) + (α Q : EReal)) := by
  set p := v f α δ with hp
  -- primal value equals `p`
  have hP : (⨅ (Q : ProbabilityMeasure Ω) (_ : α Q ≤ ENNReal.ofReal δ),
        ((∫ ω, f ω ∂(Q : Measure Ω) : ℝ) : EReal) + (α Q : EReal)) = (p : EReal) := by
    apply le_antisymm
    · apply EReal.le_of_forall_lt_iff_le.1
      intro z hz
      have hz' : p < z := by exact_mod_cast hz
      obtain ⟨r, ⟨Q, hQ, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (S_nonempty hn δ) hz'
      have hfin : α Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQ
      refine (iInf₂_le Q hQ).trans ?_
      rw [← EReal.coe_ennreal_toReal hfin]
      have : ((∫ ω, f ω ∂(Q : Measure Ω) : ℝ) : EReal) + (((α Q).toReal : ℝ) : EReal) =
          ((g f α Q : ℝ) : EReal) := by unfold g; norm_cast
      rw [this]; exact_mod_cast hr.le
    · refine le_iInf₂ fun Q hQ => ?_
      have hfin : α Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQ
      rw [← EReal.coe_ennreal_toReal hfin]
      have : ((∫ ω, f ω ∂(Q : Measure Ω) : ℝ) : EReal) + (((α Q).toReal : ℝ) : EReal) =
          ((g f α Q : ℝ) : EReal) := by unfold g; norm_cast
      rw [this]; exact_mod_cast v_le hC hQ
  rw [hP]
  -- weak duality
  have hweak : ∀ l : ℝ, 0 ≤ l → ((-(l * δ) : ℝ) : EReal) +
      (⨅ Q : ProbabilityMeasure Ω, ((∫ ω, f ω ∂(Q : Measure Ω) : ℝ) : EReal) +
        ((l + 1 : ℝ) : EReal) * (α Q : EReal)) ≤ (p : EReal) := by
    intro l hl
    rw [← hP]
    refine le_iInf₂ fun Q hQ => ?_
    have hfin : α Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQ
    have haδ : (α Q).toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ.le hQ
    refine (add_le_add le_rfl (iInf_le (fun Q : ProbabilityMeasure Ω =>
      ((∫ ω, f ω ∂(Q : Measure Ω) : ℝ) : EReal) + ((l + 1 : ℝ) : EReal) * (α Q : EReal)) Q)).trans ?_
    rw [ereal_term_fin hfin, ← EReal.coe_ennreal_toReal hfin]
    have h0 : 0 ≤ (α Q).toReal := ENNReal.toReal_nonneg
    have : -(l * δ) + ((∫ ω, f ω ∂(Q : Measure Ω)) + (l + 1) * (α Q).toReal) ≤
        (∫ ω, f ω ∂(Q : Measure Ω)) + (α Q).toReal := by nlinarith
    exact_mod_cast this
  -- dual attainment
  obtain ⟨l₀, hl₀, hsub⟩ := subgrad (v_convex hf hC hn hc) (fun _ _ h => v_anti hC hn h) hδ
  refine ⟨⟨l₀, hl₀, le_antisymm (hweak l₀ hl₀) ?_⟩, ?_⟩
  · have hinf : ((p + l₀ * δ : ℝ) : EReal) ≤ ⨅ Q : ProbabilityMeasure Ω,
        ((∫ ω, f ω ∂(Q : Measure Ω) : ℝ) : EReal) + ((l₀ + 1 : ℝ) : EReal) * (α Q : EReal) := by
      refine le_iInf fun Q => ?_
      by_cases hfin : α Q = ⊤
      · rw [hfin, ereal_term_top hl₀]; exact le_top
      · rw [ereal_term_fin hfin]
        have hQa : α Q ≤ ENNReal.ofReal (α Q).toReal := (ENNReal.ofReal_toReal hfin).ge
        have h1 := v_le hC hQa
        have h2 := hsub (α Q).toReal ENNReal.toReal_nonneg
        have : p + l₀ * δ ≤ (∫ ω, f ω ∂(Q : Measure Ω)) + (l₀ + 1) * (α Q).toReal := by
          unfold g at h1; nlinarith
        exact_mod_cast this
    calc (p : EReal) = ((-(l₀ * δ) : ℝ) : EReal) + ((p + l₀ * δ : ℝ) : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
      _ ≤ _ := add_le_add le_rfl hinf
  · rintro _ ⟨l, hl, rfl⟩
    exact hweak l hl

end SoftRobustSDAux

open SoftRobust.Duality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (M : Model Ω n m)
    (𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)) (h𝒬 : IsAdmissibleFamily 𝒬)
    (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M.X) :
    IsGreatest
      ((fun l : ℝ => ((-(l * δ) : ℝ) : EReal) +
          ⨅ Q : ProbabilityMeasure Ω,
            ((∫ ω, M.payoff x ω ∂(Q : Measure Ω) : ℝ) : EReal) +
              ((l + 1 : ℝ) : EReal) * (penaltyOfFamily 𝒬 Q : EReal)) '' Set.Ici 0)
      (⨅ (Q : ProbabilityMeasure Ω) (_ : penaltyOfFamily 𝒬 Q ≤ ENNReal.ofReal δ),
        ((∫ ω, M.payoff x ω ∂(Q : Measure Ω) : ℝ) : EReal) + (penaltyOfFamily 𝒬 Q : EReal)) := by
  obtain ⟨-, ⟨hconv, -⟩, hnorm⟩ := SoftRobust.Duality.rhoQ_normalized_convex 𝒬 h𝒬
  obtain ⟨C, hC⟩ := M.payoff_bounded x hx
  exact SoftRobustSDAux.strong_duality_gen (M.payoff x) (M.payoff_measurable x hx) C hC
    (penaltyOfFamily 𝒬) hconv hnorm δ hδ
