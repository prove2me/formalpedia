-- Prove2me | solution 1 for SepMeasures.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:12:57.440086+00:00
-- url     : https://prove2.me/submissions/319249d7-2e1e-44e3-af68-2d9d2f845b81

import Mathlib
import Definitions.Def_SepMeasures_Hyp
import Theorems.Thm_SepMeasures_lemma_2_4
import Theorems.Thm_SepMeasures_lemma_2_5
import Theorems.Thm_SepMeasures_claim_3_4
import Theorems.Thm_SepMeasures_claim_3_5

open MeasureTheory SepMeasures

namespace AuxEq8

def negHyp {d : ℕ} (H : Hyp d) : Hyp d :=
  ⟨-H.u, -H.c, neg_ne_zero.mpr H.hu⟩

lemma negHyp_set {d : ℕ} (H : Hyp d) : (negHyp H).set = H.set := by
  ext x
  simp only [Hyp.set, negHyp, inner_neg_left]
  change -inner ℝ H.u x = -H.c ↔ inner ℝ H.u x = H.c
  constructor <;> intro h <;> linarith

lemma negHyp_sign {d : ℕ} (H : Hyp d) (x : E d) : (negHyp H).sign x = -H.sign x := by
  simp only [Hyp.sign, negHyp, inner_neg_left]
  by_cases h1 : -H.c < -inner ℝ H.u x
  · have h2 : inner ℝ H.u x < H.c := by linarith
    have h3 : ¬ H.c < inner ℝ H.u x := by linarith
    simp [h1, h2, h3]
  · by_cases h2 : -inner ℝ H.u x < -H.c
    · have h3 : H.c < inner ℝ H.u x := by linarith
      simp [h1, h2, h3]
    · have h3 : ¬ H.c < inner ℝ H.u x := by linarith
      have h4 : ¬ inner ℝ H.u x < H.c := by linarith
      simp [h1, h2, h3, h4]

lemma measurableSet_hyp_pos {d : ℕ} (K : Hyp d) : MeasurableSet K.pos :=
  isOpen_lt continuous_const (continuous_const.inner continuous_id) |>.measurableSet

lemma measurableSet_hyp_neg {d : ℕ} (K : Hyp d) : MeasurableSet K.neg :=
  isOpen_lt (continuous_const.inner continuous_id) continuous_const |>.measurableSet

lemma measurable_sign {d : ℕ} (K : Hyp d) : Measurable K.sign := by
  unfold Hyp.sign
  exact Measurable.ite (measurableSet_hyp_pos K) measurable_const
    (Measurable.ite (measurableSet_hyp_neg K) measurable_const measurable_const)

lemma sign_mem_Icc {d : ℕ} (K : Hyp d) (x : E d) : K.sign x ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold Hyp.sign
  split_ifs <;> constructor <;> norm_num

lemma sign_sq_eq_one {d : ℕ} (K : Hyp d) {x : E d} (hx : x ∉ K.set) :
    K.sign x * K.sign x = 1 := by
  have hne : inner ℝ K.u x ≠ K.c := hx
  unfold Hyp.sign
  rcases lt_or_gt_of_ne hne with hl | hg
  · simp [hl, not_lt.mpr hl.le]
  · simp [hg]

lemma fair_sign_probs {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {U : Ω → ℝ} (hU : Measurable U)
    (hae : ∀ᵐ ω ∂ρ, U ω = -1 ∨ U ω = 1) (hint : ∫ ω, U ω ∂ρ = 0) :
    ρ {ω | U ω = 1} = 1 / 2 ∧ ρ {ω | U ω = -1} = 1 / 2 := by
  set A₁ : Set Ω := {ω | U ω = 1}
  set A₂ : Set Ω := {ω | U ω = -1}
  have hA₁ : MeasurableSet A₁ := hU (measurableSet_singleton 1)
  have hA₂ : MeasurableSet A₂ := hU (measurableSet_singleton (-1))
  have hdisj : Disjoint A₁ A₂ := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    change U ω = 1 at h1
    change U ω = -1 at h2
    linarith
  have hcompl : ρ (A₁ ∪ A₂)ᶜ = 0 := by
    have hmem : ∀ᵐ ω ∂ρ, ω ∈ A₁ ∪ A₂ := by
      filter_upwards [hae] with ω hω
      exact hω.symm
    rw [ae_iff] at hmem
    exact measure_mono_null (fun ω hω => hω) hmem
  have huniv : ρ (A₁ ∪ A₂) = 1 :=
    (prob_compl_eq_zero_iff (hA₁.union hA₂)).mp hcompl
  have hsum : ρ.real A₁ + ρ.real A₂ = 1 := by
    rw [← measureReal_union hdisj hA₂, measureReal_def, huniv, ENNReal.toReal_one]
  have heq_ae : U =ᵐ[ρ] fun ω => A₁.indicator (1 : Ω → ℝ) ω -
      A₂.indicator (1 : Ω → ℝ) ω := by
    filter_upwards [hae] with ω hω
    rcases hω with hneg | hpos
    · have h1 : ω ∉ A₁ := by change ¬ U ω = 1; linarith
      have h2 : ω ∈ A₂ := hneg
      simp [hneg, h1, h2]
    · have h1 : ω ∈ A₁ := hpos
      have h2 : ω ∉ A₂ := by change ¬ U ω = -1; linarith
      simp [hpos, h1, h2]
  have hdiff : ρ.real A₁ - ρ.real A₂ = 0 := by
    have hi1 : Integrable (A₁.indicator (1 : Ω → ℝ)) ρ :=
      (integrable_const 1).indicator hA₁
    have hi2 : Integrable (A₂.indicator (1 : Ω → ℝ)) ρ :=
      (integrable_const 1).indicator hA₂
    have h0 := hint
    rw [integral_congr_ae heq_ae, integral_sub hi1 hi2,
      integral_indicator_one hA₁, integral_indicator_one hA₂] at h0
    exact h0
  have hr1 : ρ.real A₁ = 1 / 2 := by linarith
  have hr2 : ρ.real A₂ = 1 / 2 := by linarith
  have henn : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat, one_div]
  constructor
  · rw [← ofReal_measureReal, hr1, henn]
  · rw [← ofReal_measureReal, hr2, henn]

lemma apply_claim_3_4_single (ρ : Measure (E 2)) [IsProbabilityMeasure ρ]
    (H K : Hyp 2) (hH : ρ H.set = 0) (bH : ∫ x, H.sign x ∂ρ = 0) :
    |∫ x, K.sign x ∂ρ| + |∫ x, K.sign x * H.sign x ∂ρ| ≤ 1 := by
  have hae : ∀ᵐ x ∂ρ, H.sign x = -1 ∨ H.sign x = 1 := by
    have hnot : ∀ᵐ x ∂ρ, x ∉ H.set := by rw [ae_iff]; simpa using hH
    filter_upwards [hnot] with x hx
    have hne : inner ℝ H.u x ≠ H.c := hx
    unfold Hyp.sign
    rcases lt_or_gt_of_ne hne with hl | hg
    · left; simp [hl, not_lt.mpr hl.le]
    · right; simp [hg]
  obtain ⟨hp1, hpm1⟩ := fair_sign_probs ρ (measurable_sign H) hae bH
  have h := SepMeasures.claim_3_4 ρ H.sign K.sign (measurable_sign H) (measurable_sign K)
    hp1 hpm1 (ae_of_all ρ (sign_mem_Icc K))
  have hcomm : (∫ x, H.sign x * K.sign x ∂ρ) = ∫ x, K.sign x * H.sign x ∂ρ := by
    congr 1; ext x; ring
  rwa [hcomm] at h

lemma apply_claim_3_4_prod (ρ : Measure (E 2)) [IsProbabilityMeasure ρ]
    (H₁ H₂ K : Hyp 2) (hH₁ : ρ H₁.set = 0) (hH₂ : ρ H₂.set = 0)
    (b₁₂ : ∫ x, H₁.sign x * H₂.sign x ∂ρ = 0) :
    |∫ x, K.sign x * H₁.sign x ∂ρ| + |∫ x, K.sign x * H₂.sign x ∂ρ| ≤ 1 := by
  let U : E 2 → ℝ := fun x => H₁.sign x * H₂.sign x
  let W : E 2 → ℝ := fun x => K.sign x * H₁.sign x
  have hU : Measurable U := (measurable_sign H₁).mul (measurable_sign H₂)
  have hW : Measurable W := (measurable_sign K).mul (measurable_sign H₁)
  have hnot1 : ∀ᵐ x ∂ρ, x ∉ H₁.set := by rw [ae_iff]; simpa using hH₁
  have hnot2 : ∀ᵐ x ∂ρ, x ∉ H₂.set := by rw [ae_iff]; simpa using hH₂
  have haeU : ∀ᵐ x ∂ρ, U x = -1 ∨ U x = 1 := by
    filter_upwards [hnot1, hnot2] with x hx1 hx2
    have s1 : H₁.sign x * H₁.sign x = 1 := sign_sq_eq_one H₁ hx1
    have s2 : H₂.sign x * H₂.sign x = 1 := sign_sq_eq_one H₂ hx2
    have hsq : U x * U x = 1 := by
      change (H₁.sign x * H₂.sign x) * (H₁.sign x * H₂.sign x) = 1
      calc (H₁.sign x * H₂.sign x) * (H₁.sign x * H₂.sign x)
        _ = (H₁.sign x * H₁.sign x) * (H₂.sign x * H₂.sign x) := by ring
        _ = 1 * 1 := by rw [s1, s2]
        _ = 1 := one_mul 1
    rcases mul_self_eq_one_iff.mp hsq with h1 | hm1
    · exact Or.inr h1
    · exact Or.inl hm1
  have hWb : ∀ᵐ x ∂ρ, W x ∈ Set.Icc (-1 : ℝ) 1 := by
    refine ae_of_all ρ fun x => ?_
    have h1 := sign_mem_Icc K x
    have h2 := sign_mem_Icc H₁ x
    rw [Set.mem_Icc] at h1 h2 ⊢
    dsimp [W]
    constructor <;> nlinarith
  obtain ⟨hp1, hpm1⟩ := fair_sign_probs ρ hU haeU b₁₂
  have h := SepMeasures.claim_3_4 ρ U W hU hW hp1 hpm1 hWb
  have haeUW : (fun x => U x * W x) =ᵐ[ρ] fun x => K.sign x * H₂.sign x := by
    filter_upwards [hnot1] with x hx1
    dsimp [U, W]
    have s1 := sign_sq_eq_one H₁ hx1
    calc (H₁.sign x * H₂.sign x) * (K.sign x * H₁.sign x)
      _ = K.sign x * H₂.sign x * (H₁.sign x * H₁.sign x) := by ring
      _ = K.sign x * H₂.sign x := by rw [s1, mul_one]
  rwa [integral_congr_ae haeUW] at h

lemma no_four_quadrants_on_line (α₁ β₁ α₂ β₂ t₁ t₂ t₃ t₄ : ℝ)
    (h11 : 0 < α₁ * t₁ + β₁ ∧ 0 < α₂ * t₁ + β₂)
    (h12 : 0 < α₁ * t₂ + β₁ ∧ α₂ * t₂ + β₂ < 0)
    (h21 : α₁ * t₃ + β₁ < 0 ∧ 0 < α₂ * t₃ + β₂)
    (h22 : α₁ * t₄ + β₁ < 0 ∧ α₂ * t₄ + β₂ < 0) : False := by
  have hα₁ : α₁ ≠ 0 := by intro h; subst h; linarith [h11.1, h21.1]
  have hα₂ : α₂ ≠ 0 := by intro h; subst h; linarith [h11.2, h12.2]
  rcases lt_or_gt_of_ne hα₁ with h1neg | h1pos <;> rcases lt_or_gt_of_ne hα₂ with h2neg | h2pos
  · have ht1 : t₁ < t₄ := by nlinarith [h11.1, h22.1]
    nlinarith [h11.2, h22.2, ht1]
  · have ht1 : t₂ < t₃ := by nlinarith [h12.1, h21.1]
    nlinarith [h12.2, h21.2, ht1]
  · have ht1 : t₃ < t₂ := by nlinarith [h12.1, h21.1]
    nlinarith [h12.2, h21.2, ht1]
  · have ht1 : t₄ < t₁ := by nlinarith [h11.1, h22.1]
    nlinarith [h11.2, h22.2, ht1]

lemma sign_eq_one_iff {d : ℕ} (H : Hyp d) (x : E d) :
    H.sign x = 1 ↔ H.c < inner ℝ H.u x := by
  unfold Hyp.sign
  split_ifs with h1 h2
  · simp [h1]
  · constructor <;> intro h <;> norm_num at h <;> exact False.elim (h1 h)
  · constructor <;> intro h <;> norm_num at h <;> exact False.elim (h1 h)

lemma sign_eq_neg_one_iff {d : ℕ} (H : Hyp d) (x : E d) :
    H.sign x = -1 ↔ inner ℝ H.u x < H.c := by
  unfold Hyp.sign
  split_ifs with h1 h2
  · constructor
    · intro h; norm_num at h
    · intro h; linarith
  · simp [h2]
  · constructor <;> intro h <;> norm_num at h <;> exact False.elim (h2 h)

lemma exists_crossing_in_quadrant {μ ν : Measure (E 2)} {H₁ H₂ K : Hyp 2} {a b : ℝ}
    (ha : a = -1 ∨ a = 1) (hb : b = -1 ∨ b = 1)
    (hxpos : 0 < μ {x | H₁.sign x = a ∧ H₂.sign x = b ∧ K.sign x = b})
    (hypos : 0 < ν {y | H₁.sign y = a ∧ H₂.sign y = b ∧ K.sign y = -b}) :
    ∃ z : E 2, inner ℝ K.u z = K.c ∧
      0 < a * (inner ℝ H₁.u z - H₁.c) ∧ 0 < b * (inner ℝ H₂.u z - H₂.c) := by
  obtain ⟨x, hx1, hx2, hxK⟩ := nonempty_of_measure_ne_zero hxpos.ne'
  obtain ⟨y, hy1, hy2, hyK⟩ := nonempty_of_measure_ne_zero hypos.ne'
  have hax : 0 < a * (inner ℝ H₁.u x - H₁.c) := by
    rcases ha with rfl | rfl
    · have := (sign_eq_neg_one_iff H₁ x).mp hx1; linarith
    · have := (sign_eq_one_iff H₁ x).mp hx1; linarith
  have hay : 0 < a * (inner ℝ H₁.u y - H₁.c) := by
    rcases ha with rfl | rfl
    · have := (sign_eq_neg_one_iff H₁ y).mp hy1; linarith
    · have := (sign_eq_one_iff H₁ y).mp hy1; linarith
  have hbx : 0 < b * (inner ℝ H₂.u x - H₂.c) := by
    rcases hb with rfl | rfl
    · have := (sign_eq_neg_one_iff H₂ x).mp hx2; linarith
    · have := (sign_eq_one_iff H₂ x).mp hx2; linarith
  have hby : 0 < b * (inner ℝ H₂.u y - H₂.c) := by
    rcases hb with rfl | rfl
    · have := (sign_eq_neg_one_iff H₂ y).mp hy2; linarith
    · have := (sign_eq_one_iff H₂ y).mp hy2; linarith
  have hKx : 0 < b * (inner ℝ K.u x - K.c) := by
    rcases hb with rfl | rfl
    · have := (sign_eq_neg_one_iff K x).mp hxK; linarith
    · have := (sign_eq_one_iff K x).mp hxK; linarith
  have hKy : b * (inner ℝ K.u y - K.c) < 0 := by
    rcases hb with rfl | rfl
    · norm_num at hyK; have := (sign_eq_one_iff K y).mp hyK; linarith
    · have := (sign_eq_neg_one_iff K y).mp hyK; linarith
  set fx := inner ℝ K.u x - K.c
  set fy := inner ℝ K.u y - K.c
  have hdenom : b * (fx - fy) > 0 := by linarith
  have hfx_ne_fy : fx - fy ≠ 0 := by intro h; rw [h, mul_zero] at hdenom; exact lt_irrefl 0 hdenom
  let θ : ℝ := fx / (fx - fy)
  have hθ0 : 0 < θ := by
    have : θ = (b * fx) / (b * (fx - fy)) := by
      have hbne : b ≠ 0 := by rcases hb with rfl | rfl <;> norm_num
      dsimp only [θ]
      field_simp [hbne, hfx_ne_fy]
    rw [this]
    exact div_pos hKx hdenom
  have hθ1 : 0 < 1 - θ := by
    have : 1 - θ = (-b * fy) / (b * (fx - fy)) := by
      have hbne : b ≠ 0 := by rcases hb with rfl | rfl <;> norm_num
      dsimp only [θ]
      field_simp [hbne, hfx_ne_fy]
      ring
    rw [this]
    exact div_pos (by linarith) hdenom
  refine ⟨(1 - θ) • x + θ • y, ?_, ?_, ?_⟩
  · have hlin : inner ℝ K.u ((1 - θ) • x + θ • y) =
        (1 - θ) * inner ℝ K.u x + θ * inner ℝ K.u y := by
      rw [inner_add_right, inner_smul_right, inner_smul_right]
    rw [hlin]
    dsimp [θ, fx, fy] at hfx_ne_fy ⊢
    field_simp [hfx_ne_fy]
    ring
  · have hlin : inner ℝ H₁.u ((1 - θ) • x + θ • y) - H₁.c =
        (1 - θ) * (inner ℝ H₁.u x - H₁.c) + θ * (inner ℝ H₁.u y - H₁.c) := by
      rw [inner_add_right, inner_smul_right, inner_smul_right]; ring
    rw [hlin, mul_add, ← mul_assoc, ← mul_assoc]
    have h1 : 0 < (1 - θ) * (a * (inner ℝ H₁.u x - H₁.c)) := mul_pos hθ1 hax
    have h2 : 0 < θ * (a * (inner ℝ H₁.u y - H₁.c)) := mul_pos hθ0 hay
    linarith
  · have hlin : inner ℝ H₂.u ((1 - θ) • x + θ • y) - H₂.c =
        (1 - θ) * (inner ℝ H₂.u x - H₂.c) + θ * (inner ℝ H₂.u y - H₂.c) := by
      rw [inner_add_right, inner_smul_right, inner_smul_right]; ring
    rw [hlin, mul_add, ← mul_assoc, ← mul_assoc]
    have h1 : 0 < (1 - θ) * (b * (inner ℝ H₂.u x - H₂.c)) := mul_pos hθ1 hbx
    have h2 : 0 < θ * (b * (inner ℝ H₂.u y - H₂.c)) := mul_pos hθ0 hby
    linarith

lemma line_param_E2 (K : Hyp 2) (z₀ z : E 2)
    (hz₀ : inner ℝ K.u z₀ = K.c) (hz : inner ℝ K.u z = K.c) :
    ∃ t : ℝ, z = z₀ + t • (!₂[-K.u 1, K.u 0] : E 2) := by
  have hu_sum : K.u 0 ^ 2 + K.u 1 ^ 2 ≠ 0 := by
    intro h
    apply K.hu
    ext i
    fin_cases i
    · change K.u 0 = 0; nlinarith [sq_nonneg (K.u 0), sq_nonneg (K.u 1)]
    · change K.u 1 = 0; nlinarith [sq_nonneg (K.u 0), sq_nonneg (K.u 1)]
  have horth : K.u 0 * (z 0 - z₀ 0) + K.u 1 * (z 1 - z₀ 1) = 0 := by
    have hdiff : inner ℝ K.u (z - z₀) = 0 := by rw [inner_sub_right, hz, hz₀, sub_self]
    have h2 := hdiff
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      star_trivial, PiLp.sub_apply] at h2
    linarith
  refine ⟨(-K.u 1 * (z 0 - z₀ 0) + K.u 0 * (z 1 - z₀ 1)) / (K.u 0 ^ 2 + K.u 1 ^ 2), ?_⟩
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero]
    field_simp [hu_sum]
    linear_combination K.u 0 * horth
  · simp only [Fin.mk_one, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp [hu_sum]
    linear_combination K.u 1 * horth

lemma phi_le_one_oriented (μ ν : Measure (E 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H₁ H₂ H₃ K : Hyp 2)
    (hμ₁ : μ H₁.set = 0) (hμ₂ : μ H₂.set = 0) (hμ₃ : μ H₃.set = 0) (hμK : μ K.set = 0)
    (hν₁ : ν H₁.set = 0) (hν₂ : ν H₂.set = 0) (hν₃ : ν H₃.set = 0) (hνK : ν K.set = 0)
    (bμ₁ : ∫ x, H₁.sign x ∂μ = 0) (bμ₂ : ∫ x, H₂.sign x ∂μ = 0)
    (bμ₁₃ : ∫ x, H₁.sign x * H₃.sign x ∂μ = 0)
    (bν₁ : ∫ y, H₁.sign y ∂ν = 0) (bν₃ : ∫ y, H₃.sign y ∂ν = 0)
    (bν₁₂ : ∫ y, H₁.sign y * H₂.sign y ∂ν = 0)
    (hp₂_nn : 0 ≤ ∫ x, K.sign x * H₂.sign x ∂μ)
    (hp₃_nn : 0 ≤ ∫ x, K.sign x * H₃.sign x ∂μ) :
    (∫ x, K.sign x ∂μ) * (∫ y, K.sign y ∂ν)
        - ((∫ x, K.sign x * H₁.sign x ∂μ) * (∫ y, K.sign y * H₁.sign y ∂ν)
          + (∫ x, K.sign x * H₂.sign x ∂μ) * (∫ y, K.sign y * H₂.sign y ∂ν)
          + (∫ x, K.sign x * H₃.sign x ∂μ) * (∫ y, K.sign y * H₃.sign y ∂ν)) ≤ 1 := by
  set p₀ := ∫ x, K.sign x ∂μ
  set q₀ := ∫ y, K.sign y ∂ν
  set p₁ := ∫ x, K.sign x * H₁.sign x ∂μ
  set q₁ := ∫ y, K.sign y * H₁.sign y ∂ν
  set p₂ := ∫ x, K.sign x * H₂.sign x ∂μ
  set q₂ := ∫ y, K.sign y * H₂.sign y ∂ν
  set p₃ := ∫ x, K.sign x * H₃.sign x ∂μ
  set q₃ := ∫ y, K.sign y * H₃.sign y ∂ν
  have hA : |p₀| + |p₁| ≤ 1 := apply_claim_3_4_single μ H₁ K hμ₁ bμ₁
  have _hB : |q₀| + |q₁| ≤ 1 := apply_claim_3_4_single ν H₁ K hν₁ bν₁
  have hC : |p₀| + |p₂| ≤ 1 := apply_claim_3_4_single μ H₂ K hμ₂ bμ₂
  have hD : |q₀| + |q₃| ≤ 1 := apply_claim_3_4_single ν H₃ K hν₃ bν₃
  have hE : |p₁| + |p₃| ≤ 1 := apply_claim_3_4_prod μ H₁ H₃ K hμ₁ hμ₃ bμ₁₃
  have hF : |q₁| + |q₂| ≤ 1 := apply_claim_3_4_prod ν H₁ H₂ K hν₁ hν₂ bν₁₂
  have hp₂_abs : |p₂| = p₂ := abs_of_nonneg hp₂_nn
  have hp₃_abs : |p₃| = p₃ := abs_of_nonneg hp₃_nn
  by_contra hgt
  push Not at hgt
  have hp0q0 : p₀ * q₀ ≤ |p₀| * |q₀| := by rw [← abs_mul]; exact le_abs_self _
  have hp3q3 : -(p₃ * q₃) ≤ p₃ * |q₃| := by
    have : -(p₃ * q₃) = p₃ * (-q₃) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left (neg_le_abs q₃) hp₃_nn
  have hp1q1 : -(p₁ * q₁) ≤ |p₁| * |q₁| := by
    have : -(p₁ * q₁) ≤ |p₁ * q₁| := neg_le_abs _
    rwa [abs_mul] at this
  have hp2q2 : -(p₂ * q₂) ≤ p₂ * |q₂| := by
    have : -(p₂ * q₂) = p₂ * (-q₂) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left (neg_le_abs q₂) hp₂_nn
  have h9a : p₀ * q₀ - p₃ * q₃ ≤ max |p₀| p₃ := by
    have hm1 : |p₀| ≤ max |p₀| p₃ := le_max_left _ _
    have hm2 : p₃ ≤ max |p₀| p₃ := le_max_right _ _
    have hnn : 0 ≤ max |p₀| p₃ := (abs_nonneg p₀).trans hm1
    calc p₀ * q₀ - p₃ * q₃ ≤ |p₀| * |q₀| + p₃ * |q₃| := by linarith
      _ ≤ max |p₀| p₃ * |q₀| + max |p₀| p₃ * |q₃| :=
          add_le_add (mul_le_mul_of_nonneg_right hm1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hm2 (abs_nonneg _))
      _ = max |p₀| p₃ * (|q₀| + |q₃|) := by ring
      _ ≤ max |p₀| p₃ * 1 := mul_le_mul_of_nonneg_left hD hnn
      _ = max |p₀| p₃ := mul_one _
  have h9b : -(p₁ * q₁) - p₂ * q₂ ≤ max |p₁| p₂ := by
    have hm1 : |p₁| ≤ max |p₁| p₂ := le_max_left _ _
    have hm2 : p₂ ≤ max |p₁| p₂ := le_max_right _ _
    have hnn : 0 ≤ max |p₁| p₂ := (abs_nonneg p₁).trans hm1
    calc -(p₁ * q₁) - p₂ * q₂ ≤ |p₁| * |q₁| + p₂ * |q₂| := by linarith
      _ ≤ max |p₁| p₂ * |q₁| + max |p₁| p₂ * |q₂| :=
          add_le_add (mul_le_mul_of_nonneg_right hm1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hm2 (abs_nonneg _))
      _ = max |p₁| p₂ * (|q₁| + |q₂|) := by ring
      _ ≤ max |p₁| p₂ * 1 := mul_le_mul_of_nonneg_left hF hnn
      _ = max |p₁| p₂ := mul_one _
  have hp23 : 1 < p₂ + p₃ := by
    have hsum : max |p₀| p₃ + max |p₁| p₂ > 1 := by linarith
    rcases max_cases |p₀| p₃ with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases max_cases |p₁| p₂ with ⟨h2, _⟩ | ⟨h2, _⟩
    · linarith [hA]
    · linarith [hC, hp₂_abs]
    · linarith [hE, hp₃_abs]
    · linarith
  have h11 : p₀ * q₀ - (p₁ * q₁ + p₂ * q₂ + p₃ * q₃) ≤
      1 + (p₂ + p₃ - 1) * (-q₂ - q₃ - 1) := by
    have hp0_le : |p₀| ≤ 1 - p₂ := by linarith [hC, hp₂_abs]
    have hp1_le : |p₁| ≤ 1 - p₃ := by linarith [hE, hp₃_abs]
    have h1mp2 : 0 ≤ 1 - p₂ := by linarith [abs_nonneg p₀]
    have h1mp3 : 0 ≤ 1 - p₃ := by linarith [abs_nonneg p₁]
    have h10 : p₀ * q₀ - p₁ * q₁ ≤ (1 - p₂) * |q₀| + (1 - p₃) * |q₁| := by
      calc p₀ * q₀ - p₁ * q₁ ≤ |p₀| * |q₀| + |p₁| * |q₁| := by linarith
        _ ≤ (1 - p₂) * |q₀| + (1 - p₃) * |q₁| :=
            add_le_add (mul_le_mul_of_nonneg_right hp0_le (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hp1_le (abs_nonneg _))
    have hq3_le : -q₃ ≤ |q₃| := neg_le_abs q₃
    have hq2_le : -q₂ ≤ |q₂| := neg_le_abs q₂
    calc p₀ * q₀ - (p₁ * q₁ + p₂ * q₂ + p₃ * q₃)
      _ ≤ (1 - p₂) * |q₀| + (1 - p₃) * |q₁| - p₂ * q₂ - p₃ * q₃ := by linarith
      _ = (1 - p₂) * (|q₀| + (-q₃)) + (1 - p₃) * (|q₁| + (-q₂)) -
            (p₂ + p₃ - 1) * (q₂ + q₃) := by ring
      _ ≤ (1 - p₂) * (|q₀| + |q₃|) + (1 - p₃) * (|q₁| + |q₂|) -
            (p₂ + p₃ - 1) * (q₂ + q₃) := by nlinarith
      _ ≤ (1 - p₂) * 1 + (1 - p₃) * 1 - (p₂ + p₃ - 1) * (q₂ + q₃) := by nlinarith
      _ = 1 + (p₂ + p₃ - 1) * (-q₂ - q₃ - 1) := by ring
  have hq23 : 1 < -q₂ - q₃ := by
    have hpos : 0 < (p₂ + p₃ - 1) * (-q₂ - q₃ - 1) := by linarith
    have hp_pos : 0 < p₂ + p₃ - 1 := by linarith
    have := pos_of_mul_pos_right hpos hp_pos.le
    linarith
  have hc35 := SepMeasures.claim_3_5 2 (by norm_num) μ ν H₁ H₂ H₃ K
    hμ₁ hμ₂ hμ₃ hμK hν₁ hν₂ hν₃ hνK bμ₁ bμ₂ bμ₁₃ bν₁ bν₃ bν₁₂ hp23 hq23
  obtain ⟨z11, hz11K, hz11_1, hz11_2⟩ := exists_crossing_in_quadrant (Or.inr rfl) (Or.inr rfl)
    (hc35 1 (by simp) 1 (by simp)).1 (hc35 1 (by simp) 1 (by simp)).2
  obtain ⟨z12, hz12K, hz12_1, hz12_2⟩ := exists_crossing_in_quadrant (Or.inr rfl) (Or.inl rfl)
    (hc35 1 (by simp) (-1) (by simp)).1 (hc35 1 (by simp) (-1) (by simp)).2
  obtain ⟨z21, hz21K, hz21_1, hz21_2⟩ := exists_crossing_in_quadrant (Or.inl rfl) (Or.inr rfl)
    (hc35 (-1) (by simp) 1 (by simp)).1 (hc35 (-1) (by simp) 1 (by simp)).2
  obtain ⟨z22, hz22K, hz22_1, hz22_2⟩ := exists_crossing_in_quadrant (Or.inl rfl) (Or.inl rfl)
    (hc35 (-1) (by simp) (-1) (by simp)).1 (hc35 (-1) (by simp) (-1) (by simp)).2
  obtain ⟨t₂, hz12_eq⟩ := line_param_E2 K z11 z12 hz11K hz12K
  obtain ⟨t₃, hz21_eq⟩ := line_param_E2 K z11 z21 hz11K hz21K
  obtain ⟨t₄, hz22_eq⟩ := line_param_E2 K z11 z22 hz11K hz22K
  rw [hz12_eq] at hz12_1 hz12_2
  rw [hz21_eq] at hz21_1 hz21_2
  rw [hz22_eq] at hz22_1 hz22_2
  let v : E 2 := !₂[-K.u 1, K.u 0]
  have hlin1 : ∀ t : ℝ, inner ℝ H₁.u (z11 + t • v) - H₁.c =
      (inner ℝ H₁.u v) * t + (inner ℝ H₁.u z11 - H₁.c) := by
    intro t; rw [inner_add_right, inner_smul_right]; ring
  have hlin2 : ∀ t : ℝ, inner ℝ H₂.u (z11 + t • v) - H₂.c =
      (inner ℝ H₂.u v) * t + (inner ℝ H₂.u z11 - H₂.c) := by
    intro t; rw [inner_add_right, inner_smul_right]; ring
  exact no_four_quadrants_on_line (inner ℝ H₁.u v) (inner ℝ H₁.u z11 - H₁.c)
    (inner ℝ H₂.u v) (inner ℝ H₂.u z11 - H₂.c) 0 t₂ t₃ t₄
    ⟨by linarith, by linarith⟩
    ⟨by linarith [hlin1 t₂], by linarith [hlin2 t₂]⟩
    ⟨by linarith [hlin1 t₃], by linarith [hlin2 t₃]⟩
    ⟨by linarith [hlin1 t₄], by linarith [hlin2 t₄]⟩

end AuxEq8

theorem solution (μ ν : Measure (E 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H₁ H₂ H₃ K : Hyp 2)
    (hμ₁ : μ H₁.set = 0) (hμ₂ : μ H₂.set = 0) (hμ₃ : μ H₃.set = 0) (hμK : μ K.set = 0)
    (hν₁ : ν H₁.set = 0) (hν₂ : ν H₂.set = 0) (hν₃ : ν H₃.set = 0) (hνK : ν K.set = 0)
    (bμ₁ : ∫ x, H₁.sign x ∂μ = 0) (bμ₂ : ∫ x, H₂.sign x ∂μ = 0)
    (bμ₁₃ : ∫ x, H₁.sign x * H₃.sign x ∂μ = 0)
    (bν₁ : ∫ y, H₁.sign y ∂ν = 0) (bν₃ : ∫ y, H₃.sign y ∂ν = 0)
    (bν₁₂ : ∫ y, H₁.sign y * H₂.sign y ∂ν = 0) :
    (∫ x, K.sign x ∂μ) * (∫ y, K.sign y ∂ν)
        - ((∫ x, K.sign x * H₁.sign x ∂μ) * (∫ y, K.sign y * H₁.sign y ∂ν)
          + (∫ x, K.sign x * H₂.sign x ∂μ) * (∫ y, K.sign y * H₂.sign y ∂ν)
          + (∫ x, K.sign x * H₃.sign x ∂μ) * (∫ y, K.sign y * H₃.sign y ∂ν)) ≤ 1 ∧
    (μ.prod ν).real (Sep K) ≤
      (μ.prod ν).real (Sep K ∩ Sep H₁) + (μ.prod ν).real (Sep K ∩ Sep H₂)
        + (μ.prod ν).real (Sep K ∩ Sep H₃) := by
  let H₂' : Hyp 2 := if 0 ≤ ∫ x, K.sign x * H₂.sign x ∂μ then H₂ else AuxEq8.negHyp H₂
  let H₃' : Hyp 2 := if 0 ≤ ∫ x, K.sign x * H₃.sign x ∂μ then H₃ else AuxEq8.negHyp H₃
  have hH₂'_set : H₂'.set = H₂.set := by dsimp [H₂']; split_ifs <;> simp [AuxEq8.negHyp_set]
  have hH₃'_set : H₃'.set = H₃.set := by dsimp [H₃']; split_ifs <;> simp [AuxEq8.negHyp_set]
  have bμ₂' : ∫ x, H₂'.sign x ∂μ = 0 := by
    dsimp [H₂']
    split_ifs
    · exact bμ₂
    · simp [AuxEq8.negHyp_sign, integral_neg, bμ₂]
  have bν₁₂' : ∫ y, H₁.sign y * H₂'.sign y ∂ν = 0 := by
    dsimp [H₂']
    split_ifs
    · exact bν₁₂
    · have : (fun y => H₁.sign y * (AuxEq8.negHyp H₂).sign y) =
          fun y => -(H₁.sign y * H₂.sign y) := by
        ext y; simp [AuxEq8.negHyp_sign]
      rw [this, integral_neg, bν₁₂, neg_zero]
  have bν₃' : ∫ y, H₃'.sign y ∂ν = 0 := by
    dsimp [H₃']
    split_ifs
    · exact bν₃
    · simp [AuxEq8.negHyp_sign, integral_neg, bν₃]
  have bμ₁₃' : ∫ x, H₁.sign x * H₃'.sign x ∂μ = 0 := by
    dsimp [H₃']
    split_ifs
    · exact bμ₁₃
    · have : (fun x => H₁.sign x * (AuxEq8.negHyp H₃).sign x) =
          fun x => -(H₁.sign x * H₃.sign x) := by
        ext x; simp [AuxEq8.negHyp_sign]
      rw [this, integral_neg, bμ₁₃, neg_zero]
  have hp₂' : 0 ≤ ∫ x, K.sign x * H₂'.sign x ∂μ := by
    dsimp [H₂']
    split_ifs with h
    · exact h
    · have : (fun x => K.sign x * (AuxEq8.negHyp H₂).sign x) =
          fun x => -(K.sign x * H₂.sign x) := by ext x; simp [AuxEq8.negHyp_sign]
      rw [this, integral_neg]; linarith
  have hp₃' : 0 ≤ ∫ x, K.sign x * H₃'.sign x ∂μ := by
    dsimp [H₃']
    split_ifs with h
    · exact h
    · have : (fun x => K.sign x * (AuxEq8.negHyp H₃).sign x) =
          fun x => -(K.sign x * H₃.sign x) := by ext x; simp [AuxEq8.negHyp_sign]
      rw [this, integral_neg]; linarith
  have hprod2 : (∫ x, K.sign x * H₂'.sign x ∂μ) * (∫ y, K.sign y * H₂'.sign y ∂ν) =
      (∫ x, K.sign x * H₂.sign x ∂μ) * (∫ y, K.sign y * H₂.sign y ∂ν) := by
    dsimp [H₂']
    split_ifs
    · rfl
    · have h1 : (fun x => K.sign x * (AuxEq8.negHyp H₂).sign x) =
          fun x => -(K.sign x * H₂.sign x) := by ext x; simp [AuxEq8.negHyp_sign]
      rw [h1, integral_neg, integral_neg, neg_mul_neg]
  have hprod3 : (∫ x, K.sign x * H₃'.sign x ∂μ) * (∫ y, K.sign y * H₃'.sign y ∂ν) =
      (∫ x, K.sign x * H₃.sign x ∂μ) * (∫ y, K.sign y * H₃.sign y ∂ν) := by
    dsimp [H₃']
    split_ifs
    · rfl
    · have h1 : (fun x => K.sign x * (AuxEq8.negHyp H₃).sign x) =
          fun x => -(K.sign x * H₃.sign x) := by ext x; simp [AuxEq8.negHyp_sign]
      rw [h1, integral_neg, integral_neg, neg_mul_neg]
  have hphi : (∫ x, K.sign x ∂μ) * (∫ y, K.sign y ∂ν)
        - ((∫ x, K.sign x * H₁.sign x ∂μ) * (∫ y, K.sign y * H₁.sign y ∂ν)
          + (∫ x, K.sign x * H₂.sign x ∂μ) * (∫ y, K.sign y * H₂.sign y ∂ν)
          + (∫ x, K.sign x * H₃.sign x ∂μ) * (∫ y, K.sign y * H₃.sign y ∂ν)) ≤ 1 := by
    have h' := AuxEq8.phi_le_one_oriented μ ν H₁ H₂' H₃' K
      hμ₁ (hH₂'_set.symm ▸ hμ₂) (hH₃'_set.symm ▸ hμ₃) hμK
      hν₁ (hH₂'_set.symm ▸ hν₂) (hH₃'_set.symm ▸ hν₃) hνK
      bμ₁ bμ₂' bμ₁₃' bν₁ bν₃' bν₁₂' hp₂' hp₃'
    rwa [hprod2, hprod3] at h'
  refine ⟨hphi, ?_⟩
  have hD := SepMeasures.lemma_2_4 2 (by norm_num) μ ν K hμK hνK
  have hI1 := SepMeasures.lemma_2_5 2 (by norm_num) μ ν K H₁
    (measure_union_null hμK hμ₁) (measure_union_null hνK hν₁)
  have hI2 := SepMeasures.lemma_2_5 2 (by norm_num) μ ν K H₂
    (measure_union_null hμK hμ₂) (measure_union_null hνK hν₂)
  have hI3 := SepMeasures.lemma_2_5 2 (by norm_num) μ ν K H₃
    (measure_union_null hμK hμ₃) (measure_union_null hνK hν₃)
  rw [hD, hI1, hI2, hI3, bμ₁, bμ₂, bν₃]
  linarith
