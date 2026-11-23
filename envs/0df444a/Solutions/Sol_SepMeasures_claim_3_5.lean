-- Prove2me | solution 1 for SepMeasures.claim_3_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:24:32.958281+00:00
-- url     : https://prove2.me/submissions/a0367aed-742d-4158-86a5-b9db6b1debc3

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory SepMeasures

namespace Aux35

lemma measurableSet_hyp_pos {d : ℕ} (K : Hyp d) : MeasurableSet K.pos :=
  isOpen_lt continuous_const (continuous_const.inner continuous_id) |>.measurableSet

lemma measurableSet_hyp_neg {d : ℕ} (K : Hyp d) : MeasurableSet K.neg :=
  isOpen_lt (continuous_const.inner continuous_id) continuous_const |>.measurableSet

lemma measurable_sign {d : ℕ} (K : Hyp d) : Measurable K.sign := by
  unfold Hyp.sign
  exact Measurable.ite (measurableSet_hyp_pos K) measurable_const
    (Measurable.ite (measurableSet_hyp_neg K) measurable_const measurable_const)

lemma integrable_sign {d : ℕ} (μ : Measure (E d)) [IsFiniteMeasure μ] (K : Hyp d) :
    Integrable K.sign μ := by
  refine Integrable.of_bound (measurable_sign K).aestronglyMeasurable 1 (ae_of_all μ fun x => ?_)
  unfold Hyp.sign
  split_ifs <;> norm_num

lemma integrable_sign_mul {d : ℕ} (μ : Measure (E d)) [IsFiniteMeasure μ] (K K' : Hyp d) :
    Integrable (fun x => K.sign x * K'.sign x) μ := by
  refine Integrable.of_bound
    ((measurable_sign K).mul (measurable_sign K')).aestronglyMeasurable 1 (ae_of_all μ fun x => ?_)
  have h1 : |K.sign x| ≤ 1 := by unfold Hyp.sign; split_ifs <;> norm_num
  have h2 : |K'.sign x| ≤ 1 := by unfold Hyp.sign; split_ifs <;> norm_num
  simpa [abs_mul] using mul_le_one₀ h1 (abs_nonneg _) h2

lemma sign_mem_pair {d : ℕ} (K : Hyp d) {x : E d} (hx : x ∉ K.set) :
    K.sign x = -1 ∨ K.sign x = 1 := by
  have hne : inner ℝ K.u x ≠ K.c := hx
  unfold Hyp.sign
  rcases lt_or_gt_of_ne hne with hl | hg
  · left; simp [hl, not_lt.mpr hl.le]
  · right; simp [hg]

lemma pointwise_bound {a b c s₁ m₁ m₂ k : ℝ}
    (ha : a = -1 ∨ a = 1) (hb : b = -1 ∨ b = 1) (hc : c = -1 ∨ c = 1)
    (hs₁ : s₁ = -1 ∨ s₁ = 1) (hm₁ : m₁ = -1 ∨ m₁ = 1)
    (hm₂ : m₂ = -1 ∨ m₂ = 1) (hk : k = -1 ∨ k = 1)
    (hnot : ¬ (s₁ = a ∧ m₁ = b ∧ m₂ = b ∧ k = c * b)) :
    c * (k * m₁) + c * (k * m₂) + b * m₁ + a * b * (s₁ * m₂) ≤ 1 - a * s₁ := by
  revert hnot
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hs₁ with rfl | rfl <;> rcases hm₁ with rfl | rfl <;>
    rcases hm₂ with rfl | rfl <;> rcases hk with rfl | rfl <;>
    norm_num

lemma half_pos {d : ℕ} (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    (H₁ M₁ M₂ K : Hyp d)
    (hρ₁ : ρ H₁.set = 0) (hρM₁ : ρ M₁.set = 0) (hρM₂ : ρ M₂.set = 0) (hρK : ρ K.set = 0)
    (b₁ : ∫ x, H₁.sign x ∂ρ = 0) (bM₁ : ∫ x, M₁.sign x ∂ρ = 0)
    (b₁M₂ : ∫ x, H₁.sign x * M₂.sign x ∂ρ = 0)
    {a b c : ℝ} (ha : a = -1 ∨ a = 1) (hb : b = -1 ∨ b = 1) (hc : c = -1 ∨ c = 1)
    (hgt : 1 < c * (∫ x, K.sign x * M₁.sign x ∂ρ) + c * (∫ x, K.sign x * M₂.sign x ∂ρ)) :
    0 < ρ {x | H₁.sign x = a ∧ M₁.sign x = b ∧ M₂.sign x = b ∧ K.sign x = c * b} := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hae : ∀ᵐ x ∂ρ,
      c * (K.sign x * M₁.sign x) + c * (K.sign x * M₂.sign x) + b * M₁.sign x +
        a * b * (H₁.sign x * M₂.sign x) ≤ 1 - a * H₁.sign x := by
    have h1 : ∀ᵐ x ∂ρ, x ∉ H₁.set := by rw [ae_iff]; simpa using hρ₁
    have h2 : ∀ᵐ x ∂ρ, x ∉ M₁.set := by rw [ae_iff]; simpa using hρM₁
    have h3 : ∀ᵐ x ∂ρ, x ∉ M₂.set := by rw [ae_iff]; simpa using hρM₂
    have h4 : ∀ᵐ x ∂ρ, x ∉ K.set := by rw [ae_iff]; simpa using hρK
    have h5 : ∀ᵐ x ∂ρ, ¬ (H₁.sign x = a ∧ M₁.sign x = b ∧ M₂.sign x = b ∧ K.sign x = c * b) := by
      rw [ae_iff]; simpa using hzero
    filter_upwards [h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5
    exact pointwise_bound ha hb hc
      (sign_mem_pair H₁ hx1) (sign_mem_pair M₁ hx2) (sign_mem_pair M₂ hx3) (sign_mem_pair K hx4) hx5
  have iKM₁ : Integrable (fun x => c * (K.sign x * M₁.sign x)) ρ :=
    (integrable_sign_mul ρ K M₁).const_mul c
  have iKM₂ : Integrable (fun x => c * (K.sign x * M₂.sign x)) ρ :=
    (integrable_sign_mul ρ K M₂).const_mul c
  have iM₁ : Integrable (fun x => b * M₁.sign x) ρ :=
    (integrable_sign ρ M₁).const_mul b
  have i₁M₂ : Integrable (fun x => a * b * (H₁.sign x * M₂.sign x)) ρ :=
    (integrable_sign_mul ρ H₁ M₂).const_mul (a * b)
  have i12 : Integrable (fun x => c * (K.sign x * M₁.sign x) + c * (K.sign x * M₂.sign x)) ρ :=
    iKM₁.add iKM₂
  have i123 : Integrable (fun x =>
      c * (K.sign x * M₁.sign x) + c * (K.sign x * M₂.sign x) + b * M₁.sign x) ρ :=
    i12.add iM₁
  have iLHS : Integrable (fun x =>
      c * (K.sign x * M₁.sign x) + c * (K.sign x * M₂.sign x) + b * M₁.sign x +
        a * b * (H₁.sign x * M₂.sign x)) ρ :=
    i123.add i₁M₂
  have iRHS : Integrable (fun x => 1 - a * H₁.sign x) ρ :=
    (integrable_const (1 : ℝ)).sub ((integrable_sign ρ H₁).const_mul a)
  have hint_le : ∫ x, (c * (K.sign x * M₁.sign x) + c * (K.sign x * M₂.sign x) + b * M₁.sign x +
      a * b * (H₁.sign x * M₂.sign x)) ∂ρ ≤ ∫ x, (1 - a * H₁.sign x) ∂ρ :=
    integral_mono_ae iLHS iRHS hae
  rw [integral_add i123 i₁M₂, integral_add i12 iM₁, integral_add iKM₁ iKM₂,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub (integrable_const 1) ((integrable_sign ρ H₁).const_mul a),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    b₁, bM₁, b₁M₂] at hint_le
  linarith

end Aux35

theorem solution (d : ℕ) (hd : 1 ≤ d) (μ ν : Measure (E d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H₁ H₂ H₃ K : Hyp d)
    (hμ₁ : μ H₁.set = 0) (hμ₂ : μ H₂.set = 0) (hμ₃ : μ H₃.set = 0) (hμK : μ K.set = 0)
    (hν₁ : ν H₁.set = 0) (hν₂ : ν H₂.set = 0) (hν₃ : ν H₃.set = 0) (hνK : ν K.set = 0)
    (bμ₁ : ∫ x, H₁.sign x ∂μ = 0) (bμ₂ : ∫ x, H₂.sign x ∂μ = 0)
    (bμ₁₃ : ∫ x, H₁.sign x * H₃.sign x ∂μ = 0)
    (bν₁ : ∫ y, H₁.sign y ∂ν = 0) (bν₃ : ∫ y, H₃.sign y ∂ν = 0)
    (bν₁₂ : ∫ y, H₁.sign y * H₂.sign y ∂ν = 0)
    (hp : 1 < (∫ x, K.sign x * H₂.sign x ∂μ) + ∫ x, K.sign x * H₃.sign x ∂μ)
    (hq : 1 < -(∫ y, K.sign y * H₂.sign y ∂ν) - ∫ y, K.sign y * H₃.sign y ∂ν) :
    ∀ a ∈ ({-1, 1} : Set ℝ), ∀ b ∈ ({-1, 1} : Set ℝ),
      0 < μ {x | H₁.sign x = a ∧ H₂.sign x = b ∧ K.sign x = b} ∧
      0 < ν {y | H₁.sign y = a ∧ H₂.sign y = b ∧ K.sign y = -b} := by
  have _ := hd
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  constructor
  · have hpos := Aux35.half_pos μ H₁ H₂ H₃ K hμ₁ hμ₂ hμ₃ hμK bμ₁ bμ₂ bμ₁₃ ha hb (Or.inr rfl)
      (by linarith)
    exact hpos.trans_le (measure_mono fun x hx => ⟨hx.1, hx.2.1, by simpa using hx.2.2.2⟩)
  · have hpos := Aux35.half_pos ν H₁ H₃ H₂ K hν₁ hν₃ hν₂ hνK bν₁ bν₃ bν₁₂ ha hb (Or.inl rfl)
      (by linarith)
    exact hpos.trans_le (measure_mono fun y hy => ⟨hy.1, hy.2.2.1, by simpa using hy.2.2.2⟩)
