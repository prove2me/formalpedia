-- Prove2me | solution 1 for UnderstandingML.ridge_regression_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:11:53.450109+00:00
-- url     : https://prove2.me/submissions/1e1a4498-e1cd-4c0d-a8ea-947038326965

import Theorems.Thm_UnderstandingML_convex_smooth_bounded_learnable
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

namespace UMLRidge

variable {d : ℕ}

/-- Projection of an example onto the support `‖x‖ ≤ 1`, `|y| ≤ 1`. -/
noncomputable def clip (z : Vec d × ℝ) : Vec d × ℝ :=
  ((max 1 ‖z.1‖)⁻¹ • z.1, max (-1) (min 1 z.2))

lemma continuous_clip : Continuous (clip (d := d)) := by
  have h1 : Continuous fun z : Vec d × ℝ ↦ max (1 : ℝ) ‖z.1‖ :=
    Continuous.max continuous_const (Continuous.norm continuous_fst)
  have h2 : Continuous fun z : Vec d × ℝ ↦ (max (1 : ℝ) ‖z.1‖)⁻¹ :=
    Continuous.inv₀ h1 fun z ↦ (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  have h3 : Continuous fun z : Vec d × ℝ ↦ (max (1 : ℝ) ‖z.1‖)⁻¹ • z.1 :=
    Continuous.smul h2 continuous_fst
  have h4 : Continuous fun z : Vec d × ℝ ↦ max (-1 : ℝ) (min 1 z.2) :=
    Continuous.max continuous_const (Continuous.min continuous_const continuous_snd)
  exact Continuous.prodMk h3 h4

lemma norm_clip_fst_le (z : Vec d × ℝ) : ‖(clip z).1‖ ≤ 1 := by
  unfold clip
  have h1 : (0 : ℝ) < max 1 ‖z.1‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h1.le), inv_mul_le_iff₀ h1, mul_one]
  exact le_max_right _ _

lemma abs_clip_snd_le (z : Vec d × ℝ) : |(clip z).2| ≤ 1 := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma clip_eq_self {z : Vec d × ℝ} (h : ‖z.1‖ ≤ 1 ∧ |z.2| ≤ 1) : clip z = z := by
  obtain ⟨h1, h2⟩ := h
  rw [abs_le] at h2
  unfold clip
  ext1
  · simp [max_eq_left h1]
  · simp [min_eq_right h2.2, max_eq_right h2.1]

/-- The ridge loss evaluated at the projected example. -/
noncomputable def clipLoss (w : Vec d) (z : Vec d × ℝ) : ℝ := ridgeLoss w (clip z)

lemma continuous_ridge : Continuous fun p : Vec d × (Vec d × ℝ) ↦ ridgeLoss p.1 p.2 := by
  unfold ridgeLoss
  exact continuous_const.mul
    (((continuous_fst.inner (continuous_fst.comp continuous_snd)).sub
      (continuous_snd.comp continuous_snd)).pow 2)

lemma measurable_clipLoss : Measurable (Function.uncurry (clipLoss (d := d))) := by
  have : Function.uncurry (clipLoss (d := d)) =
      (fun p : Vec d × (Vec d × ℝ) ↦ ridgeLoss p.1 p.2) ∘
        (fun p : Vec d × (Vec d × ℝ) ↦ (p.1, clip p.2)) := rfl
  rw [this]
  exact (continuous_ridge.comp (continuous_fst.prodMk (continuous_clip.comp continuous_snd))).measurable

/-- Gradient of `w ↦ ½(⟨w, x⟩ − y)²`. -/
lemma hasGradientAt_ridge (x : Vec d) (y : ℝ) (w : Vec d) :
    HasGradientAt (fun w : Vec d ↦ (1 / 2 : ℝ) * (⟪w, x⟫_ℝ - y) ^ 2) ((⟪w, x⟫_ℝ - y) • x) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlin : HasFDerivAt (fun w : Vec d ↦ ⟪x, w⟫_ℝ) (innerSL ℝ x) w :=
    ContinuousLinearMap.hasFDerivAt (innerSL ℝ x)
  have hsq : HasDerivAt (fun s : ℝ ↦ (1 / 2 : ℝ) * ((s - y) * (s - y))) (⟪x, w⟫_ℝ - y)
      ⟪x, w⟫_ℝ := by
    have h0 : HasDerivAt (fun s : ℝ ↦ s - y) 1 ⟪x, w⟫_ℝ :=
      (hasDerivAt_id _).sub_const y
    have h := HasDerivAt.const_mul (1 / 2 : ℝ) (HasDerivAt.mul h0 h0)
    exact h.congr_deriv (by ring)
  have hcomp := HasDerivAt.comp_hasFDerivAt w hsq hlin
  have hfun : (fun w : Vec d ↦ (1 / 2 : ℝ) * (⟪w, x⟫_ℝ - y) ^ 2) =
      (fun s : ℝ ↦ (1 / 2 : ℝ) * ((s - y) * (s - y))) ∘ (fun w : Vec d ↦ ⟪x, w⟫_ℝ) := by
    funext v; simp [real_inner_comm, sq]
  rw [hfun]
  refine hcomp.congr_fderiv ?_
  ext v
  rw [InnerProductSpace.toDual_apply_apply]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_smul_left, real_inner_comm x w]

lemma gradient_ridge (x : Vec d) (y : ℝ) (w : Vec d) :
    gradient (fun w : Vec d ↦ (1 / 2 : ℝ) * (⟪w, x⟫_ℝ - y) ^ 2) w = (⟪w, x⟫_ℝ - y) • x :=
  (hasGradientAt_ridge x y w).gradient

/-- The projected ridge problem is convex-smooth-bounded with `β = 1` on the ball of radius `B`. -/
lemma convexSmoothBounded_clipLoss (B : ℝ) :
    ConvexSmoothBounded (Metric.closedBall (0 : Vec d) B) clipLoss 1 B := by
  refine ⟨convex_closedBall _ _, fun w hw ↦ by simpa using hw, fun z ↦ ?_, fun w z ↦ ?_,
    fun z ↦ ⟨?_, fun v w ↦ ?_⟩⟩
  · -- convexity
    refine ⟨convex_univ, fun w₁ _ w₂ _ a b ha hb hab ↦ ?_⟩
    simp only [clipLoss, ridgeLoss, smul_eq_mul]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    set s₁ := ⟪w₁, (clip z).1⟫_ℝ
    set s₂ := ⟪w₂, (clip z).1⟫_ℝ
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, sq_nonneg (s₁ - s₂)]
  · -- nonnegativity
    simp only [clipLoss, ridgeLoss]; positivity
  · -- differentiability
    exact fun w ↦ (hasGradientAt_ridge (clip z).1 (clip z).2 w).differentiableAt
  · -- the gradient is `1`-Lipschitz
    show ‖gradient (fun w : Vec d ↦ (1 / 2 : ℝ) * (⟪w, (clip z).1⟫_ℝ - (clip z).2) ^ 2) v -
        gradient (fun w : Vec d ↦ (1 / 2 : ℝ) * (⟪w, (clip z).1⟫_ℝ - (clip z).2) ^ 2) w‖ ≤
        1 * ‖v - w‖
    rw [gradient_ridge, gradient_ridge, ← sub_smul, norm_smul, Real.norm_eq_abs]
    have hx := norm_clip_fst_le z
    have e : ⟪v, (clip z).1⟫_ℝ - (clip z).2 - (⟪w, (clip z).1⟫_ℝ - (clip z).2) =
        ⟪v - w, (clip z).1⟫_ℝ := by rw [inner_sub_left]; ring
    rw [e]
    have h1 : |⟪v - w, (clip z).1⟫_ℝ| ≤ ‖v - w‖ * ‖(clip z).1‖ := abs_real_inner_le_norm _ _
    calc |⟪v - w, (clip z).1⟫_ℝ| * ‖(clip z).1‖ ≤ ‖v - w‖ * ‖(clip z).1‖ * ‖(clip z).1‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ ‖v - w‖ * 1 * 1 := by gcongr
      _ = 1 * ‖v - w‖ := by ring

lemma clipLoss_zero_le (z : Vec d × ℝ) : clipLoss 0 z ≤ 1 := by
  simp only [clipLoss, ridgeLoss, inner_zero_left, zero_sub, even_two, Even.neg_pow]
  have h := abs_clip_snd_le z
  have : (clip z).2 ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (clip z).2]
  linarith

end UMLRidge

open UMLRidge in
theorem solution {d : ℕ} (D : Measure (Vec d × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ‖z.1‖ ≤ 1 ∧ |z.2| ≤ 1) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (m : ℕ) (hm : 150 * B ^ 2 / ε ^ 2 ≤ m) (A : Learner (Vec d × ℝ) (Vec d))
    (hA : IsRLMLearner ridgeLoss (ε / (3 * B ^ 2)) A) (hAmeas : ∀ m, Measurable (A m)) :
    ∀ w : Vec d, ‖w‖ ≤ B →
      ∫ S, risk ridgeLoss D (A m S) ∂(iidLaw D m) ≤ risk ridgeLoss D w + ε := by
  intro w hw
  -- the learner run on projected samples
  set A' : Learner (Vec d × ℝ) (Vec d) := fun k S ↦ A k (clip ∘ S) with hA'_def
  have hA' : IsRLMLearner clipLoss (ε / (3 * B ^ 2)) A' := fun k S w' ↦ hA k (clip ∘ S) w'
  have hA'meas : ∀ k, Measurable (A' k) := fun k ↦
    (hAmeas k).comp (measurable_pi_lambda _ fun i ↦
      continuous_clip.measurable.comp (measurable_pi_apply i))
  have h := convex_smooth_bounded_learnable (Metric.closedBall (0 : Vec d) B) clipLoss one_pos
    hB (convexSmoothBounded_clipLoss B) clipLoss_zero_le hε0 hε1 m (by rwa [mul_one])
    A' hA' measurable_clipLoss hA'meas D w (by simpa using hw)
  -- `clipLoss` and `ridgeLoss` have the same risk under `D`
  have hrisk : ∀ v : Vec d, risk clipLoss D v = risk ridgeLoss D v := by
    intro v
    unfold risk clipLoss
    refine integral_congr_ae ?_
    filter_upwards [hD] with z hz
    rw [clip_eq_self hz]
  -- `D^m`-almost every sample is unchanged by projection
  have hS : ∀ᵐ S ∂(iidLaw D m), clip ∘ S = S := by
    have : ∀ i : Fin m, ∀ᵐ S ∂(iidLaw D m), clip (S i) = S i := by
      intro i
      have hqmp := (measurePreserving_eval (μ := fun _ : Fin m ↦ D) i).quasiMeasurePreserving
      have := hqmp.ae (hD.mono fun z hz ↦ clip_eq_self hz)
      simpa [iidLaw] using this
    filter_upwards [ae_all_iff.2 this] with S hS
    funext i; exact hS i
  have hint : ∫ S, risk clipLoss D (A' m S) ∂(iidLaw D m) =
      ∫ S, risk ridgeLoss D (A m S) ∂(iidLaw D m) := by
    refine integral_congr_ae ?_
    filter_upwards [hS] with S hS
    simp only [hA'_def, hS, hrisk]
  rw [← hint, ← hrisk w]
  exact h
