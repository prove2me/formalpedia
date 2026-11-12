-- Prove2me | solution 1 for SpectralSharpness.NormalWindow.lemma_9_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:31:29.231227+00:00
-- url     : https://prove2.me/submissions/9c078eb8-801a-4cf2-8bb6-23d9a1ecbdf3

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_BandLimited
import Definitions.Def_SpectralSharpness_NormalWindow_ExponentialType
import Theorems.Thm_SpectralSharpness_NormalWindow_bernstein_exponential_type

section
set_option autoImplicit false

namespace SpectralSharpness.Dev.LineExt
open SpectralSharpness.NormalWindow

lemma differentiable_of_spectrum {n : ℕ} (S : Set (Fin n → ℤ)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : HasSpectrumIn S f) : Differentiable ℝ f := by
  obtain ⟨F, c, -, hF⟩ := hf
  have h1 : Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ k ∈ F, c k * Complex.exp (Complex.I * (freqDot k x : ℂ))) := by
    unfold freqDot
    fun_prop
  have h2 : f = fun x => (∑ k ∈ F, c k * Complex.exp (Complex.I * (freqDot k x : ℂ))).re := by
    funext x
    rw [← hF x]; simp
  rw [h2]
  exact Complex.reCLM.differentiable.comp h1

/-- the entire extension along a line. -/
noncomputable def lineExt {n : ℕ} (F : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x0 v : EuclideanSpace ℝ (Fin n)) (w : ℂ) : ℂ :=
  ∑ k ∈ F, c k * Complex.exp (Complex.I * ((freqDot k x0 : ℂ) + w * (freqDot k v : ℂ)))

lemma lineExt_diff {n : ℕ} (F : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x0 v : EuclideanSpace ℝ (Fin n)) : Differentiable ℂ (lineExt F c x0 v) := by
  unfold lineExt
  fun_prop

lemma freqDot_add_smul {n : ℕ} (k : Fin n → ℤ) (x0 v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    freqDot k (x0 + t • v) = freqDot k x0 + t * freqDot k v := by
  unfold freqDot
  simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma lineExt_real {n : ℕ} (F : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x0 v : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ∀ x, (f x : ℂ) = ∑ k ∈ F, c k * Complex.exp (Complex.I * (freqDot k x : ℂ)))
    (t : ℝ) : lineExt F c x0 v (t : ℂ) = ((f (x0 + t • v) : ℝ) : ℂ) := by
  rw [hF, lineExt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [freqDot_add_smul]; push_cast; rfl

lemma lineExt_bound {n : ℕ} (F : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x0 v : EuclideanSpace ℝ (Fin n)) (τ : ℝ) (hτ : ∀ k ∈ F, |freqDot k v| ≤ τ)
    (w : ℂ) : ‖lineExt F c x0 v w‖ ≤ (∑ k ∈ F, ‖c k‖) * Real.exp (τ * ‖w‖) := by
  unfold lineExt
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have : (Complex.I * ((freqDot k x0 : ℂ) + w * (freqDot k v : ℂ))).re = -(w.im * freqDot k v) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have h1 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  calc -(w.im * freqDot k v) ≤ |w.im * freqDot k v| := neg_le_abs _
    _ = |w.im| * |freqDot k v| := abs_mul _ _
    _ ≤ ‖w‖ * τ := mul_le_mul h1 (hτ k hk) (abs_nonneg _) (norm_nonneg _)
    _ = τ * ‖w‖ := mul_comm _ _

lemma isEntireType_lineExt {n : ℕ} (F : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x0 v : EuclideanSpace ℝ (Fin n)) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : ∀ k ∈ F, |freqDot k v| ≤ τ) :
    IsEntireOfExponentialTypeLE τ (lineExt F c x0 v) := by
  refine ⟨lineExt_diff F c x0 v, fun ε hε => ⟨∑ k ∈ F, ‖c k‖, fun z => ?_⟩⟩
  refine (lineExt_bound F c x0 v τ hτ z).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  nlinarith [norm_nonneg z]

/-- the directional derivative equals the derivative of the extension at `0`. -/
lemma fderiv_eq_deriv_lineExt {n : ℕ} (F : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x0 v : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ∀ x, (f x : ℂ) = ∑ k ∈ F, c k * Complex.exp (Complex.I * (freqDot k x : ℂ)))
    (hd : Differentiable ℝ f) (x : ℝ) :
    ((fderiv ℝ f (x0 + x • v) v : ℝ) : ℂ) = deriv (lineExt F c x0 v) (x : ℂ) := by
  have h1 : HasDerivAt (fun t : ℝ => f (x0 + t • v)) (fderiv ℝ f (x0 + x • v) v) x := by
    have h := (hd (x0 + x • v)).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => x0 + t • v) v x := by
      simpa using ((hasDerivAt_id x).smul_const v).const_add x0
    exact h.comp_hasDerivAt x h2
  have h3 := h1.ofReal_comp
  have h4 : HasDerivAt (fun t : ℝ => lineExt F c x0 v (t : ℂ)) (deriv (lineExt F c x0 v) (x : ℂ)) x :=
    ((lineExt_diff F c x0 v) (x : ℂ)).hasDerivAt.comp_ofReal
  have h5 : (fun t : ℝ => lineExt F c x0 v (t : ℂ)) = fun t : ℝ => ((f (x0 + t • v) : ℝ) : ℂ) := by
    funext t; exact lineExt_real F c x0 v f hF t
  rw [h5] at h4
  exact h3.unique h4

end SpectralSharpness.Dev.LineExt
end

section
set_option autoImplicit false

namespace SpectralSharpness.Dev.L91
open SpectralSharpness.NormalWindow SpectralSharpness.Dev.LineExt

lemma norm_sq_eq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    ∑ i, (v i) ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [hv] at h
  simpa using h.symm

lemma freqDot_le_ball {n : ℕ} (d : ℝ) (k : Fin n → ℤ) (hk : Real.sqrt (∑ i, ((k i : ℝ)) ^ 2) ≤ d)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) : |freqDot k v| ≤ d := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (k i : ℝ)) (fun i => v i)
  rw [norm_sq_eq v hv, mul_one] at h1
  have : |freqDot k v| ≤ Real.sqrt (∑ i, ((k i : ℝ)) ^ 2) := by
    apply Real.abs_le_sqrt
    simpa [freqDot] using h1
  exact this.trans hk

lemma freqDot_le_cube {n : ℕ} (d : ℝ) (k : Fin n → ℤ) (hk : ∀ i, |(k i : ℝ)| ≤ d)
    (v : EuclideanSpace ℝ (Fin n)) : |freqDot k v| ≤ d * ∑ i, |v i| := by
  unfold freqDot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hk i) (abs_nonneg _)

lemma deriv_bound {n : ℕ} (S : Set (Fin n → ℤ)) (v : EuclideanSpace ℝ (Fin n)) (τ A : ℝ)
    (hτ0 : 0 ≤ τ) (hS : ∀ k ∈ S, |freqDot k v| ≤ τ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : HasSpectrumIn S f) (hA : ∀ x, |f x| ≤ A) (x₀ : EuclideanSpace ℝ (Fin n)) :
    |fderiv ℝ f x₀ v| ≤ τ * A := by
  have hd := differentiable_of_spectrum S f hf
  obtain ⟨F, c, hFS, hF⟩ := hf
  have hE := isEntireType_lineExt F c x₀ v τ hτ0 (fun k hk => hS k (hFS hk))
  have hB := bernstein_exponential_type τ A hτ0 (lineExt F c x₀ v) hE (fun x => by
    rw [lineExt_real F c x₀ v f hF x]
    simpa using hA _) 0
  have := fderiv_eq_deriv_lineExt F c x₀ v f hF hd 0
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at this hB
  rw [← this] at hB
  simpa using hB

lemma gradient_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (h : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → |fderiv ℝ f x₀ v| ≤ B) :
    ‖gradient f x₀‖ ≤ B := by
  by_cases h0 : gradient f x₀ = 0
  · rw [h0]; simpa using hB0
  · set g := gradient f x₀ with hg
    have hn : 0 < ‖g‖ := norm_pos_iff.mpr h0
    have key : fderiv ℝ f x₀ g = ‖g‖ ^ 2 := by
      have : inner ℝ g g = fderiv ℝ f x₀ g :=
        InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := g) (y := fderiv ℝ f x₀)
      rw [real_inner_self_eq_norm_sq] at this
      exact this.symm
    have hv : ‖(‖g‖⁻¹) • g‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have := h _ hv
    rw [map_smul, key, smul_eq_mul] at this
    have e : ‖g‖⁻¹ * ‖g‖ ^ 2 = ‖g‖ := by field_simp
    rw [e, abs_of_pos hn] at this
    exact this

end SpectralSharpness.Dev.L91

namespace SpectralSharpness.NormalWindow
open SpectralSharpness.Dev.L91 in
theorem chk_lemma_9_1 {n : ℕ} (d A : ℝ) (hd : 0 ≤ d) :
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBandLimitedBall d f → (∀ x, |f x| ≤ A) →
      (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ x₀, |fderiv ℝ f x₀ v| ≤ d * A) ∧
      (∀ x₀, ‖gradient f x₀‖ ≤ d * A)) ∧
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBandLimitedCube d f → (∀ x, |f x| ≤ A) →
      ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ x₀,
        |fderiv ℝ f x₀ v| ≤ d * (∑ i, |v i|) * A ∧
        d * (∑ i, |v i|) * A ≤ Real.sqrt n * d * A) := by
  have hA0 : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, (∀ x, |f x| ≤ A) → 0 ≤ A :=
    fun f hA => (abs_nonneg _).trans (hA 0)
  refine ⟨fun f hf hA => ?_, fun f hf hA v hv x₀ => ?_⟩
  · have hb : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ x₀, |fderiv ℝ f x₀ v| ≤ d * A := by
      intro v hv x₀
      refine deriv_bound (euclidBall n d) v d A hd (fun k hk => freqDot_le_ball d k hk v hv) f hf hA x₀
    exact ⟨hb, fun x₀ => gradient_bound f _ (mul_nonneg hd (hA0 f hA)) x₀ (fun v hv => hb v hv x₀)⟩
  · have hAn := hA0 f hA
    have hsum : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨deriv_bound (supCube n d) v (d * ∑ i, |v i|) A (mul_nonneg hd hsum)
      (fun k hk => freqDot_le_cube d k hk v) f hf hA x₀ |>.trans_eq (by ring), ?_⟩
    have h1 : ∑ i, |v i| ≤ Real.sqrt n := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) (fun i => |v i|)
      simp only [one_pow, one_mul, sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at this
      rw [norm_sq_eq v hv] at this
      exact Real.le_sqrt_of_sq_le (by simpa using this)
    have : d * (∑ i, |v i|) * A ≤ d * Real.sqrt n * A := by
      apply mul_le_mul_of_nonneg_right _ hAn
      exact mul_le_mul_of_nonneg_left h1 hd
    calc _ ≤ _ := this
      _ = _ := by ring

end SpectralSharpness.NormalWindow
end

theorem solution : type_of% @SpectralSharpness.NormalWindow.chk_lemma_9_1 := @SpectralSharpness.NormalWindow.chk_lemma_9_1
