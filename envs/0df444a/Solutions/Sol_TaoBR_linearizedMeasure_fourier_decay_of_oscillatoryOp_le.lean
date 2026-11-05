-- Prove2me | solution 1 for TaoBR.linearizedMeasure_fourier_decay_of_oscillatoryOp_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T13:39:51.603967+00:00
-- url     : https://prove2.me/submissions/2f0a6ae9-1918-4fb0-9860-482062ae1958

import Mathlib
import Definitions.Def_TaoBR

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
/-!
# Blueprint: power Fourier decay of the linearized measures (Tao 1999, Theorem 4.9 gap)

Route (see p2m-standalone/tao-br-readings/proofs/decay/PLAN.md):
* `knapp`: the operator bound `hS`, tested on an anisotropic Knapp function, forces the phase
  `x ↦ ⟪e, Φ x⟫` to oscillate by at least `c₀ τ^A r^B` on every ball of radius `r` around a point
  where `‖ψ(·, y₀)‖ ≥ τ`.
* `taylor_exists_large`: such an oscillation along a ray gives a large derivative of order `≤ k`.
* `vdc`: one-dimensional van der Corput.
* `convex_phase_bound`: van der Corput, averaged over lines in a direction, on a small convex set.
* `decay_of_knapp`: averaging over balls of radius `σ`, the decay of the Fourier transform.
-/
/-- The map `x ↦ ∇_y φ(x, y₀)`. -/
noncomputable def Phi {n m : ℕ} (φ : E n → E m → ℝ) (y₀ : E m) (x : E n) : E m :=
  gradient (fun y => φ x y) y₀

/-- The `j`-th derivative of `F` at `x` in the direction `v`. -/
noncomputable def dd {n : ℕ} (j : ℕ) (F : E n → ℝ) (v x : E n) : ℝ :=
  iteratedDeriv j (fun s : ℝ => F (x + s • v)) 0

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartV
lemma contDiff_top_le' {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ) : ContDiff ℝ n g :=
  hg.of_le (by exact_mod_cast le_top)

lemma differentiable_iter {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n g) :=
  (contDiff_top_le' hg (n + 1)).differentiable_iteratedDeriv' n

lemma continuous_phase {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (L : ℝ) :
    Continuous (fun s => Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)) := by
  have : Continuous g := hg.continuous
  fun_prop

lemma vdc_one (g : ℝ → ℝ) (a b M η L : ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hab : a ≤ b)
    (hba : b - a ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hM : 1 ≤ M) (hL : 1 ≤ L)
    (h1 : ∀ s ∈ Set.Icc a b, η ≤ |deriv g s|)
    (h2 : ∀ s ∈ Set.Icc a b, |deriv (deriv g) s| ≤ M) :
    ‖∫ s in a..b, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ ≤ 3 * M / (L * η ^ 2) := by
  have hL0 : 0 < L := by linarith
  have hd1 : Differentiable ℝ g := by simpa using differentiable_iter hg 0
  have hd2 : Differentiable ℝ (deriv g) := by simpa using differentiable_iter hg 1
  have hc2 : Continuous (deriv (deriv g)) := by
    simpa [iteratedDeriv_succ] using (contDiff_top_le' hg 2).continuous_iteratedDeriv' 2
  have hne : ∀ s ∈ Set.Icc a b, deriv g s ≠ 0 := fun s hs h0 => by
    have := h1 s hs; rw [h0, abs_zero] at this; linarith
  have hLne : ∀ s ∈ Set.Icc a b, L * deriv g s ≠ 0 := fun s hs => mul_ne_zero hL0.ne' (hne s hs)
  set f : ℝ → ℂ := fun s => Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I) with hfdef
  set f' : ℝ → ℂ := fun s => f s * (((L * deriv g s : ℝ) : ℂ) * Complex.I) with hf'def
  set w : ℝ → ℂ := fun s => (((L * deriv g s)⁻¹ : ℝ) : ℂ) * (-Complex.I) with hwdef
  set w' : ℝ → ℂ := fun s =>
    ((-(L * deriv (deriv g) s) / (L * deriv g s) ^ 2 : ℝ) : ℂ) * (-Complex.I) with hw'def
  have hu : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hf : ∀ x, HasDerivAt f (f' x) x := fun x =>
    ((((hd1 x).hasDerivAt.const_mul L).ofReal_comp).mul_const Complex.I).cexp
  have hw : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x := by
    intro x hx
    rw [hu] at hx
    have hr : HasDerivAt (fun s => (L * deriv g s)⁻¹)
        (-(L * deriv (deriv g) x) / (L * deriv g x) ^ 2) x :=
      ((hd2 x).hasDerivAt.const_mul L).inv (hLne x hx)
    exact hr.ofReal_comp.mul_const (-Complex.I)
  have hfc : Continuous f := continuous_phase hg L
  have hf'c : Continuous f' := by
    have : Continuous (deriv g) := hd2.continuous
    simp only [hf'def]; fun_prop
  have hw'c : ContinuousOn w' (Set.uIcc a b) := by
    rw [hu]
    have hr : ContinuousOn (fun s => -(L * deriv (deriv g) s) / (L * deriv g s) ^ 2)
        (Set.Icc a b) :=
      ContinuousOn.div (by fun_prop) (by have := hd2.continuous; fun_prop)
        (fun s hs => pow_ne_zero 2 (hLne s hs))
    exact (Complex.continuous_ofReal.comp_continuousOn hr).mul continuousOn_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hw (fun x _ => hf x)
    (hw'c.intervalIntegrable) (hf'c.intervalIntegrable a b)
  have heq : ∫ s in a..b, f s = ∫ s in a..b, w s * f' s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [hu] at hs
    have hx : ((L * deriv g s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLne s hs
    show f s = w s * f' s
    have : w s * f' s = f s * (((L * deriv g s : ℝ) : ℂ)⁻¹ * ((L * deriv g s : ℝ) : ℂ)) *
        (-(Complex.I * Complex.I)) := by
      simp only [hwdef, hf'def, Complex.ofReal_inv]; ring
    rw [this, inv_mul_cancel₀ hx, Complex.I_mul_I]; ring
  have hnf : ∀ x, ‖f x‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I _
  have hnw : ∀ x ∈ Set.Icc a b, ‖w x‖ ≤ 1 / (L * η) := by
    intro x hx
    simp only [hwdef, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_mul, abs_of_pos hL0, one_div]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (h1 x hx) hL0.le)
  have hnw' : ∀ x ∈ Set.uIoc a b, ‖w' x * f x‖ ≤ M / (L * η ^ 2) := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self (by simpa [Set.uIoc_of_le hab] using hx)
    rw [norm_mul, hnf, mul_one]
    simp only [hw'def, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    have hd : deriv g x ≠ 0 := hne x hx'
    have hrw : |-(L * deriv (deriv g) x) / (L * deriv g x) ^ 2|
        = |deriv (deriv g) x| / (L * |deriv g x| ^ 2) := by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hL0, abs_pow, abs_mul, abs_of_pos hL0]
      field_simp
    rw [hrw]
    have hη2 : L * η ^ 2 ≤ L * |deriv g x| ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le (h1 x hx') 2) hL0.le
    exact div_le_div₀ (by linarith) (h2 x hx') (by positivity) hη2
  have hint : ‖∫ x in a..b, w' x * f x‖ ≤ M / (L * η ^ 2) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const hnw'
    rw [abs_of_nonneg (by linarith)] at this
    calc _ ≤ _ := this
      _ ≤ M / (L * η ^ 2) * 1 := mul_le_mul_of_nonneg_left hba (by positivity)
      _ = _ := mul_one _
  have hbm : b ∈ Set.Icc a b := Set.right_mem_Icc.2 hab
  have ham : a ∈ Set.Icc a b := Set.left_mem_Icc.2 hab
  have hend : ∀ x ∈ Set.Icc a b, ‖w x * f x‖ ≤ 1 / (L * η) := fun x hx => by
    rw [norm_mul, hnf, mul_one]; exact hnw x hx
  have hcmp : 1 / (L * η) ≤ M / (L * η ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 1 * (L * η ^ 2) ≤ M * (L * η) := by
      have h3 : η ^ 2 ≤ η := by nlinarith
      calc 1 * (L * η ^ 2) ≤ 1 * (L * η) := by gcongr
        _ ≤ M * (L * η) := mul_le_mul_of_nonneg_right hM (by positivity)
    exact this
  change ‖∫ s in a..b, f s‖ ≤ _
  rw [heq, hibp]
  calc ‖w b * f b - w a * f a - ∫ x in a..b, w' x * f x‖
      ≤ ‖w b * f b‖ + ‖w a * f a‖ + ‖∫ x in a..b, w' x * f x‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ M / (L * η ^ 2) + M / (L * η ^ 2) + M / (L * η ^ 2) := by
        gcongr
        · exact (hend b hbm).trans hcmp
        · exact (hend a ham).trans hcmp
    _ = 3 * M / (L * η ^ 2) := by ring

/-- Mean value bound: `|g^{(j)}| ≥ η` gives `η |t - s| ≤ |g^{(j-1)} t - g^{(j-1)} s|`. -/
lemma mvt_lower {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ) (a b η : ℝ)
    (h : ∀ s ∈ Set.Icc a b, η ≤ |iteratedDeriv (n + 1) g s|) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      η * |t - s| ≤ |iteratedDeriv n g t - iteratedDeriv n g s| := by
  have key : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      η * |t - s| ≤ |iteratedDeriv n g t - iteratedDeriv n g s| := by
    intro s hs t ht hst
    have hd := differentiable_iter hg n
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope (iteratedDeriv n g) hst
      hd.continuous.continuousOn (hd.differentiableOn)
    rw [← iteratedDeriv_succ] at hceq
    have hcm : c ∈ Set.Icc a b := ⟨hs.1.trans hc.1.le, hc.2.le.trans ht.2⟩
    have hts : 0 < t - s := sub_pos.2 hst
    have : iteratedDeriv n g t - iteratedDeriv n g s = iteratedDeriv (n + 1) g c * (t - s) := by
      rw [hceq]; field_simp
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_right (h c hcm) (abs_nonneg _)
  intro s hs t ht
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact key s hs t ht hlt
  · subst heq; simp
  · rw [abs_sub_comm t s, abs_sub_comm (iteratedDeriv n g t)]
    exact key t ht s hs hgt

lemma vdc_aux (n : ℕ) : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ (g : ℝ → ℝ) (a b M η L : ℝ),
    ContDiff ℝ (⊤ : ℕ∞) g → a ≤ b → b - a ≤ 1 → 0 < η → η ≤ 1 → 1 ≤ M → 1 ≤ L →
    (∀ s ∈ Set.Icc a b, η ≤ |iteratedDeriv (n + 1) g s|) →
    (∀ s ∈ Set.Icc a b, |iteratedDeriv 2 g s| ≤ M) →
    ‖∫ s in a..b, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ ≤
      C * M * L ^ (-c) * η ^ (-(2 : ℝ)) := by
  induction n with
  | zero =>
    refine ⟨3, 1, by norm_num, one_pos, ?_⟩
    intro g a b M η L hg hab hba hη hη1 hM hL h1 h2
    have hL0 : 0 < L := by linarith
    have := vdc_one g a b M η L hg hab hba hη hη1 hM hL (by simpa using h1)
      (by simpa [iteratedDeriv_succ] using h2)
    rw [Real.rpow_neg hL0.le, Real.rpow_neg hη.le, Real.rpow_one, Real.rpow_two]
    calc _ ≤ 3 * M / (L * η ^ 2) := this
      _ = _ := by field_simp
  | succ n ih =>
    obtain ⟨C', c', hC', hc', ih⟩ := ih
    refine ⟨2 * C' + 4, c' / 3, by linarith, by positivity, ?_⟩
    intro g a b M η L hg hab hba hη hη1 hM hL h1 h2
    have hL0 : 0 < L := by linarith
    set H := iteratedDeriv (n + 1) g with hH
    set α : ℝ := L ^ (-(c' / 3)) with hαdef
    have hα0 : 0 < α := Real.rpow_pos_of_pos hL0 _
    have hα1 : α ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
    set δ : ℝ := 2 * α / η with hδdef
    have hδ0 : 0 ≤ δ := by positivity
    have hηδ : η * δ = 2 * α := by rw [hδdef]; field_simp
    have hmvt := mvt_lower hg (n + 1) a b η h1
    obtain ⟨s0, hs0, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
      (Set.nonempty_Icc.2 hab) ((differentiable_iter hg (n + 1)).continuous.abs.continuousOn)
    have good : ∀ t ∈ Set.Icc a b, δ ≤ |t - s0| → α ≤ |H t| := by
      intro t ht hδt
      by_cases hα : α ≤ |H s0|
      · exact hα.trans (hmin ht)
      · push Not at hα
        have h3 := hmvt s0 hs0 t ht
        have h4 : η * δ ≤ η * |t - s0| := mul_le_mul_of_nonneg_left hδt hη.le
        have h5 : |H t - H s0| ≤ |H t| + |H s0| := abs_sub _ _
        linarith
    -- the bound on a piece where `|H| ≥ α`
    set B : ℝ := C' * M * L ^ (-c') * α ^ (-(2 : ℝ)) with hBdef
    have hB0 : 0 ≤ B := by positivity
    have piece : ∀ p q : ℝ, p ≤ q → Set.Icc p q ⊆ Set.Icc a b →
        (p = q ∨ ∀ t ∈ Set.Icc p q, α ≤ |H t|) →
        ‖∫ s in p..q, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ ≤ B := by
      intro p q hpq hsub hcase
      rcases hcase with hpq' | hgood
      · subst hpq'; simpa using hB0
      · have hqp : q - p ≤ 1 := by
          have := hsub (Set.left_mem_Icc.2 hpq); have := hsub (Set.right_mem_Icc.2 hpq)
          linarith [this.2, (hsub (Set.left_mem_Icc.2 hpq)).1]
        exact ih g p q M α L hg hpq hqp hα0 hα1 hM hL hgood (fun s hs => h2 s (hsub hs))
    set u := max a (s0 - δ) with hudef
    set v := min b (s0 + δ) with hvdef
    have hau : a ≤ u := le_max_left _ _
    have hus0 : u ≤ s0 := max_le hs0.1 (by linarith)
    have hs0v : s0 ≤ v := le_min hs0.2 (by linarith)
    have hvb : v ≤ b := min_le_left _ _
    have hvu : v - u ≤ 2 * δ := by
      have : v ≤ s0 + δ := min_le_right _ _
      have : s0 - δ ≤ u := le_max_right _ _
      linarith
    have hF := continuous_phase hg L
    have hsplit : ∫ s in a..b, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I) =
        (∫ s in a..u, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)) +
        (∫ s in u..v, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)) +
        (∫ s in v..b, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _)
          (hF.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _)
          (hF.intervalIntegrable _ _)]
    have hleft : ‖∫ s in a..u, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ ≤ B := by
      refine piece a u hau (Set.Icc_subset_Icc le_rfl (hus0.trans hs0.2)) ?_
      by_cases hle : s0 - δ ≤ a
      · left; exact (max_eq_left hle).symm
      · right
        intro t ht
        refine good t ⟨ht.1, ht.2.trans (hus0.trans hs0.2)⟩ ?_
        have : u = s0 - δ := max_eq_right (by linarith)
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.2]
    have hright : ‖∫ s in v..b, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ ≤ B := by
      refine piece v b hvb (Set.Icc_subset_Icc (hs0.1.trans hs0v) le_rfl) ?_
      by_cases hle : b ≤ s0 + δ
      · left; exact min_eq_left hle
      · right
        intro t ht
        refine good t ⟨(hs0.1.trans hs0v).trans ht.1, ht.2⟩ ?_
        have : v = s0 + δ := min_eq_right (by linarith)
        rw [abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.1]
    have hmid : ‖∫ s in u..v, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * δ := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v) (C := 1)
        (f := fun s => Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I))
        (fun x _ => (Complex.norm_exp_ofReal_mul_I _).le)
      rw [one_mul, abs_of_nonneg (by linarith)] at this
      linarith
    -- arithmetic
    have hBα : B = C' * M * α := by
      have : L ^ (-c') * α ^ (-(2 : ℝ)) = α := by
        rw [hαdef, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
        congr 1; ring
      rw [hBdef, mul_assoc (C' * M), this]
    have hE : η ^ (-(2 : ℝ)) = 1 / η ^ 2 := by
      rw [Real.rpow_neg hη.le, Real.rpow_two, one_div]
    have hE1 : 1 ≤ 1 / η ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_one₀ hη.le hη1
    have hδE : 2 * δ ≤ 4 * M * α * (1 / η ^ 2) := by
      have h6 : 1 / η ≤ 1 / η ^ 2 := by
        rw [div_le_div_iff₀ hη (by positivity), one_mul, one_mul]; nlinarith
      have h7 : 2 * δ = 4 * α * (1 / η) := by rw [hδdef]; ring
      rw [h7]
      calc 4 * α * (1 / η) ≤ 4 * α * (1 / η ^ 2) := by gcongr
        _ ≤ 4 * M * α * (1 / η ^ 2) := by
          have : 4 * α ≤ 4 * M * α := by nlinarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
    have hBE : 2 * B ≤ 2 * C' * M * α * (1 / η ^ 2) := by
      rw [hBα]
      have : 0 ≤ 2 * C' * M * α := by positivity
      calc 2 * (C' * M * α) = 2 * C' * M * α * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hE1 this
    rw [hsplit, hE]
    calc _ ≤ ‖∫ s in a..u, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ +
          ‖∫ s in u..v, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ +
          ‖∫ s in v..b, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ B + 2 * δ + B := by gcongr
      _ ≤ (2 * C' + 4) * M * α * (1 / η ^ 2) := by nlinarith

theorem vdc (j : ℕ) (hj : 1 ≤ j) : ∃ C c : ℝ, 0 < c ∧ ∀ (g : ℝ → ℝ) (a b M η L : ℝ),
    ContDiff ℝ (⊤ : ℕ∞) g → a ≤ b → b - a ≤ 1 → 0 < η → η ≤ 1 → 1 ≤ M → 1 ≤ L →
    (∀ s ∈ Set.Icc a b, η ≤ |iteratedDeriv j g s|) →
    (∀ s ∈ Set.Icc a b, |iteratedDeriv 2 g s| ≤ M) →
    ‖∫ s in a..b, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ ≤
      C * M * L ^ (-c) * η ^ (-(2 : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  obtain ⟨C, c, -, hc, h⟩ := vdc_aux n
  exact ⟨C, c, hc, h⟩

end TaoBR.TaoDecay.PartV
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
/-! ## Part V: one-dimensional lemmas -/
alias vdc := TaoBR.TaoDecay.PartV.vdc

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartV
/-! ## Taylor -/
lemma taylor_pos (k : ℕ) (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (M s : ℝ) (hs : 0 < s)
    (hs1 : s ≤ 1) (hM : ∀ u ∈ Set.Icc 0 s, |iteratedDeriv (k + 1) g u| ≤ M) :
    |g s - g 0| ≤ ∑ j ∈ Finset.range k, |iteratedDeriv (j + 1) g 0| + M * s ^ (k + 1) := by
  have hU : UniqueDiffOn ℝ (Set.Icc 0 s) := uniqueDiffOn_Icc hs
  have hwithin : ∀ n : ℕ, ∀ y ∈ Set.Icc 0 s,
      iteratedDerivWithin n g (Set.Icc 0 s) y = iteratedDeriv n g y :=
    fun n y hy => iteratedDerivWithin_eq_iteratedDeriv hU (contDiff_top_le' hg n).contDiffAt hy
  have h0 : (0 : ℝ) ∈ Set.Icc 0 s := Set.left_mem_Icc.2 hs.le
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 h0)
  have hrem := taylor_mean_remainder_bound (f := g) (n := k) (C := M) hs.le
    (by exact_mod_cast (contDiff_top_le' hg (k + 1)).contDiffOn) (Set.right_mem_Icc.2 hs.le)
    (fun y hy => by rw [Real.norm_eq_abs, hwithin _ y hy]; exact hM y hy)
  rw [taylor_within_apply, Finset.sum_range_succ', Real.norm_eq_abs] at hrem
  set S := ∑ j ∈ Finset.range k,
    (((j + 1).factorial : ℝ)⁻¹ * (s - 0) ^ (j + 1)) • iteratedDerivWithin (j + 1) g (Set.Icc 0 s) 0
    with hSdef
  have hS : |S| ≤ ∑ j ∈ Finset.range k, |iteratedDeriv (j + 1) g 0| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [hwithin _ 0 h0, smul_eq_mul, abs_mul, sub_zero]
    have hc0 : 0 ≤ ((j + 1).factorial : ℝ)⁻¹ * s ^ (j + 1) := by positivity
    have hc1 : ((j + 1).factorial : ℝ)⁻¹ * s ^ (j + 1) ≤ 1 := by
      have h1 : s ^ (j + 1) ≤ 1 := pow_le_one₀ hs.le hs1
      have h2 : ((j + 1).factorial : ℝ)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
      calc _ ≤ 1 * 1 := mul_le_mul h2 h1 (by positivity) zero_le_one
        _ = 1 := one_mul 1
    rw [abs_of_nonneg hc0]
    calc _ ≤ 1 * |iteratedDeriv (j + 1) g 0| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
      _ = _ := one_mul _
  have hfirst : (((0 : ℕ).factorial : ℝ)⁻¹ * (s - 0) ^ 0) • iteratedDerivWithin 0 g (Set.Icc 0 s) 0
      = g 0 := by simp
  rw [hfirst] at hrem
  have hrem' : M * (s - 0) ^ (k + 1) / k.factorial ≤ M * s ^ (k + 1) := by
    rw [sub_zero]
    exact div_le_self (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  have : g s - g 0 = (g s - (S + g 0)) + S := by ring
  rw [this]
  calc |(g s - (S + g 0)) + S| ≤ |g s - (S + g 0)| + |S| := abs_add_le _ _
    _ ≤ M * s ^ (k + 1) + ∑ j ∈ Finset.range k, |iteratedDeriv (j + 1) g 0| :=
        add_le_add (hrem.trans hrem') hS
    _ = _ := add_comm _ _

lemma taylor_sum (k : ℕ) (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (M r θ s : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hs : |s| ≤ r)
    (hM : ∀ u : ℝ, |u| ≤ r → |iteratedDeriv (k + 1) g u| ≤ M) (hθ : θ ≤ |g s - g 0|) :
    θ - M * r ^ (k + 1) ≤ ∑ j ∈ Finset.range k, |iteratedDeriv (j + 1) g 0| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by simpa using hr.le))
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, |iteratedDeriv (j + 1) g 0| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  rcases lt_trichotomy s 0 with hneg | hzero | hpos
  · set g' : ℝ → ℝ := fun x => g (-x) with hg'
    have hg'c : ContDiff ℝ (⊤ : ℕ∞) g' := hg.comp contDiff_neg
    have habs : ∀ n : ℕ, ∀ u : ℝ, |iteratedDeriv n g' u| = |iteratedDeriv n g (-u)| := by
      intro n u
      rw [hg', iteratedDeriv_comp_neg, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
    have hs' : 0 < -s := neg_pos.2 hneg
    have h := taylor_pos k g' hg'c M (-s) hs' ((abs_of_neg hneg ▸ hs).trans hr1)
      (fun u hu => by
        rw [habs]; apply hM; rw [abs_neg, abs_of_nonneg hu.1]
        exact hu.2.trans (abs_of_neg hneg ▸ hs))
    simp only [hg', neg_neg, neg_zero] at h
    have hpow : M * (-s) ^ (k + 1) ≤ M * r ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs'.le (abs_of_neg hneg ▸ hs) _) hM0
    have hsumeq : ∑ j ∈ Finset.range k, |iteratedDeriv (j + 1) (fun x => g (-x)) 0|
        = ∑ j ∈ Finset.range k, |iteratedDeriv (j + 1) g 0| :=
      Finset.sum_congr rfl fun j _ => by
        have := habs (j + 1) 0; simp only [hg', neg_zero] at this; exact this
    rw [hsumeq] at h
    linarith
  · subst hzero
    simp only [sub_self, abs_zero] at hθ
    have : 0 ≤ M * r ^ (k + 1) := by positivity
    linarith
  · have h := taylor_pos k g hg M s hpos ((abs_of_pos hpos ▸ hs).trans hr1)
      (fun u hu => hM u (by rw [abs_of_nonneg hu.1]; exact hu.2.trans (abs_of_pos hpos ▸ hs)))
    have hpow : M * s ^ (k + 1) ≤ M * r ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le (abs_of_pos hpos ▸ hs) _) hM0
    linarith

theorem taylor_exists_large (k : ℕ) (hk : 1 ≤ k) (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (M r θ s : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hs : |s| ≤ r)
    (hM : ∀ u : ℝ, |u| ≤ r → |iteratedDeriv (k + 1) g u| ≤ M) (hθ : θ ≤ |g s - g 0|) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ (θ - M * r ^ (k + 1)) / k ≤ |iteratedDeriv j g 0| := by
  have h := taylor_sum k g hg M r θ s hr hr1 hs hM hθ
  by_contra hcon
  push Not at hcon
  have hlt : ∑ j ∈ Finset.range k, |iteratedDeriv (j + 1) g 0|
      < ∑ _j ∈ Finset.range k, (θ - M * r ^ (k + 1)) / k :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega))
      fun j hj => hcon (j + 1) (by omega) (by have := Finset.mem_range.1 hj; omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [mul_div_cancel₀ _ hk0] at hlt
  linarith

end TaoBR.TaoDecay.PartV
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
alias taylor_exists_large := TaoBR.TaoDecay.PartV.taylor_exists_large

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartR
/-! ## Directional derivatives -/
/-- Derivatives along a line are directional derivatives at the moving point. -/
theorem iteratedDeriv_line {n : ℕ} (j : ℕ) (F : E n → ℝ) (v x : E n) (s₀ : ℝ) :
    iteratedDeriv j (fun s : ℝ => F (x + s • v)) s₀ = dd j F v (x + s₀ • v) := by
  unfold dd
  have h := congrFun (iteratedDeriv_comp_add_const j (fun s : ℝ => F (x + s • v)) s₀) 0
  simp only [zero_add] at h
  rw [← h]
  congr 1
  funext s
  congr 1
  rw [add_smul]
  abel

end TaoBR.TaoDecay.PartR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
/-! ## Part D: decay from the oscillation bound -/
alias iteratedDeriv_line := TaoBR.TaoDecay.PartR.iteratedDeriv_line

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartR
lemma top_le {j : ℕ} : ((j : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

lemma top_lt {j : ℕ} : ((j : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast ENat.natCast_lt_top j

/-- `dd` is the iterated Fréchet derivative applied to `v, …, v`. -/
lemma dd_eq {n : ℕ} (j : ℕ) (F : E n → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v x : E n) :
    dd j F v x = iteratedFDeriv ℝ j F x (fun _ => v) := by
  unfold dd
  set L : ℝ →L[ℝ] E n := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hL
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => F (x + y)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have hfun : (fun s : ℝ => F (x + s • v)) = (fun y : E n => F (x + y)) ∘ L := by
    funext s; simp [hL]
  rw [iteratedDeriv_eq_iteratedFDeriv, hfun, L.iteratedFDeriv_comp_right hG 0 top_le,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp [hL]

lemma dd_inner {n m : ℕ} (Φ : E n → E m) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : ℕ) (e : E m)
    (v x : E n) :
    dd j (fun z => inner ℝ e (Φ z)) v x = inner ℝ e (iteratedFDeriv ℝ j Φ x (fun _ => v)) := by
  have hF : (fun z => inner ℝ e (Φ z)) = (innerSL ℝ e) ∘ Φ := by
    funext z; simp
  rw [dd_eq j _ (by rw [hF]; exact (innerSL ℝ e).contDiff.comp hΦ), hF,
    (innerSL ℝ e).iteratedFDeriv_comp_left hΦ.contDiffAt top_le]
  simp

lemma norm_apply_const_le {n m : ℕ} {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E n) (E m))
    (v : E n) (hv : ‖v‖ = 1) : ‖A (fun _ => v)‖ ≤ ‖A‖ := by
  have := A.le_opNorm (fun _ => v)
  simpa [hv] using this

/-- Uniform bounds on the directional derivatives of `⟪e, Φ⟫` on a ball, and their Lipschitz
dependence on the base point. -/
theorem dd_bounds {n m : ℕ} (Φ : E n → E m) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (ρ : ℝ) (k : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ e : E m, ‖e‖ = 1 → ∀ v : E n, ‖v‖ = 1 → ∀ j ≤ k,
      ∀ x ∈ closedBall (0 : E n) ρ, ∀ x' ∈ closedBall (0 : E n) ρ,
        |dd j (fun z => inner ℝ e (Φ z)) v x| ≤ M ∧
        |dd j (fun z => inner ℝ e (Φ z)) v x - dd j (fun z => inner ℝ e (Φ z)) v x'| ≤
          M * ‖x - x'‖ := by
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ x ∈ closedBall (0 : E n) ρ, ‖iteratedFDeriv ℝ i Φ x‖ ≤ C :=
    fun i => (isCompact_closedBall (0 : E n) ρ).exists_bound_of_continuousOn
      (hΦ.continuous_iteratedFDeriv top_le).continuousOn
  choose C hC using hb
  set S : ℝ := ∑ i ∈ Finset.range (k + 2), |C i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hCi : ∀ i ≤ k + 1, C i ≤ S := by
    intro i hi
    refine (le_abs_self _).trans ?_
    exact Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  refine ⟨1 + S, by linarith, ?_⟩
  intro e he v hv j hj x hx x' hx'
  rw [dd_inner Φ hΦ, dd_inner Φ hΦ, ← inner_sub_right]
  constructor
  · refine (abs_real_inner_le_norm _ _).trans ?_
    rw [he, one_mul]
    refine (norm_apply_const_le _ v hv).trans ((hC j x hx).trans ?_)
    linarith [hCi j (by omega)]
  · refine (abs_real_inner_le_norm _ _).trans ?_
    rw [he, one_mul, ← sub_apply]
    refine (norm_apply_const_le _ v hv).trans ?_
    have hlip := (convex_closedBall (0 : E n) ρ).norm_image_sub_le_of_norm_fderiv_le
      (f := iteratedFDeriv ℝ j Φ) (C := C (j + 1))
      (fun y _ => (hΦ.differentiable_iteratedFDeriv top_lt).differentiableAt)
      (fun y hy => by rw [norm_fderiv_iteratedFDeriv]; exact hC (j + 1) y hy) hx' hx
    refine hlip.trans ?_
    gcongr
    linarith [hCi (j + 1) (by omega)]

end TaoBR.TaoDecay.PartR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
alias dd_bounds := TaoBR.TaoDecay.PartR.dd_bounds

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartR
/-! ## Van der Corput on a convex set -/
/-- The phase `exp(-2πi t F)`. -/
noncomputable def phase {n : ℕ} (t : ℝ) (F : E n → ℝ) (y : E n) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((t * F y : ℝ) : ℂ)))

lemma phase_eq {n : ℕ} (t : ℝ) (F : E n → ℝ) (y : E n) :
    phase t F y = Complex.exp ((((2 * Real.pi * t) * (-F y) : ℝ) : ℂ) * Complex.I) := by
  unfold phase
  congr 1
  push_cast
  ring

lemma norm_phase {n : ℕ} (t : ℝ) (F : E n → ℝ) (y : E n) : ‖phase t F y‖ = 1 := by
  rw [phase_eq, Complex.norm_exp_ofReal_mul_I]

lemma continuous_phase {n : ℕ} (t : ℝ) (F : E n → ℝ) (hF : Continuous F) :
    Continuous (phase t F) := by
  unfold phase
  fun_prop

/-- A closed convex nonempty subset of `[0, σ]` is a closed interval. -/
lemma eq_Icc_of_convex {J : Set ℝ} {σ : ℝ} (hc : Convex ℝ J) (hcl : IsClosed J)
    (hb : J ⊆ Set.Icc 0 σ) (hne : J.Nonempty) : J = Set.Icc (sInf J) (sSup J) := by
  have hK : IsCompact J := isCompact_Icc.of_isClosed_subset hcl hb
  ext s
  constructor
  · intro hs
    exact ⟨csInf_le hK.bddBelow hs, le_csSup hK.bddAbove hs⟩
  · intro hs
    exact (convex_iff_ordConnected.1 hc).out (hK.sInf_mem hne) (hK.sSup_mem hne) hs

lemma dist_le_two {n : ℕ} {x z v : E n} {σ s : ℝ} (hv : ‖v‖ = 1) (hs : s ∈ Set.Icc 0 σ)
    (hx : x + s • v ∈ closedBall z σ) : x ∈ closedBall z (2 * σ) := by
  rw [mem_closedBall] at hx ⊢
  have h1 : dist x (x + s • v) = s := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
  have := dist_triangle x (x + s • v) z
  linarith [hs.2]

/-- The bound on one line. -/
lemma line_bound {n j : ℕ} (C₀ c₀ : ℝ) (hc₀ : 0 < c₀)
    (hvdc : ∀ (g : ℝ → ℝ) (a b M η L : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) g → a ≤ b → b - a ≤ 1 → 0 < η → η ≤ 1 → 1 ≤ M → 1 ≤ L →
      (∀ s ∈ Set.Icc a b, η ≤ |iteratedDeriv j g s|) →
      (∀ s ∈ Set.Icc a b, |iteratedDeriv 2 g s| ≤ M) →
      ‖∫ s in a..b, Complex.exp (((L * g s : ℝ) : ℂ) * Complex.I)‖ ≤
        C₀ * M * L ^ (-c₀) * η ^ (-(2 : ℝ)))
    (F : E n → ℝ) (Q : Set (E n)) (x v : E n) (σ M η t : ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hQc : Convex ℝ Q) (hQcl : IsClosed Q)
    (hσ1 : σ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hM : 1 ≤ M) (ht : 1 ≤ t)
    (hjd : ∀ x ∈ Q, η ≤ |dd j F v x|) (h2d : ∀ x ∈ Q, |dd 2 F v x| ≤ M) :
    ‖∫ s in Set.Icc 0 σ, Q.indicator (phase t F) (x + s • v)‖ ≤
      |C₀| * M * t ^ (-c₀) * η ^ (-(2 : ℝ)) := by
  have hB0 : 0 ≤ |C₀| * M * t ^ (-c₀) * η ^ (-(2 : ℝ)) := by
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ t) (-c₀)
    have := Real.rpow_nonneg hη.le (-(2:ℝ))
    have := abs_nonneg C₀
    positivity
  set P : Set ℝ := (fun s : ℝ => x + s • v) ⁻¹' Q with hP
  have hcont : Continuous (fun s : ℝ => x + s • v) := by fun_prop
  have hPm : MeasurableSet P := (hQcl.preimage hcont).measurableSet
  have hind : ∀ s : ℝ, Q.indicator (phase t F) (x + s • v) =
      P.indicator (fun s => phase t F (x + s • v)) s := by
    intro s
    by_cases h : x + s • v ∈ Q
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show s ∈ P from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show s ∉ P from h)]
  simp_rw [hind]
  rw [setIntegral_indicator hPm]
  set J : Set ℝ := Set.Icc 0 σ ∩ P with hJ
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · rw [hJe, Measure.restrict_empty, integral_zero_measure, norm_zero]
    exact hB0
  have hPc : Convex ℝ P :=
    (hQc.translate_preimage_right x).is_linear_preimage (IsLinearMap.isLinearMap_smul' v)
  have hJc : Convex ℝ J := (convex_Icc 0 σ).inter hPc
  have hJcl : IsClosed J := isClosed_Icc.inter (hQcl.preimage hcont)
  have hJeq := eq_Icc_of_convex hJc hJcl Set.inter_subset_left hJne
  set a := sInf J
  set b := sSup J
  obtain ⟨s0, hs0⟩ := hJne
  have hab : a ≤ b := by
    rw [hJeq] at hs0; exact hs0.1.trans hs0.2
  have haJ : a ∈ J := by rw [hJeq]; exact Set.left_mem_Icc.2 hab
  have hbJ : b ∈ J := by rw [hJeq]; exact Set.right_mem_Icc.2 hab
  have hsub : ∀ s ∈ Set.Icc a b, x + s • v ∈ Q := by
    intro s hs
    rw [← hJeq] at hs
    exact hs.2
  rw [hJeq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simp_rw [phase_eq]
  set g : ℝ → ℝ := fun s => -F (x + s • v) with hg
  have hgd : ∀ i s, iteratedDeriv i g s = -dd i F v (x + s • v) := by
    intro i s
    rw [show g = -(fun s : ℝ => F (x + s • v)) from rfl, iteratedDeriv_neg, iteratedDeriv_line]
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hL : 1 ≤ 2 * Real.pi * t := by nlinarith
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := (hF.comp (by fun_prop)).neg
  have key := hvdc g a b M η (2 * Real.pi * t) hgs hab (by linarith [haJ.1.1, hbJ.1.2]) hη hη1
    hM hL
    (fun s hs => by rw [hgd, abs_neg]; exact hjd _ (hsub s hs))
    (fun s hs => by rw [hgd, abs_neg]; exact h2d _ (hsub s hs))
  refine key.trans ?_
  have hLc : (2 * Real.pi * t) ^ (-c₀) ≤ t ^ (-c₀) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by nlinarith) (by linarith)
  have h1 : 0 ≤ M * (2 * Real.pi * t) ^ (-c₀) * η ^ (-(2 : ℝ)) := by
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.pi * t) (-c₀)
    have := Real.rpow_nonneg hη.le (-(2:ℝ))
    positivity
  calc C₀ * M * (2 * Real.pi * t) ^ (-c₀) * η ^ (-(2 : ℝ))
      = C₀ * (M * (2 * Real.pi * t) ^ (-c₀) * η ^ (-(2 : ℝ))) := by ring
    _ ≤ |C₀| * (M * (2 * Real.pi * t) ^ (-c₀) * η ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h1
    _ = (|C₀| * M) * (2 * Real.pi * t) ^ (-c₀) * η ^ (-(2 : ℝ)) := by ring
    _ ≤ (|C₀| * M) * t ^ (-c₀) * η ^ (-(2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLc (mul_nonneg (abs_nonneg _) (by linarith)))
          (Real.rpow_nonneg hη.le _)

lemma line_zero {n : ℕ} (F : E n → ℝ) (Q : Set (E n)) (x z v : E n) (σ t : ℝ)
    (hQ : Q ⊆ closedBall z σ) (hv : ‖v‖ = 1) (hx : x ∉ closedBall z (2 * σ)) :
    ∫ s in Set.Icc 0 σ, Q.indicator (phase t F) (x + s • v) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro s hs
  apply Set.indicator_of_notMem
  intro hq
  exact hx (dist_le_two hv hs (hQ hq))

/-- Averaging over the segments `x + [0, σ] v`. -/
lemma average {n : ℕ} (f : E n → ℂ) (hf : Measurable f) (z v : E n) (σ : ℝ) (hσ : 0 < σ)
    (hv : ‖v‖ = 1) (hsupp : ∀ y, f y ≠ 0 → y ∈ closedBall z σ) (hb : ∀ y, ‖f y‖ ≤ 1) :
    σ • ∫ x, f x = ∫ x, ∫ s in Set.Icc 0 σ, f (x + s • v) := by
  set G : E n → ℝ → ℂ := fun x s => (Set.Icc 0 σ).indicator (fun s => f (x + s • v)) s with hG
  have h1 : ∀ x, ∫ s in Set.Icc 0 σ, f (x + s • v) = ∫ s, G x s := by
    intro x
    rw [hG, integral_indicator measurableSet_Icc]
  simp_rw [h1]
  -- integrability of `G` on the product
  set K : Set (E n × ℝ) := closedBall z (2 * σ) ×ˢ Set.Icc 0 σ with hK
  have hKm : MeasurableSet K := measurableSet_closedBall.prod measurableSet_Icc
  have hKfin : (volume.prod volume) K ≠ ∞ := by
    rw [hK, Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_closedBall_lt_top.ne measure_Icc_lt_top.ne
  have hbound : Integrable (K.indicator (fun _ => (1 : ℝ))) (volume.prod volume) :=
    (integrable_indicator_iff hKm).2 (integrableOn_const hKfin)
  have hGm : Measurable (Function.uncurry G) := by
    have hm1 : Measurable (fun p : E n × ℝ => f (p.1 + p.2 • v)) :=
      hf.comp (by fun_prop : Continuous (fun p : E n × ℝ => p.1 + p.2 • v)).measurable
    have : Function.uncurry G =
        (Prod.snd ⁻¹' Set.Icc 0 σ).indicator (fun p : E n × ℝ => f (p.1 + p.2 • v)) := by
      funext p
      simp only [Function.uncurry, hG, Set.indicator, Set.mem_preimage]
    rw [this]
    exact hm1.indicator (measurable_snd measurableSet_Icc)
  have hGi : Integrable (Function.uncurry G) (volume.prod volume) := by
    refine hbound.mono' hGm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    rintro ⟨x, s⟩
    simp only [Function.uncurry, hG]
    by_cases hs : s ∈ Set.Icc 0 σ
    · rw [Set.indicator_of_mem hs]
      by_cases h0 : f (x + s • v) = 0
      · rw [h0, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      · have hxK : (x, s) ∈ K := ⟨dist_le_two hv hs (hsupp _ h0), hs⟩
        rw [Set.indicator_of_mem hxK]
        exact hb _
    · rw [Set.indicator_of_notMem hs, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  rw [integral_integral_swap hGi]
  have h2 : ∀ s, ∫ x, G x s = (Set.Icc 0 σ).indicator (fun _ => ∫ x, f x) s := by
    intro s
    by_cases hs : s ∈ Set.Icc 0 σ
    · simp only [hG, Set.indicator_of_mem hs]
      exact integral_add_right_eq_self f (s • v)
    · simp only [hG, Set.indicator_of_notMem hs, integral_zero]
  simp_rw [h2]
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hσ.le, sub_zero]

/-- Van der Corput on a small closed convex set, averaged over the lines in direction `v`. -/
theorem convex_phase_bound (n j : ℕ) (hj : 1 ≤ j) : ∃ C c : ℝ, 0 < c ∧
    ∀ (F : E n → ℝ) (Q : Set (E n)) (z v : E n) (σ M η t : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) F → Convex ℝ Q → IsClosed Q → Q ⊆ closedBall z σ →
      0 < σ → σ ≤ 1 → ‖v‖ = 1 → 0 < η → η ≤ 1 → 1 ≤ M → 1 ≤ t →
      (∀ x ∈ Q, η ≤ |dd j F v x|) → (∀ x ∈ Q, |dd 2 F v x| ≤ M) →
      ‖∫ x in Q, Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ)))‖ ≤
        C * σ ^ n * σ⁻¹ * M * t ^ (-c) * η ^ (-(2 : ℝ)) := by
  obtain ⟨C₀, c₀, hc₀, hvdc⟩ := vdc j hj
  set V : ℝ := (volume (ball (0 : E n) 1)).toReal with hV
  refine ⟨|C₀| * 2 ^ n * V, c₀, hc₀, ?_⟩
  intro F Q z v σ M η t hF hQc hQcl hQ hσ hσ1 hv hη hη1 hM ht hjd h2d
  set B : ℝ := |C₀| * M * t ^ (-c₀) * η ^ (-(2 : ℝ)) with hB
  have hB0 : 0 ≤ B := by
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ t) (-c₀)
    have := Real.rpow_nonneg hη.le (-(2:ℝ))
    have := abs_nonneg C₀
    positivity
  have hQm : MeasurableSet Q := hQcl.measurableSet
  set f : E n → ℂ := Q.indicator (phase t F) with hf
  have hfm : Measurable f := (continuous_phase t F hF.continuous).measurable.indicator hQm
  have hLHS : ∫ x in Q, Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) =
      ∫ x, f x := by
    rw [hf, integral_indicator hQm]
    rfl
  rw [hLHS]
  have havg := average f hfm z v σ hσ hv
    (fun y hy => by
      by_contra h
      exact hy (Set.indicator_of_notMem (fun hq => h (hQ hq)) _))
    (fun y => by
      by_cases hq : y ∈ Q
      · rw [hf, Set.indicator_of_mem hq, norm_phase]
      · rw [hf, Set.indicator_of_notMem hq, norm_zero]; exact zero_le_one)
  set I : E n → ℂ := fun x => ∫ s in Set.Icc 0 σ, f (x + s • v) with hI
  have hIb : ∀ x, ‖I x‖ ≤ (closedBall z (2 * σ)).indicator (fun _ => B) x := by
    intro x
    by_cases hx : x ∈ closedBall z (2 * σ)
    · rw [Set.indicator_of_mem hx]
      exact line_bound C₀ c₀ hc₀ hvdc F Q x v σ M η t hF hQc hQcl hσ1 hη hη1 hM ht hjd h2d
    · rw [Set.indicator_of_notMem hx, hI]
      simp only
      rw [line_zero F Q x z v σ t hQ hv hx, norm_zero]
  have hball : volume.real (closedBall z (2 * σ)) = (2 * σ) ^ n * V := by
    rw [measureReal_def, Measure.addHaar_closedBall volume z (by linarith), finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hint : ‖∫ x, I x‖ ≤ (2 * σ) ^ n * V * B := by
    refine (norm_integral_le_of_norm_le ?_ (Filter.Eventually.of_forall hIb)).trans ?_
    · exact (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    · rw [integral_indicator_const _ measurableSet_closedBall, hball, smul_eq_mul]
  have key : σ * ‖∫ x, f x‖ ≤ (2 * σ) ^ n * V * B := by
    have : ‖σ • ∫ x, f x‖ = σ * ‖∫ x, f x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    rw [← this, havg]
    exact hint
  have := (le_inv_mul_iff₀ hσ).2 key
  refine this.trans (le_of_eq ?_)
  rw [hB, mul_pow]
  ring

end TaoBR.TaoDecay.PartR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
alias convex_phase_bound := TaoBR.TaoDecay.PartR.convex_phase_bound

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartD
/-!
# Part D: `decay_of_knapp`

Averaging over balls of radius `σ` (via `integral_convolution`), the oscillation bound on each
ball through `taylor_exists_large`, `dd_bounds` and `convex_phase_bound`, and the choice
`τ = t^{-γ}` of the threshold. See `p2m-standalone/tao-br-readings/proofs/decay/PLAN.md`.
-/
/-- Averaging over balls: `vol(B_σ) ‖∫ G‖ ≤ K vol(B_R)` from bounds on the ball integrals. -/
theorem avg_bound {n : ℕ} (G : E n → ℂ) (hG : Integrable G) (σ R K : ℝ)
    (hK : ∀ c : E n, ‖∫ x in closedBall c σ, G x‖ ≤
      (closedBall (0 : E n) R).indicator (fun _ => K) c) :
    volume.real (closedBall (0 : E n) σ) * ‖∫ x, G x‖ ≤
      K * volume.real (closedBall (0 : E n) R) := by
  set f : E n → ℝ := (closedBall (0 : E n) σ).indicator 1 with hf_def
  have hf : Integrable f :=
    (integrableOn_const (C := (1 : ℝ)) (s := closedBall (0 : E n) σ)
      measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have key := integral_convolution (μ := (volume : Measure (E n)))
    (ν := (volume : Measure (E n))) (ContinuousLinearMap.lsmul ℝ ℝ) hf hG
  have hfint : ∫ x, f x = volume.real (closedBall (0 : E n) σ) :=
    integral_indicator_one measurableSet_closedBall
  rw [hfint] at key
  have hconv : ∀ c : E n, convolution f G (ContinuousLinearMap.lsmul ℝ ℝ) volume c =
      ∫ x in closedBall c σ, G x := by
    intro c
    rw [convolution_def, ← integral_indicator measurableSet_closedBall,
      ← integral_sub_left_eq_self _ volume c]
    congr 1
    ext t
    have e : ‖c - t‖ = ‖t - c‖ := norm_sub_rev _ _
    simp only [sub_zero, e, hf_def, ContinuousLinearMap.lsmul_apply, Set.indicator, mem_closedBall,
      dist_eq_norm, Pi.one_apply]
    split_ifs <;> simp
  have hb : Integrable ((closedBall (0 : E n) R).indicator (fun _ => K)) :=
    (integrableOn_const (C := K) (s := closedBall (0 : E n) R)
      measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have h1 : ‖∫ c, convolution f G (ContinuousLinearMap.lsmul ℝ ℝ) volume c‖ ≤
      ∫ c, (closedBall (0 : E n) R).indicator (fun _ => K) c := by
    apply norm_integral_le_of_norm_le hb
    exact Filter.Eventually.of_forall fun c => by rw [hconv]; exact hK c
  rw [key, integral_indicator_const _ measurableSet_closedBall] at h1
  simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs, smul_eq_mul] at h1
  rw [abs_of_nonneg measureReal_nonneg] at h1
  linarith [h1]

/-! ## Polynomial lower bounds -/
/-- `f τ ≥ κ τ^P` on `(0, 1]`. -/
def PB (f : ℝ → ℝ) : Prop := ∃ κ : ℝ, 0 < κ ∧ ∃ P : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → κ * τ ^ P ≤ f τ

theorem PB.pos {f : ℝ → ℝ} (h : PB f) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : 0 < f τ := by
  obtain ⟨κ, hκ, P, hP⟩ := h
  exact lt_of_lt_of_le (by positivity) (hP τ hτ hτ1)

theorem PB.const {a : ℝ} (ha : 0 < a) : PB (fun _ => a) :=
  ⟨a, ha, 0, fun τ _ _ => by simp⟩

theorem PB.id : PB (fun τ => τ) := ⟨1, one_pos, 1, fun τ _ _ => by simp⟩

theorem PB.mul {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun τ => f τ * g τ) := by
  obtain ⟨κ, hκ, P, hP⟩ := hf
  obtain ⟨κ', hκ', P', hP'⟩ := hg
  refine ⟨κ * κ', mul_pos hκ hκ', P + P', fun τ hτ hτ1 => ?_⟩
  have e : κ * κ' * τ ^ (P + P') = (κ * τ ^ P) * (κ' * τ ^ P') := by ring
  rw [e]
  exact mul_le_mul (hP τ hτ hτ1) (hP' τ hτ hτ1) (by positivity)
    ((by positivity : (0:ℝ) ≤ κ * τ ^ P).trans (hP τ hτ hτ1))

theorem PB.pow {f : ℝ → ℝ} (hf : PB f) (k : ℕ) : PB (fun τ => f τ ^ k) := by
  induction k with
  | zero => simpa using PB.const one_pos
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem PB.minf {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun τ => min (f τ) (g τ)) := by
  obtain ⟨κ, hκ, P, hP⟩ := hf
  obtain ⟨κ', hκ', P', hP'⟩ := hg
  refine ⟨min κ κ', lt_min hκ hκ', P + P', fun τ hτ hτ1 => le_min ?_ ?_⟩
  · have h1 : τ ^ (P + P') ≤ τ ^ P := pow_le_pow_of_le_one hτ.le hτ1 (by omega)
    calc min κ κ' * τ ^ (P + P') ≤ κ * τ ^ P :=
          mul_le_mul (min_le_left _ _) h1 (by positivity) hκ.le
      _ ≤ f τ := hP τ hτ hτ1
  · have h1 : τ ^ (P + P') ≤ τ ^ P' := pow_le_pow_of_le_one hτ.le hτ1 (by omega)
    calc min κ κ' * τ ^ (P + P') ≤ κ' * τ ^ P' :=
          mul_le_mul (min_le_right _ _) h1 (by positivity) hκ'.le
      _ ≤ g τ := hP' τ hτ hτ1

/-- `convex_phase_bound` with constants uniform in `1 ≤ j ≤ k`. -/
theorem cpb_uniform (n k : ℕ) : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ j : ℕ, 1 ≤ j → j ≤ k →
    ∀ (F : E n → ℝ) (Q : Set (E n)) (z v : E n) (σ M η t : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) F → Convex ℝ Q → IsClosed Q → Q ⊆ closedBall z σ →
      0 < σ → σ ≤ 1 → ‖v‖ = 1 → 0 < η → η ≤ 1 → 1 ≤ M → 1 ≤ t →
      (∀ x ∈ Q, η ≤ |dd j F v x|) → (∀ x ∈ Q, |dd 2 F v x| ≤ M) →
      ‖∫ x in Q, Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ)))‖ ≤
        C * σ ^ n * σ⁻¹ * M * t ^ (-c) * η ^ (-(2 : ℝ)) := by
  induction k with
  | zero => exact ⟨0, 1, le_rfl, one_pos, fun j h1 h2 => by omega⟩
  | succ k ih =>
    obtain ⟨C, c, hC, hc, h⟩ := ih
    obtain ⟨C', c', hc', h'⟩ := convex_phase_bound n (k + 1) (by omega)
    refine ⟨max C C', min c c', le_max_of_le_left hC, lt_min hc hc', ?_⟩
    intro j hj1 hjk F Q z v σ M η t hF hQ hQc hQs hσ hσ1 hv hη hη1 hM ht h1 h2
    have hM0 : 0 ≤ M := by linarith
    have hX : 0 ≤ σ ^ n * σ⁻¹ * M :=
      mul_nonneg (mul_nonneg (pow_nonneg hσ.le n) (inv_nonneg.2 hσ.le)) hM0
    have hY : 0 ≤ η ^ (-(2 : ℝ)) := Real.rpow_nonneg hη.le _
    have hmono : ∀ C₀ c₀ : ℝ, C₀ ≤ max C C' → min c c' ≤ c₀ →
        C₀ * σ ^ n * σ⁻¹ * M * t ^ (-c₀) * η ^ (-(2 : ℝ)) ≤
          max C C' * σ ^ n * σ⁻¹ * M * t ^ (-min c c') * η ^ (-(2 : ℝ)) := by
      intro C₀ c₀ hC₀ hc₀
      have ht1 : t ^ (-c₀) ≤ t ^ (-min c c') :=
        Real.rpow_le_rpow_of_exponent_le ht (by linarith)
      have ht0 : 0 ≤ t ^ (-c₀) := Real.rpow_nonneg (by linarith) _
      calc C₀ * σ ^ n * σ⁻¹ * M * t ^ (-c₀) * η ^ (-(2 : ℝ))
          = C₀ * ((σ ^ n * σ⁻¹ * M) * t ^ (-c₀) * η ^ (-(2 : ℝ))) := by ring
        _ ≤ max C C' * ((σ ^ n * σ⁻¹ * M) * t ^ (-c₀) * η ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_right hC₀ (mul_nonneg (mul_nonneg hX ht0) hY)
        _ ≤ max C C' * ((σ ^ n * σ⁻¹ * M) * t ^ (-min c c') * η ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht1 hX) hY)
            (le_max_of_le_left hC)
        _ = max C C' * σ ^ n * σ⁻¹ * M * t ^ (-min c c') * η ^ (-(2 : ℝ)) := by ring
    rcases Nat.lt_or_ge j (k + 1) with hjk' | hjk'
    · exact (h j hj1 (by omega) F Q z v σ M η t hF hQ hQc hQs hσ hσ1 hv hη hη1 hM ht h1 h2).trans
        (hmono C c (le_max_left _ _) (min_le_left _ _))
    · have hj : j = k + 1 := by omega
      subst hj
      exact (h' F Q z v σ M η t hF hQ hQc hQs hσ hσ1 hv hη hη1 hM ht h1 h2).trans
        (hmono C' c' (le_max_right _ _) (min_le_right _ _))

theorem norm_phase (t y : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * ((t * y : ℝ) : ℂ)))‖ = 1 := by
  rw [show -(2 * Real.pi * Complex.I * ((t * y : ℝ) : ℂ)) =
      ((-(2 * Real.pi * (t * y)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The bound on one ball. -/
theorem ball_bound {n : ℕ} (F : E n → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (w : E n → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (ρ : ℝ) (hsupp : ∀ x, w x ≠ 0 → ‖x‖ ≤ ρ) (Lw : ℝ≥0)
    (hLip : LipschitzWith Lw w) (W : ℝ) (hW : ∀ x, w x ≤ W)
    (k : ℕ) (hk : 1 ≤ k) (M : ℝ) (hM1 : 1 ≤ M)
    (hM : ∀ v : E n, ‖v‖ = 1 → ∀ j ≤ k + 1,
      ∀ x ∈ closedBall (0 : E n) (ρ + 2), ∀ x' ∈ closedBall (0 : E n) (ρ + 2),
        |dd j F v x| ≤ M ∧ |dd j F v x - dd j F v x'| ≤ M * ‖x - x'‖)
    (Cm cm : ℝ) (hCm : 0 ≤ Cm)
    (hcpb : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∀ (F : E n → ℝ) (Q : Set (E n)) (z v : E n) (σ M η t : ℝ),
        ContDiff ℝ (⊤ : ℕ∞) F → Convex ℝ Q → IsClosed Q → Q ⊆ closedBall z σ →
        0 < σ → σ ≤ 1 → ‖v‖ = 1 → 0 < η → η ≤ 1 → 1 ≤ M → 1 ≤ t →
        (∀ x ∈ Q, η ≤ |dd j F v x|) → (∀ x ∈ Q, |dd 2 F v x| ≤ M) →
        ‖∫ x in Q, Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ)))‖ ≤
          Cm * σ ^ n * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ)))
    (t τ r θ η σ : ℝ) (ht : 1 ≤ t) (hτ : 0 < τ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hθ : 0 < θ) (hMr : M * r ^ (k + 1) ≤ θ / 2)
    (hη : 0 < η) (hη1 : η ≤ 1) (hηθ : 4 * k * η ≤ θ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hση : 2 * M * σ ≤ η)
    (hosc : ∀ x₀ : E n, τ ≤ w x₀ → ∃ x ∈ closedBall x₀ r, θ ≤ |F x - F x₀|)
    (c : E n) :
    ‖∫ x in closedBall c σ,
        Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) * ((w x : ℝ) : ℂ)‖ ≤
      volume.real (closedBall c σ) * (τ + 2 * Lw * σ) +
        W * (Cm * σ ^ n * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ))) := by
  have hFc : Continuous F := hF.continuous
  have hwc : Continuous w := hLip.continuous
  have hW0 : 0 ≤ W := (hw0 0).trans (hW 0)
  have hM0 : 0 ≤ M := by linarith
  have hvol : 0 ≤ volume.real (closedBall c σ) := measureReal_nonneg
  have hbd0 : 0 ≤ Cm * σ ^ n * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ)) := by
    have := Real.rpow_nonneg (show (0:ℝ) ≤ t by linarith) (-cm)
    have := Real.rpow_nonneg hη.le (-(2:ℝ))
    have := pow_nonneg hσ.le n
    have := inv_nonneg.2 hσ.le
    positivity
  have hLw0 : (0 : ℝ) ≤ Lw := Lw.2
  have hnormE : ∀ x (y : ℝ), ‖Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) *
      ((y : ℝ) : ℂ)‖ = |y| := by
    intro x y
    rw [norm_mul, norm_phase, Complex.norm_real, Real.norm_eq_abs, one_mul]
  by_cases hA : ∃ x₀ ∈ closedBall c σ, τ ≤ w x₀
  · obtain ⟨x₀, hx₀Q, hτx₀⟩ := hA
    have hx₀ρ : ‖x₀‖ ≤ ρ := hsupp x₀ (by linarith)
    have hx₀c : ‖x₀ - c‖ ≤ σ := by rw [mem_closedBall, dist_eq_norm] at hx₀Q; exact hx₀Q
    have hx₀mem : x₀ ∈ closedBall (0 : E n) (ρ + 2) := by
      rw [mem_closedBall, dist_zero_right]; linarith
    obtain ⟨x, hxr, hθx⟩ := hosc x₀ hτx₀
    have hxne : x ≠ x₀ := by
      rintro rfl
      simp only [sub_self, abs_zero] at hθx
      linarith
    have hd : 0 < ‖x - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hxne)
    have hdr : ‖x - x₀‖ ≤ r := by rw [mem_closedBall, dist_eq_norm] at hxr; exact hxr
    set d := ‖x - x₀‖ with hd_def
    set v : E n := d⁻¹ • (x - x₀) with hv_def
    have hv : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hd, inv_mul_cancel₀ hd.ne']
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => F (x₀ + u • v)) :=
      hF.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have hgd : F (x₀ + d • v) = F x := by
      rw [hv_def, smul_smul, mul_inv_cancel₀ hd.ne', one_smul, add_sub_cancel]
    have hgM : ∀ u : ℝ, |u| ≤ r →
        |iteratedDeriv (k + 1) (fun u : ℝ => F (x₀ + u • v)) u| ≤ M := by
      intro u hu
      rw [iteratedDeriv_line]
      have hmem : x₀ + u • v ∈ closedBall (0 : E n) (ρ + 2) := by
        rw [mem_closedBall, dist_zero_right]
        calc ‖x₀ + u • v‖ ≤ ‖x₀‖ + ‖u • v‖ := norm_add_le _ _
          _ = ‖x₀‖ + |u| := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
          _ ≤ ρ + 2 := by linarith
      exact (hM v hv (k + 1) le_rfl _ hmem x₀ hx₀mem).1
    obtain ⟨j, hj1, hjk, hj⟩ := taylor_exists_large k hk (fun u : ℝ => F (x₀ + u • v)) hg
      M r θ d hr hr1 (by rw [abs_of_pos hd]; exact hdr) hgM
      (by show θ ≤ |F (x₀ + d • v) - F (x₀ + (0:ℝ) • v)|; rw [hgd, zero_smul, add_zero]; exact hθx)
    have hjx₀ : 2 * η ≤ |dd j F v x₀| := by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have : 2 * η ≤ (θ - M * r ^ (k + 1)) / k := by
        rw [le_div_iff₀ hk0]; nlinarith
      exact this.trans hj
    have hgood : ∀ x' ∈ closedBall c σ, η ≤ |dd j F v x'| := by
      intro x' hx'
      have hx'c : ‖x' - c‖ ≤ σ := by rw [mem_closedBall, dist_eq_norm] at hx'; exact hx'
      have h2σ : ‖x₀ - x'‖ ≤ 2 * σ := by
        calc ‖x₀ - x'‖ = ‖(x₀ - c) - (x' - c)‖ := by congr 1; abel
          _ ≤ ‖x₀ - c‖ + ‖x' - c‖ := norm_sub_le _ _
          _ ≤ 2 * σ := by linarith
      have hx'mem : x' ∈ closedBall (0 : E n) (ρ + 2) := by
        rw [mem_closedBall, dist_zero_right]
        calc ‖x'‖ = ‖x₀ - (x₀ - x')‖ := by congr 1; abel
          _ ≤ ‖x₀‖ + ‖x₀ - x'‖ := norm_sub_le _ _
          _ ≤ ρ + 2 := by linarith
      have hL := (hM v hv j (by omega) x₀ hx₀mem x' hx'mem).2
      have hL' : M * ‖x₀ - x'‖ ≤ M * (2 * σ) := mul_le_mul_of_nonneg_left h2σ hM0
      have := abs_sub_abs_le_abs_sub (dd j F v x₀) (dd j F v x')
      linarith
    have h2 : ∀ x' ∈ closedBall c σ, |dd 2 F v x'| ≤ M := by
      intro x' hx'
      have hx'c : ‖x' - c‖ ≤ σ := by rw [mem_closedBall, dist_eq_norm] at hx'; exact hx'
      have hx'mem : x' ∈ closedBall (0 : E n) (ρ + 2) := by
        rw [mem_closedBall, dist_zero_right]
        calc ‖x'‖ = ‖x₀ - (x₀ - x')‖ := by congr 1; abel
          _ ≤ ‖x₀‖ + ‖x₀ - x'‖ := norm_sub_le _ _
          _ ≤ ‖x₀‖ + (‖x₀ - c‖ + ‖x' - c‖) := by
              gcongr
              calc ‖x₀ - x'‖ = ‖(x₀ - c) - (x' - c)‖ := by congr 1; abel
                _ ≤ ‖x₀ - c‖ + ‖x' - c‖ := norm_sub_le _ _
          _ ≤ ρ + 2 := by linarith
      exact (hM v hv 2 (by omega) x' hx'mem x' hx'mem).1
    have hQ := hcpb j hj1 hjk F (closedBall c σ) c v σ M η t hF (convex_closedBall c σ)
      isClosed_closedBall subset_rfl hσ hσ1 hv hη hη1 hM1 ht hgood h2
    have hcE : Continuous fun x =>
        Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) := by fun_prop
    have hint1 : IntegrableOn (fun x =>
        Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) * ((w x₀ : ℝ) : ℂ))
        (closedBall c σ) :=
      (hcE.mul continuous_const).continuousOn.integrableOn_compact (isCompact_closedBall c σ)
    have hint2 : IntegrableOn (fun x =>
        Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) *
          ((w x - w x₀ : ℝ) : ℂ)) (closedBall c σ) :=
      (hcE.mul (Complex.continuous_ofReal.comp (hwc.sub continuous_const))).continuousOn.integrableOn_compact
        (isCompact_closedBall c σ)
    have hsplit : ∫ x in closedBall c σ,
        Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) * ((w x : ℝ) : ℂ) =
        (∫ x in closedBall c σ,
          Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ)))) * ((w x₀ : ℝ) : ℂ) +
        ∫ x in closedBall c σ, Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) *
          ((w x - w x₀ : ℝ) : ℂ) := by
      rw [← integral_mul_const, ← integral_add hint1 hint2]
      congr 1
      ext x
      push_cast
      ring
    have hb1 : ‖(∫ x in closedBall c σ,
          Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ)))) * ((w x₀ : ℝ) : ℂ)‖ ≤
        W * (Cm * σ ^ n * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ))) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x₀), mul_comm]
      exact mul_le_mul (hW x₀) hQ (norm_nonneg _) hW0
    have hb2 : ‖∫ x in closedBall c σ,
        Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) *
          ((w x - w x₀ : ℝ) : ℂ)‖ ≤ (Lw * (2 * σ)) * volume.real (closedBall c σ) := by
      apply norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top
      intro x hx
      rw [hnormE]
      have hxc : ‖x - c‖ ≤ σ := by rw [mem_closedBall, dist_eq_norm] at hx; exact hx
      have h1 := hLip.dist_le_mul x x₀
      rw [Real.dist_eq, dist_eq_norm] at h1
      have h2σ : ‖x - x₀‖ ≤ 2 * σ := by
        calc ‖x - x₀‖ = ‖(x - c) - (x₀ - c)‖ := by congr 1; abel
          _ ≤ ‖x - c‖ + ‖x₀ - c‖ := norm_sub_le _ _
          _ ≤ 2 * σ := by linarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2σ hLw0)
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have : 0 ≤ volume.real (closedBall c σ) * τ := mul_nonneg hvol hτ.le
    nlinarith
  · push Not at hA
    have hb : ‖∫ x in closedBall c σ,
        Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) * ((w x : ℝ) : ℂ)‖ ≤
        τ * volume.real (closedBall c σ) := by
      apply norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top
      intro x hx
      rw [hnormE, abs_of_nonneg (hw0 x)]
      exact (hA x hx).le
    have : 0 ≤ volume.real (closedBall c σ) * (2 * Lw * σ) := by positivity
    have : 0 ≤ W * (Cm * σ ^ n * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ))) := mul_nonneg hW0 hbd0
    nlinarith

/-! ## The integral over all of space -/
theorem vol_closedBall {n : ℕ} (c : E n) {s : ℝ} (hs : 0 ≤ s) :
    volume.real (closedBall c s) = s ^ n * volume.real (ball (0 : E n) 1) := by
  rw [Measure.addHaar_real_closedBall volume c hs, finrank_euclideanSpace_fin]

theorem vol_unit_pos (n : ℕ) : 0 < volume.real (ball (0 : E n) 1) :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

theorem fourier_bound {n : ℕ} (F : E n → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (w : E n → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (ρ : ℝ) (hρ : 0 ≤ ρ) (hsupp : ∀ x, w x ≠ 0 → ‖x‖ ≤ ρ) (Lw : ℝ≥0)
    (hLip : LipschitzWith Lw w) (W : ℝ) (hW : ∀ x, w x ≤ W)
    (k : ℕ) (hk : 1 ≤ k) (M : ℝ) (hM1 : 1 ≤ M)
    (hM : ∀ v : E n, ‖v‖ = 1 → ∀ j ≤ k + 1,
      ∀ x ∈ closedBall (0 : E n) (ρ + 2), ∀ x' ∈ closedBall (0 : E n) (ρ + 2),
        |dd j F v x| ≤ M ∧ |dd j F v x - dd j F v x'| ≤ M * ‖x - x'‖)
    (Cm cm : ℝ) (hCm : 0 ≤ Cm)
    (hcpb : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∀ (F : E n → ℝ) (Q : Set (E n)) (z v : E n) (σ M η t : ℝ),
        ContDiff ℝ (⊤ : ℕ∞) F → Convex ℝ Q → IsClosed Q → Q ⊆ closedBall z σ →
        0 < σ → σ ≤ 1 → ‖v‖ = 1 → 0 < η → η ≤ 1 → 1 ≤ M → 1 ≤ t →
        (∀ x ∈ Q, η ≤ |dd j F v x|) → (∀ x ∈ Q, |dd 2 F v x| ≤ M) →
        ‖∫ x in Q, Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ)))‖ ≤
          Cm * σ ^ n * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ)))
    (t τ r θ η σ : ℝ) (ht : 1 ≤ t) (hτ : 0 < τ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hθ : 0 < θ) (hMr : M * r ^ (k + 1) ≤ θ / 2)
    (hη : 0 < η) (hη1 : η ≤ 1) (hηθ : 4 * k * η ≤ θ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hση : 2 * M * σ ≤ η)
    (hosc : ∀ x₀ : E n, τ ≤ w x₀ → ∃ x ∈ closedBall x₀ r, θ ≤ |F x - F x₀|) :
    ‖∫ x, Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) * ((w x : ℝ) : ℂ)‖ ≤
      (ρ + 1) ^ n * (volume.real (ball (0 : E n) 1) * (τ + 2 * Lw * σ) +
        W * (Cm * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ)))) := by
  set G : E n → ℂ := fun x =>
    Complex.exp (-(2 * Real.pi * Complex.I * ((t * F x : ℝ) : ℂ))) * ((w x : ℝ) : ℂ) with hG_def
  have hFc : Continuous F := hF.continuous
  have hwc : Continuous w := hLip.continuous
  have hGc : Continuous G := by
    rw [hG_def]; fun_prop
  have hGzero : ∀ x, ρ < ‖x‖ → G x = 0 := by
    intro x hx
    have : w x = 0 := by
      by_contra h
      exact absurd (hsupp x h) (not_le.2 hx)
    simp [hG_def, this]
  have hGs : HasCompactSupport G := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : E n) ρ)
    intro x hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact hGzero x hx
  have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGs
  set K := volume.real (closedBall (0 : E n) σ) * (τ + 2 * Lw * σ) +
    W * (Cm * σ ^ n * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ))) with hK_def
  have hball : ∀ c : E n, ‖∫ x in closedBall c σ, G x‖ ≤
      (closedBall (0 : E n) (ρ + 1)).indicator (fun _ => K) c := by
    intro c
    by_cases hc : c ∈ closedBall (0 : E n) (ρ + 1)
    · rw [Set.indicator_of_mem hc, hK_def, vol_closedBall 0 hσ.le, ← vol_closedBall c hσ.le]
      exact ball_bound F hF w hw0 ρ hsupp Lw hLip W hW k hk M hM1 hM Cm cm hCm hcpb t τ r θ η σ
        ht hτ hr hr1 hθ hMr hη hη1 hηθ hσ hσ1 hση hosc c
    · rw [Set.indicator_of_notMem hc]
      rw [mem_closedBall, dist_zero_right, not_le] at hc
      rw [setIntegral_eq_zero_of_forall_eq_zero, norm_zero]
      intro x hx
      apply hGzero
      rw [mem_closedBall, dist_eq_norm] at hx
      have : ‖c‖ ≤ ‖x‖ + ‖x - c‖ := by
        calc ‖c‖ = ‖x - (x - c)‖ := by congr 1; abel
          _ ≤ ‖x‖ + ‖x - c‖ := norm_sub_le _ _
      linarith
  have h := avg_bound G hGi σ (ρ + 1) K hball
  rw [vol_closedBall 0 hσ.le, vol_closedBall 0 (by linarith), hK_def,
    vol_closedBall 0 hσ.le] at h
  set V := volume.real (ball (0 : E n) 1)
  have hV : 0 < V := vol_unit_pos n
  have hpos : 0 < σ ^ n * V := by positivity
  have e : (σ ^ n * V * (τ + 2 * Lw * σ) + W * (Cm * σ ^ n * σ⁻¹ * M * t ^ (-cm) *
      η ^ (-(2 : ℝ)))) * ((ρ + 1) ^ n * V) =
      (σ ^ n * V) * ((ρ + 1) ^ n * (V * (τ + 2 * Lw * σ) +
        W * (Cm * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ))))) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h hpos

/-! ## Parameters -/
/-- The radius. -/
noncomputable def rr (r₀ c₀ M : ℝ) (A' : ℕ) (τ : ℝ) : ℝ :=
  min (r₀ * τ) (min 1 (c₀ * τ ^ A' * (2 * M)⁻¹))

/-- The oscillation. -/
noncomputable def th (r₀ c₀ M : ℝ) (A' k : ℕ) (τ : ℝ) : ℝ :=
  c₀ * τ ^ A' * rr r₀ c₀ M A' τ ^ k

/-- The derivative lower bound. -/
noncomputable def et (r₀ c₀ M : ℝ) (A' k : ℕ) (τ : ℝ) : ℝ :=
  min 1 (th r₀ c₀ M A' k τ * (4 * (k : ℝ))⁻¹)

/-- The ball radius. -/
noncomputable def sg (r₀ c₀ M : ℝ) (A' k : ℕ) (τ : ℝ) : ℝ :=
  min τ (et r₀ c₀ M A' k τ * (2 * M)⁻¹)

end TaoBR.TaoDecay.PartD
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartD
variable {r₀ c₀ M : ℝ} (A' k : ℕ) (hr₀ : 0 < r₀) (hc₀ : 0 < c₀) (hM : 0 < M) (hk : 1 ≤ k)
include hr₀ hc₀ hM
theorem pb_rr : PB (rr r₀ c₀ M A') := by
  show PB (fun τ => min (r₀ * τ) (min 1 (c₀ * τ ^ A' * (2 * M)⁻¹)))
  exact ((PB.const hr₀).mul PB.id).minf ((PB.const one_pos).minf
    (((PB.const hc₀).mul (PB.id.pow A')).mul (PB.const (by positivity))))

theorem pb_th : PB (th r₀ c₀ M A' k) := by
  show PB (fun τ => c₀ * τ ^ A' * rr r₀ c₀ M A' τ ^ k)
  exact ((PB.const hc₀).mul (PB.id.pow A')).mul ((pb_rr A' hr₀ hc₀ hM).pow k)

end TaoBR.TaoDecay.PartD
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartD
variable {r₀ c₀ M : ℝ} (A' k : ℕ) (hr₀ : 0 < r₀) (hc₀ : 0 < c₀) (hM : 0 < M) (hk : 1 ≤ k)
include hr₀ hc₀ hM
include hk
theorem pb_et : PB (et r₀ c₀ M A' k) := by
  show PB (fun τ => min 1 (th r₀ c₀ M A' k τ * (4 * (k : ℝ))⁻¹))
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  exact (PB.const one_pos).minf ((pb_th A' k hr₀ hc₀ hM).mul (PB.const (by positivity)))

theorem pb_sg : PB (sg r₀ c₀ M A' k) := by
  show PB (fun τ => min τ (et r₀ c₀ M A' k τ * (2 * M)⁻¹))
  exact PB.id.minf ((pb_et A' k hr₀ hc₀ hM hk).mul (PB.const (by positivity)))

end TaoBR.TaoDecay.PartD
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartD
/-! ## Real-number estimates -/
theorem rpow_two_mul_le {t γ : ℝ} (ht : 1 ≤ t) (hγ : 0 ≤ γ) :
    t ^ (-γ) ≤ 2 ^ γ * (1 + t) ^ (-γ) := by
  have h1 : (1 + t) ^ (-γ) ≥ (2 * t) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
  have h2 : (2 : ℝ) ^ γ * (2 : ℝ) ^ (-γ) = 1 := by
    rw [Real.rpow_neg (by norm_num), mul_inv_cancel₀ (by positivity)]
  have h3 : 0 ≤ (2 : ℝ) ^ γ := by positivity
  calc t ^ (-γ) = ((2 : ℝ) ^ γ * (2 : ℝ) ^ (-γ)) * t ^ (-γ) := by rw [h2, one_mul]
    _ = (2 : ℝ) ^ γ * ((2 : ℝ) ^ (-γ) * t ^ (-γ)) := by ring
    _ ≤ 2 ^ γ * (1 + t) ^ (-γ) := mul_le_mul_of_nonneg_left h1 h3

theorem one_le_rpow_two_mul {t γ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) (hγ : 0 ≤ γ) :
    1 ≤ 2 ^ γ * (1 + t) ^ (-γ) := by
  have h1 : (1 + t) ^ (-γ) ≥ (2 : ℝ) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h2 : (2 : ℝ) ^ γ * (2 : ℝ) ^ (-γ) = 1 := by
    rw [Real.rpow_neg (by norm_num), mul_inv_cancel₀ (by positivity)]
  have h3 : 0 ≤ (2 : ℝ) ^ γ := by positivity
  calc (1 : ℝ) = (2 : ℝ) ^ γ * (2 : ℝ) ^ (-γ) := h2.symm
    _ ≤ 2 ^ γ * (1 + t) ^ (-γ) := mul_le_mul_of_nonneg_left h1 h3

/-- `σ⁻¹ η⁻² t^{-c} ≤ κ⁻³ t^{-γ}` when `σ, η ≥ κ τ^P`, `τ = t^{-γ}`, `γ = c/(6(P+1))`. -/
theorem final_rpow {t cm κ σ η : ℝ} {P : ℕ} (ht : 1 ≤ t) (hcm : 0 < cm) (hκ : 0 < κ)
    (hσ : κ * (t ^ (-(cm / (6 * (P + 1))))) ^ P ≤ σ)
    (hη : κ * (t ^ (-(cm / (6 * (P + 1))))) ^ P ≤ η) :
    σ⁻¹ * t ^ (-cm) * η ^ (-(2 : ℝ)) ≤ (κ ^ 3)⁻¹ * t ^ (-(cm / (6 * (P + 1)))) := by
  set γ := cm / (6 * (P + 1)) with hγ
  have ht0 : 0 < t := by linarith
  have hP : (0 : ℝ) < 6 * (P + 1) := by positivity
  have hγ0 : 0 < γ := div_pos hcm hP
  set τ := t ^ (-γ) with hτ
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos ht0 _
  have hb0 : 0 < κ * τ ^ P := by positivity
  have hσ0 : 0 < σ := hb0.trans_le hσ
  have hη0 : 0 < η := hb0.trans_le hη
  have h1 : σ⁻¹ ≤ (κ * τ ^ P)⁻¹ := inv_anti₀ hb0 hσ
  have h2 : η ^ (-(2 : ℝ)) ≤ ((κ * τ ^ P) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hη0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hb0.le hη 2)
  have h3 : σ⁻¹ * η ^ (-(2 : ℝ)) ≤ (κ ^ 3)⁻¹ * (τ ^ (3 * P))⁻¹ := by
    calc σ⁻¹ * η ^ (-(2 : ℝ)) ≤ (κ * τ ^ P)⁻¹ * ((κ * τ ^ P) ^ 2)⁻¹ :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (κ ^ 3)⁻¹ * (τ ^ (3 * P))⁻¹ := by
          rw [← mul_inv, ← mul_inv, pow_mul]; ring
  have h4 : (τ ^ (3 * P))⁻¹ * t ^ (-cm) ≤ τ := by
    rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le, ← Real.rpow_neg ht0.le,
      ← Real.rpow_add ht0]
    apply Real.rpow_le_rpow_of_exponent_le ht
    have e : γ * (6 * (P + 1)) = cm := by rw [hγ]; field_simp
    push_cast
    nlinarith
  have hi : 0 ≤ (κ ^ 3)⁻¹ := by positivity
  calc σ⁻¹ * t ^ (-cm) * η ^ (-(2 : ℝ)) = (σ⁻¹ * η ^ (-(2 : ℝ))) * t ^ (-cm) := by ring
    _ ≤ ((κ ^ 3)⁻¹ * (τ ^ (3 * P))⁻¹) * t ^ (-cm) :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg ht0.le _)
    _ = (κ ^ 3)⁻¹ * ((τ ^ (3 * P))⁻¹ * t ^ (-cm)) := by ring
    _ ≤ (κ ^ 3)⁻¹ * τ := mul_le_mul_of_nonneg_left h4 hi

end TaoBR.TaoDecay.PartD
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartD
variable {r₀ c₀ M : ℝ} {A' k : ℕ} (hr₀ : 0 < r₀) (hc₀ : 0 < c₀) (hM : 0 < M) (hk : 1 ≤ k)
  {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
include hr₀ hc₀ hM hτ hτ1
theorem rr_pos : 0 < rr r₀ c₀ M A' τ := (pb_rr A' hr₀ hc₀ hM).pos hτ hτ1

theorem th_pos : 0 < th r₀ c₀ M A' k τ := (pb_th A' k hr₀ hc₀ hM).pos hτ hτ1

theorem hMr_ok : M * rr r₀ c₀ M A' τ ^ (k + 1) ≤ th r₀ c₀ M A' k τ / 2 := by
  have hr := rr_pos (A' := A') hr₀ hc₀ hM hτ hτ1
  have h3 : rr r₀ c₀ M A' τ ≤ c₀ * τ ^ A' * (2 * M)⁻¹ :=
    (min_le_right _ _).trans (min_le_right _ _)
  have h : M * rr r₀ c₀ M A' τ ≤ c₀ * τ ^ A' / 2 := by
    calc M * rr r₀ c₀ M A' τ ≤ M * (c₀ * τ ^ A' * (2 * M)⁻¹) :=
          mul_le_mul_of_nonneg_left h3 hM.le
      _ = c₀ * τ ^ A' / 2 := by field_simp
  calc M * rr r₀ c₀ M A' τ ^ (k + 1) = (M * rr r₀ c₀ M A' τ) * rr r₀ c₀ M A' τ ^ k := by ring
    _ ≤ (c₀ * τ ^ A' / 2) * rr r₀ c₀ M A' τ ^ k :=
        mul_le_mul_of_nonneg_right h (pow_nonneg hr.le k)
    _ = th r₀ c₀ M A' k τ / 2 := by unfold th; ring

theorem th_le {A B : ℝ} (hA : A ≤ A') (hB : B ≤ k) :
    th r₀ c₀ M A' k τ ≤ c₀ * τ ^ A * rr r₀ c₀ M A' τ ^ B := by
  have hr := rr_pos (A' := A') hr₀ hc₀ hM hτ hτ1
  have hr1 : rr r₀ c₀ M A' τ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have h1 : τ ^ A' ≤ τ ^ A := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge hτ hτ1 hA
  have h2 : rr r₀ c₀ M A' τ ^ k ≤ rr r₀ c₀ M A' τ ^ B := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge hr hr1 hB
  unfold th
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc₀.le) h2 (pow_nonneg hr.le k)
    (mul_nonneg hc₀.le (Real.rpow_nonneg hτ.le _))

end TaoBR.TaoDecay.PartD
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartD
variable {r₀ c₀ M : ℝ} {A' k : ℕ} (hr₀ : 0 < r₀) (hc₀ : 0 < c₀) (hM : 0 < M) (hk : 1 ≤ k)
  {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
include hr₀ hc₀ hM hτ hτ1
include hk
theorem et_pos : 0 < et r₀ c₀ M A' k τ := (pb_et A' k hr₀ hc₀ hM hk).pos hτ hτ1

theorem sg_pos : 0 < sg r₀ c₀ M A' k τ := (pb_sg A' k hr₀ hc₀ hM hk).pos hτ hτ1

theorem hηθ_ok : 4 * k * et r₀ c₀ M A' k τ ≤ th r₀ c₀ M A' k τ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h : et r₀ c₀ M A' k τ ≤ th r₀ c₀ M A' k τ * (4 * (k : ℝ))⁻¹ := min_le_right _ _
  calc 4 * k * et r₀ c₀ M A' k τ ≤ 4 * k * (th r₀ c₀ M A' k τ * (4 * (k : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = th r₀ c₀ M A' k τ := by field_simp

theorem hση_ok : 2 * M * sg r₀ c₀ M A' k τ ≤ et r₀ c₀ M A' k τ := by
  have h : sg r₀ c₀ M A' k τ ≤ et r₀ c₀ M A' k τ * (2 * M)⁻¹ := min_le_right _ _
  calc 2 * M * sg r₀ c₀ M A' k τ ≤ 2 * M * (et r₀ c₀ M A' k τ * (2 * M)⁻¹) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = et r₀ c₀ M A' k τ := by field_simp

end TaoBR.TaoDecay.PartD
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartD
theorem norm_phase' (y : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * (y : ℂ)))‖ = 1 := by
  simpa using norm_phase 1 y

/-- Power decay of the Fourier transform of `Φ_* (w dx)` from the oscillation bound. -/
theorem decay_of_knapp {n m : ℕ} (Φ : E n → E m) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (w : E n → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (ρ₀ : ℝ) (hsupp : ∀ x, w x ≠ 0 → ‖x‖ ≤ ρ₀) (Lw : ℝ≥0)
    (hLip : LipschitzWith Lw w)
    (hK : ∃ A B c₀ r₀ : ℝ, 0 < c₀ ∧ 0 < r₀ ∧ 0 ≤ A ∧ 0 ≤ B ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x₀ : E n, τ ≤ w x₀ → ∀ e : E m, ‖e‖ = 1 →
        ∀ r : ℝ, 0 < r → r ≤ r₀ * τ →
          ∃ x ∈ closedBall x₀ r, c₀ * τ ^ A * r ^ B ≤ |inner ℝ e (Φ x) - inner ℝ e (Φ x₀)|) :
    ∃ C c : ℝ, 0 < c ∧ ∀ ξ : E m,
      ‖∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ ξ (Φ x) : ℝ))) * ((w x : ℝ) : ℂ)‖ ≤
        C * (1 + ‖ξ‖) ^ (-c) := by
  obtain ⟨A, B, c₀, r₀, hc₀, hr₀, hA, hB, hK⟩ := hK
  set ρ := max ρ₀ 0 with hρ_def
  have hρ : 0 ≤ ρ := le_max_right _ _
  have hsupp' : ∀ x, w x ≠ 0 → ‖x‖ ≤ ρ := fun x h => (hsupp x h).trans (le_max_left _ _)
  set k := ⌊B⌋₊ + 1 with hk_def
  have hk : 1 ≤ k := by omega
  have hBk : B ≤ (k : ℝ) := by
    rw [hk_def]; push_cast; exact (Nat.lt_floor_add_one B).le
  set A' := ⌈A⌉₊ with hA'_def
  have hAA : A ≤ (A' : ℝ) := Nat.le_ceil A
  obtain ⟨M, hM1, hM⟩ := dd_bounds Φ hΦ (ρ + 2) (k + 1)
  have hM0 : 0 < M := by linarith
  obtain ⟨Cm, cm, hCm, hcm, hcpb⟩ := cpb_uniform n k
  have hLw0 : (0 : ℝ) ≤ Lw := Lw.2
  set W := w 0 + Lw * ρ with hW_def
  have hW0 : 0 ≤ W := add_nonneg (hw0 0) (mul_nonneg hLw0 hρ)
  have hW : ∀ x, w x ≤ W := by
    intro x
    by_cases h : w x = 0
    · rw [h]; exact hW0
    · have h1 := hsupp' x h
      have h2 := hLip.dist_le_mul x 0
      rw [Real.dist_eq, dist_zero_right] at h2
      have h3 : (Lw : ℝ) * ‖x‖ ≤ Lw * ρ := mul_le_mul_of_nonneg_left h1 hLw0
      have := le_abs_self (w x - w 0)
      linarith
  obtain ⟨κ, hκ, P, hP⟩ := (pb_sg A' k hr₀ hc₀ hM0 hk).minf (pb_et A' k hr₀ hc₀ hM0 hk)
  set V := volume.real (ball (0 : E n) 1) with hV_def
  have hV : 0 < V := vol_unit_pos n
  set γ := cm / (6 * ((P : ℝ) + 1)) with hγ_def
  have hγ : 0 < γ := by positivity
  set T0 := W * volume.real (closedBall (0 : E n) ρ) with hT0_def
  set D := (ρ + 1) ^ n * V * (1 + 2 * Lw) with hD_def
  set D' := (ρ + 1) ^ n * W * Cm * M with hD'_def
  have hT0 : 0 ≤ T0 := mul_nonneg hW0 measureReal_nonneg
  have hD : 0 ≤ D := by positivity
  have hD' : 0 ≤ D' * (κ ^ 3)⁻¹ := by
    have : 0 ≤ D' := mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hW0) hCm) hM0.le
    positivity
  refine ⟨2 ^ γ * (T0 + D + D' * (κ ^ 3)⁻¹), γ, hγ, fun ξ => ?_⟩
  have hfac : 0 ≤ (2 : ℝ) ^ γ * (1 + ‖ξ‖) ^ (-γ) := by positivity
  by_cases hξ : ‖ξ‖ ≤ 1
  · have hb : ‖∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ ξ (Φ x) : ℝ))) *
        ((w x : ℝ) : ℂ)‖ ≤ T0 := by
      have hint : Integrable ((closedBall (0 : E n) ρ).indicator (fun _ => W)) :=
        (integrableOn_const (C := W) (s := closedBall (0 : E n) ρ)
          measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
      have h := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall (fun x => by
        show ‖Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ ξ (Φ x) : ℝ))) *
          ((w x : ℝ) : ℂ)‖ ≤ (closedBall (0 : E n) ρ).indicator (fun _ => W) x
        rw [norm_mul, norm_phase', one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw0 x)]
        by_cases hx : x ∈ closedBall (0 : E n) ρ
        · rw [Set.indicator_of_mem hx]; exact hW x
        · rw [Set.indicator_of_notMem hx]
          rw [mem_closedBall, dist_zero_right, not_le] at hx
          have : w x = 0 := by
            by_contra h
            exact absurd (hsupp' x h) (not_le.2 hx)
          rw [this]))
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul] at h
      rw [hT0_def, mul_comm W]; exact h
    have h1 := one_le_rpow_two_mul (norm_nonneg ξ) hξ hγ.le
    calc _ ≤ T0 := hb
      _ ≤ (T0 + D + D' * (κ ^ 3)⁻¹) * 1 := by linarith
      _ ≤ (T0 + D + D' * (κ ^ 3)⁻¹) * (2 ^ γ * (1 + ‖ξ‖) ^ (-γ)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 2 ^ γ * (T0 + D + D' * (κ ^ 3)⁻¹) * (1 + ‖ξ‖) ^ (-γ) := by ring
  · push Not at hξ
    set t := ‖ξ‖ with ht_def
    have ht : 1 ≤ t := hξ.le
    have ht0 : 0 < t := by linarith
    set e : E m := t⁻¹ • ξ with he_def
    have he : ‖e‖ = 1 := by
      rw [he_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0, inv_mul_cancel₀ ht0.ne']
    have hphase : (fun x => Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ ξ (Φ x) : ℝ))) *
        ((w x : ℝ) : ℂ)) = fun x =>
        Complex.exp (-(2 * Real.pi * Complex.I * ((t * inner ℝ e (Φ x) : ℝ) : ℂ))) *
          ((w x : ℝ) : ℂ) := by
      ext x
      rw [he_def, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul]
    rw [hphase]
    set τ := t ^ (-γ) with hτ_def
    have hτ0 : 0 < τ := Real.rpow_pos_of_pos ht0 _
    have hτ1 : τ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
    have hr := rr_pos (A' := A') hr₀ hc₀ hM0 hτ0 hτ1
    have hr1 : rr r₀ c₀ M A' τ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hrτ : rr r₀ c₀ M A' τ ≤ r₀ * τ := min_le_left _ _
    have hθ := th_pos (A' := A') (k := k) hr₀ hc₀ hM0 hτ0 hτ1
    have hMr := hMr_ok (A' := A') (k := k) hr₀ hc₀ hM0 hτ0 hτ1
    have hθK := th_le (A' := A') (k := k) hr₀ hc₀ hM0 hτ0 hτ1 hAA hBk
    have hη := et_pos (A' := A') hr₀ hc₀ hM0 hk hτ0 hτ1
    have hη1 : et r₀ c₀ M A' k τ ≤ 1 := min_le_left _ _
    have hηθ := hηθ_ok (A' := A') hr₀ hc₀ hM0 hk hτ0 hτ1
    have hσ := sg_pos (A' := A') hr₀ hc₀ hM0 hk hτ0 hτ1
    have hστ : sg r₀ c₀ M A' k τ ≤ τ := min_le_left _ _
    have hσ1 : sg r₀ c₀ M A' k τ ≤ 1 := hστ.trans hτ1
    have hση := hση_ok (A' := A') hr₀ hc₀ hM0 hk hτ0 hτ1
    have hosc : ∀ x₀ : E n, τ ≤ w x₀ → ∃ x ∈ closedBall x₀ (rr r₀ c₀ M A' τ),
        th r₀ c₀ M A' k τ ≤ |inner ℝ e (Φ x) - inner ℝ e (Φ x₀)| := by
      intro x₀ hx₀
      obtain ⟨x, hx, hx'⟩ := hK τ hτ0 hτ1 x₀ hx₀ e he _ hr hrτ
      exact ⟨x, hx, hθK.trans hx'⟩
    have hFB := fourier_bound (fun z => inner ℝ e (Φ z)) (contDiff_const.inner ℝ hΦ) w hw0 ρ hρ
      hsupp' Lw hLip W hW k hk M hM1 (hM e he) Cm cm hCm hcpb t τ (rr r₀ c₀ M A' τ)
      (th r₀ c₀ M A' k τ) (et r₀ c₀ M A' k τ) (sg r₀ c₀ M A' k τ) ht hτ0 hr hr1 hθ hMr hη hη1
      hηθ hσ hσ1 hση hosc
    have hPτ := hP τ hτ0 hτ1
    have hfr := final_rpow (P := P) ht hcm hκ ((hPτ.trans (min_le_left _ _)))
      ((hPτ.trans (min_le_right _ _)))
    -- `hfr : σ⁻¹ * t^(-cm) * η^(-2) ≤ (κ^3)⁻¹ * τ`
    set σ := sg r₀ c₀ M A' k τ
    set η := et r₀ c₀ M A' k τ
    have step1 : V * (τ + 2 * Lw * σ) ≤ V * (1 + 2 * Lw) * τ := by
      have : (Lw : ℝ) * σ ≤ Lw * τ := mul_le_mul_of_nonneg_left hστ hLw0
      calc V * (τ + 2 * Lw * σ) ≤ V * (τ + 2 * (Lw * τ)) :=
            mul_le_mul_of_nonneg_left (by linarith) hV.le
        _ = V * (1 + 2 * Lw) * τ := by ring
    have step2 : W * (Cm * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ))) ≤
        W * Cm * M * ((κ ^ 3)⁻¹ * τ) := by
      calc W * (Cm * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ))) =
            (W * Cm * M) * (σ⁻¹ * t ^ (-cm) * η ^ (-(2 : ℝ))) := by ring
        _ ≤ (W * Cm * M) * ((κ ^ 3)⁻¹ * τ) :=
            mul_le_mul_of_nonneg_left hfr (mul_nonneg (mul_nonneg hW0 hCm) hM0.le)
    have hX : 0 ≤ (ρ + 1) ^ n := by positivity
    have h2 := rpow_two_mul_le ht hγ.le
    calc _ ≤ (ρ + 1) ^ n * (V * (τ + 2 * Lw * σ) +
          W * (Cm * σ⁻¹ * M * t ^ (-cm) * η ^ (-(2 : ℝ)))) := hFB
      _ ≤ (ρ + 1) ^ n * (V * (1 + 2 * Lw) * τ + W * Cm * M * ((κ ^ 3)⁻¹ * τ)) :=
          mul_le_mul_of_nonneg_left (add_le_add step1 step2) hX
      _ = (D + D' * (κ ^ 3)⁻¹) * τ := by rw [hD_def, hD'_def]; ring
      _ ≤ (T0 + D + D' * (κ ^ 3)⁻¹) * τ := mul_le_mul_of_nonneg_right (by linarith) hτ0.le
      _ ≤ (T0 + D + D' * (κ ^ 3)⁻¹) * (2 ^ γ * (1 + t) ^ (-γ)) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = 2 ^ γ * (T0 + D + D' * (κ ^ 3)⁻¹) * (1 + t) ^ (-γ) := by ring

end TaoBR.TaoDecay.PartD
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
alias decay_of_knapp := TaoBR.TaoDecay.PartD.decay_of_knapp

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartK
/-! ## Operator norm -/
lemma eLpNorm_le_opNorm {n m : ℕ} {p : ℝ≥0∞} {T : (E m → ℂ) → (E n → ℂ)} {D : ℝ≥0∞}
    (hT : opNorm p p T ≤ D) (hD : D ≠ ⊤) {f : E m → ℂ} (hf : MemLp f p volume) :
    eLpNorm (T f) p volume ≤ D * eLpNorm f p volume := by
  have hlt : sInf {C : ℝ≥0∞ | ∀ f : E m → ℂ, MemLp f p volume →
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume} < ⊤ :=
    lt_of_le_of_lt hT (lt_top_iff_ne_top.2 hD)
  obtain ⟨C₁, hC₁, -⟩ := sInf_lt_iff.1 hlt
  by_cases hz : eLpNorm f p volume = 0
  · have := hC₁ f hf; rw [hz, mul_zero] at this; rw [hz, mul_zero]; exact this
  have hft : eLpNorm f p volume ≠ ⊤ := hf.eLpNorm_ne_top
  have : eLpNorm (T f) p volume / eLpNorm f p volume ≤ opNorm p p T := by
    apply le_sInf
    intro C hC
    exact (ENNReal.div_le_iff hz hft).2 (hC f hf)
  exact (ENNReal.div_le_iff hz hft).1 (this.trans hT)

/-! ## Elementary bounds -/
lemma norm_exp_sub_one_le (t : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) - 1‖ ≤ 2 * Real.pi * |t| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(2 * Real.pi * t))
  have e : -(2 * Real.pi * Complex.I * (t : ℂ)) = Complex.I * ((-(2 * Real.pi * t) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

lemma pointwise_bound (t : ℝ) (z c : ℂ) (Ψ δ : ℝ) (hz : ‖z‖ ≤ Ψ) (hzc : ‖z - c‖ ≤ δ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) * z - c‖ ≤
      2 * Real.pi * |t| * Ψ + δ := by
  have e : Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) * z - c =
      (Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) - 1) * z + (z - c) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hzc)
  rw [norm_mul]
  exact mul_le_mul (norm_exp_sub_one_le t) hz (norm_nonneg _) (by positivity)

lemma inner_Phi {n m : ℕ} (φ : E n → E m → ℝ) (y₀ e : E m) (x : E n) :
    inner ℝ e (Phi φ y₀ x) = fderiv ℝ (φ x) y₀ e := by
  simp only [Phi, gradient]
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

/-! ## Second-order Taylor bound (first-order mean value theorem) -/
lemma taylor_bound {n m : ℕ} (φ : E n → E m → ℝ) (hd : ∀ x, Differentiable ℝ (φ x))
    (y₀ : E m) (L : ℝ) (x x₀ : E n) (y : E m)
    (hL : ∀ z ∈ closedBall y₀ ‖y - y₀‖,
      ‖fderiv ℝ (φ x) z - fderiv ℝ (φ x) y₀‖ ≤ L * ‖z - y₀‖ ∧
       ‖fderiv ℝ (φ x₀) z - fderiv ℝ (φ x₀) y₀‖ ≤ L * ‖z - y₀‖) (hL0 : 0 ≤ L) :
    |φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀ - (fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀) (y - y₀)| ≤
      2 * L * ‖y - y₀‖ ^ 2 := by
  set D := fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀ with hD
  set G : E m → ℝ := fun z => φ x z - φ x₀ z - D z with hG
  have hGd : ∀ z ∈ closedBall y₀ ‖y - y₀‖, HasFDerivWithinAt G
      (fderiv ℝ (φ x) z - fderiv ℝ (φ x₀) z - D) (closedBall y₀ ‖y - y₀‖) z := by
    intro z _
    exact ((((hd x) z).hasFDerivAt.sub ((hd x₀) z).hasFDerivAt).sub D.hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ closedBall y₀ ‖y - y₀‖,
      ‖fderiv ℝ (φ x) z - fderiv ℝ (φ x₀) z - D‖ ≤ 2 * L * ‖y - y₀‖ := by
    intro z hz
    obtain ⟨h1, h2⟩ := hL z hz
    have hz' : ‖z - y₀‖ ≤ ‖y - y₀‖ := by rwa [mem_closedBall, dist_eq_norm] at hz
    have e : fderiv ℝ (φ x) z - fderiv ℝ (φ x₀) z - D =
        (fderiv ℝ (φ x) z - fderiv ℝ (φ x) y₀) - (fderiv ℝ (φ x₀) z - fderiv ℝ (φ x₀) y₀) := by
      rw [hD]; abel
    rw [e]
    calc _ ≤ ‖fderiv ℝ (φ x) z - fderiv ℝ (φ x) y₀‖ +
          ‖fderiv ℝ (φ x₀) z - fderiv ℝ (φ x₀) y₀‖ := norm_sub_le _ _
      _ ≤ L * ‖z - y₀‖ + L * ‖z - y₀‖ := add_le_add h1 h2
      _ ≤ 2 * L * ‖y - y₀‖ := by nlinarith
  have key := (convex_closedBall y₀ ‖y - y₀‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hGd hb
    (mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm])
  have heq : G y - G y₀ = φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀ - D (y - y₀) := by
    simp only [hG, map_sub]; ring
  rw [heq, Real.norm_eq_abs] at key
  calc _ ≤ 2 * L * ‖y - y₀‖ * ‖y - y₀‖ := key
    _ = _ := by ring

/-! ## The Knapp set -/
/-- The union of `N` disjoint balls of radius `β` centred along `e`. -/
def knappSet {m : ℕ} (y₀ e : E m) (β : ℝ) (N : ℕ) : Set (E m) :=
  ⋃ k ∈ Finset.range N, ball (y₀ + (2 * (k : ℝ) * β) • e) β

lemma knappSet_mem {m : ℕ} (y₀ e : E m) (β : ℝ) (N : ℕ) (y : E m)
    (hy : y ∈ knappSet y₀ e β N) :
    ∃ k : ℕ, k < N ∧ ‖y - y₀ - (2 * (k : ℝ) * β) • e‖ < β := by
  simp only [knappSet, Set.mem_iUnion, Finset.mem_range, mem_ball, dist_eq_norm,
    exists_prop] at hy
  obtain ⟨k, hk, h⟩ := hy
  exact ⟨k, hk, by rw [sub_sub]; exact h⟩

lemma knappSet_open {m : ℕ} (y₀ e : E m) (β : ℝ) (N : ℕ) : IsOpen (knappSet y₀ e β N) :=
  isOpen_biUnion fun _ _ => isOpen_ball

lemma knappSet_volume {m : ℕ} (y₀ e : E m) (he : ‖e‖ = 1) (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    volume (knappSet y₀ e β N) = N * (ENNReal.ofReal (β ^ m) * volume (ball (0 : E m) 1)) := by
  rw [knappSet, measure_biUnion_finset]
  · simp only [Measure.addHaar_ball_of_pos volume _ hβ, finrank_euclideanSpace_fin,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro i _ j _ hij
    simp only [Function.onFun]
    apply ball_disjoint_ball
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, he, mul_one,
      Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
    have e2 : 2 * (i : ℝ) * β - 2 * j * β = (2 * β) * ((i : ℝ) - j) := by ring
    rw [e2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * β)]
    nlinarith
  · intro k _; exact measurableSet_ball

/-! ## From the pointwise lower bound to a real inequality -/
lemma chain {n m : ℕ} (p : ℝ≥0∞) (hp0 : p ≠ 0) (T : (E m → ℂ) → (E n → ℂ)) (D : ℝ)
    (hT : opNorm p p T ≤ ENNReal.ofReal D) (Y : Set (E m)) (hYm : MeasurableSet Y)
    (hYfin : volume Y ≠ ⊤) (hYpos : volume Y ≠ 0) (g : E m → ℂ) (hg : Continuous g)
    (hg1 : ∀ y, ‖g y‖ = 1) (x₀ : E n) (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hlow : ∀ x ∈ closedBall x₀ r, c ≤ ‖T (Y.indicator g) x‖) :
    c * (volume.real (closedBall x₀ r)) ^ p⁻¹.toReal ≤ D * (volume.real Y) ^ p⁻¹.toReal := by
  have hnorm : ∀ y, ‖Y.indicator g y‖ = ‖Y.indicator (fun _ => (1 : ℝ)) y‖ := by
    intro y; by_cases hy : y ∈ Y <;> simp [hy, hg1]
  have hf : MemLp (Y.indicator g) p volume :=
    (memLp_indicator_const p hYm (1 : ℝ) (Or.inr hYfin)).of_le
      (hg.aestronglyMeasurable.indicator hYm) (ae_of_all _ fun y => (hnorm y).le)
  have hfn : eLpNorm (Y.indicator g) p volume = ‖(1 : ℝ)‖ₑ * volume Y ^ (1 / p.toReal) := by
    rw [eLpNorm_congr_norm_ae (ae_of_all _ hnorm), eLpNorm_indicator_const' hYm hYpos hp0]
  have hup := eLpNorm_le_opNorm hT ENNReal.ofReal_ne_top hf
  have hBpos : volume (closedBall x₀ r) ≠ 0 := (measure_closedBall_pos _ _ hr).ne'
  have hBfin : volume (closedBall x₀ r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hlowE : eLpNorm ((closedBall x₀ r).indicator (fun _ => c)) p volume ≤
      eLpNorm (T (Y.indicator g)) p volume := by
    apply eLpNorm_mono
    intro x
    by_cases hx : x ∈ closedBall x₀ r
    · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_pos hc]
      exact hlow x hx
    · simp [Set.indicator_of_notMem hx]
  rw [eLpNorm_indicator_const' measurableSet_closedBall hBpos hp0] at hlowE
  rw [hfn] at hup
  have h := hlowE.trans hup
  have hs : 1 / p.toReal = p⁻¹.toReal := by rw [one_div, ENNReal.toReal_inv]
  rw [hs, Real.enorm_of_nonneg hc.le, enorm_one, one_mul,
    ← ENNReal.ofReal_toReal hBfin, ← ENNReal.ofReal_toReal hYfin,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul hc.le] at h
  rcases le_or_gt D 0 with hD | hD
  · rw [ENNReal.ofReal_of_nonpos hD, zero_mul] at h
    have : 0 < c * (volume (closedBall x₀ r)).toReal ^ p⁻¹.toReal := by
      apply mul_pos hc
      apply Real.rpow_pos_of_pos
      exact ENNReal.toReal_pos hBpos hBfin
    exact absurd (ENNReal.ofReal_eq_zero.1 (le_antisymm h bot_le)) (not_le.2 this)
  rw [← ENNReal.ofReal_mul hD.le, ENNReal.ofReal_le_ofReal_iff'] at h
  rcases h with h | h
  · simpa [measureReal_def] using h
  · exfalso
    have : 0 < c * (volume (closedBall x₀ r)).toReal ^ p⁻¹.toReal := by
      apply mul_pos hc
      apply Real.rpow_pos_of_pos
      exact ENNReal.toReal_pos hBpos hBfin
    linarith

/-! ## The pointwise lower bound for `S_R f` -/
lemma knappSet_norm_le {m : ℕ} (y₀ e : E m) (he : ‖e‖ = 1) (β a H : ℝ) (N : ℕ) (hβ0 : 0 < β)
    (hβle : β ≤ a * H) (hk : ∀ k : ℕ, k < N → 2 * (k : ℝ) * β ≤ a * H) (y : E m)
    (hy : y ∈ knappSet y₀ e β N) : ‖y - y₀‖ ≤ 2 * a * H := by
  obtain ⟨k, hk', hw⟩ := knappSet_mem y₀ e β N y hy
  have hk2 := hk k hk'
  have hnn : 0 ≤ 2 * (k : ℝ) * β := by positivity
  calc ‖y - y₀‖ = ‖(2 * (k : ℝ) * β) • e + (y - y₀ - (2 * (k : ℝ) * β) • e)‖ := by
        congr 1; abel
    _ ≤ ‖(2 * (k : ℝ) * β) • e‖ + ‖y - y₀ - (2 * (k : ℝ) * β) • e‖ := norm_add_le _ _
    _ ≤ a * H + a * H := by
        rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hnn]
        exact add_le_add hk2 (hw.le.trans hβle)
    _ = 2 * a * H := by ring

lemma theta_bound {n m : ℕ} (φ : E n → E m → ℝ) (hd : ∀ x, Differentiable ℝ (φ x))
    (y₀ e : E m) (he : ‖e‖ = 1) (x₀ x : E n) (L₂ H a β : ℝ) (N : ℕ)
    (hL₂0 : 0 ≤ L₂)
    (hL₂ : ∀ y ∈ closedBall y₀ 1, ‖fderiv ℝ (φ x) y - fderiv ℝ (φ x) y₀‖ ≤ L₂ * ‖y - y₀‖ ∧
      ‖fderiv ℝ (φ x₀) y - fderiv ℝ (φ x₀) y₀‖ ≤ L₂ * ‖y - y₀‖)
    (hDw : ∀ w : E m, |(fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀) w| ≤ L₂ * ‖w‖)
    (hDe : |(fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀) e| ≤ H)
    (hH : 0 < H) (hH1 : H ≤ 1) (ha : 0 < a) (ha8 : 8 * L₂ * a ≤ 1) (ha2 : a ≤ 1 / 2)
    (hβ0 : 0 < β) (hβL : L₂ * β ≤ a * H ^ 2) (hβle : β ≤ a * H)
    (hk : ∀ k : ℕ, k < N → 2 * (k : ℝ) * β ≤ a * H) (y : E m) (hy : y ∈ knappSet y₀ e β N) :
    |(H ^ 2)⁻¹ * (φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀)| ≤ 3 * a := by
  obtain ⟨k, hk', hw⟩ := knappSet_mem y₀ e β N y hy
  have hyy := knappSet_norm_le y₀ e he β a H N hβ0 hβle hk y hy
  have h2aH : 2 * a * H ≤ 1 := by nlinarith
  have hT := taylor_bound φ hd y₀ L₂ x x₀ y
    (fun z hz => hL₂ z (closedBall_subset_closedBall (hyy.trans h2aH) hz)) hL₂0
  set D := fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀ with hD
  set t : ℝ := 2 * (k : ℝ) * β with ht
  set w := y - y₀ - t • e with hwdef
  have hsplit : D (y - y₀) = t * D e + D w := by
    have : y - y₀ = t • e + w := by rw [hwdef]; abel
    rw [this, map_add, map_smul, smul_eq_mul]
  have ht0 : 0 ≤ t := by positivity
  have h1 : 2 * L₂ * ‖y - y₀‖ ^ 2 ≤ a * H ^ 2 := by
    have : ‖y - y₀‖ ^ 2 ≤ (2 * a * H) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyy 2
    have h8 : 8 * L₂ * a * (a * H ^ 2) ≤ 1 * (a * H ^ 2) :=
      mul_le_mul_of_nonneg_right ha8 (by positivity)
    nlinarith
  have h2 : |t * D e| ≤ a * H * H := by
    rw [abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul (hk k hk') hDe (abs_nonneg _) (by positivity)
  have h3 : |D w| ≤ a * H ^ 2 := by
    refine (hDw w).trans ?_
    calc L₂ * ‖w‖ ≤ L₂ * β := mul_le_mul_of_nonneg_left hw.le hL₂0
      _ ≤ a * H ^ 2 := hβL
  have hΘ : |φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀| ≤ 3 * a * H ^ 2 := by
    have e1 : φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀ =
        (φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀ - D (y - y₀)) + t * D e + D w := by
      rw [hsplit]; ring
    rw [e1]
    calc _ ≤ |φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀ - D (y - y₀) + t * D e| + |D w| := abs_add_le _ _
      _ ≤ |φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀ - D (y - y₀)| + |t * D e| + |D w| := by
          gcongr; exact abs_add_le _ _
      _ ≤ a * H ^ 2 + a * H * H + a * H ^ 2 := by
          gcongr
          exact hT.trans h1
      _ = 3 * a * H ^ 2 := by ring
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (H ^ 2)⁻¹)]
  calc (H ^ 2)⁻¹ * |φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀| ≤ (H ^ 2)⁻¹ * (3 * a * H ^ 2) :=
        mul_le_mul_of_nonneg_left hΘ (by positivity)
    _ = 3 * a := by field_simp

lemma lower_pointwise {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφc : ∀ x, Continuous (φ x)) (hψc : ∀ x, Continuous (ψ x))
    (hd : ∀ x, Differentiable ℝ (φ x))
    (y₀ e : E m) (he : ‖e‖ = 1) (x₀ x : E n) (L₂ Ψ τ H a β δ : ℝ) (N : ℕ)
    (hL₂0 : 0 ≤ L₂)
    (hL₂ : ∀ y ∈ closedBall y₀ 1, ‖fderiv ℝ (φ x) y - fderiv ℝ (φ x) y₀‖ ≤ L₂ * ‖y - y₀‖ ∧
      ‖fderiv ℝ (φ x₀) y - fderiv ℝ (φ x₀) y₀‖ ≤ L₂ * ‖y - y₀‖)
    (hDw : ∀ w : E m, |(fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀) w| ≤ L₂ * ‖w‖)
    (hDe : |(fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀) e| ≤ H)
    (hΨ : ∀ y, ‖ψ x y‖ ≤ Ψ) (hψL : ∀ y ∈ closedBall y₀ (2 * a * H), ‖ψ x y - ψ x₀ y₀‖ ≤ δ)
    (hH : 0 < H) (hH1 : H ≤ 1) (ha : 0 < a) (ha8 : 8 * L₂ * a ≤ 1) (ha2 : a ≤ 1 / 2)
    (hβ0 : 0 < β) (hβL : L₂ * β ≤ a * H ^ 2) (hβle : β ≤ a * H)
    (hk : ∀ k : ℕ, k < N → 2 * (k : ℝ) * β ≤ a * H)
    (hsmall : 2 * Real.pi * (3 * a) * Ψ + δ ≤ τ / 2) (hτ : τ ≤ ‖ψ x₀ y₀‖)
    (hYfin : volume (knappSet y₀ e β N) ≠ ⊤) :
    τ / 2 * volume.real (knappSet y₀ e β N) ≤
      ‖oscillatoryOp φ ψ (H ^ 2)⁻¹ ((knappSet y₀ e β N).indicator
        (fun y => Complex.exp (2 * Real.pi * Complex.I * (((H ^ 2)⁻¹ * φ x₀ y : ℝ) : ℂ)))) x‖ := by
  set Y := knappSet y₀ e β N with hY
  set R : ℝ := (H ^ 2)⁻¹ with hR
  have hYm : MeasurableSet Y := (knappSet_open y₀ e β N).measurableSet
  have h2aH : 2 * a * H ≤ 1 := by nlinarith
  have hYsub : Y ⊆ closedBall y₀ 1 := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm]
    exact (knappSet_norm_le y₀ e he β a H N hβ0 hβle hk y hy).trans h2aH
  set g : E m → ℂ := fun y => Complex.exp (2 * Real.pi * Complex.I * ((R * φ x₀ y : ℝ) : ℂ))
    with hg
  set K : E m → ℂ := fun y => Complex.exp (-(2 * Real.pi * Complex.I * ((R * φ x y : ℝ) : ℂ))) *
    ψ x y with hK
  have hS : oscillatoryOp φ ψ R (Y.indicator g) x = ∫ y in Y, K y * g y := by
    simp only [oscillatoryOp, kernelOp]
    rw [← integral_indicator hYm]
    congr 1; funext y
    by_cases hy : y ∈ Y
    · simp only [Set.indicator_of_mem hy, hK]
    · simp only [Set.indicator_of_notMem hy, mul_zero]
  set u : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R * (φ x y₀ - φ x₀ y₀) : ℝ) : ℂ))
    with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, Complex.norm_exp]; simp
  have huK : ∀ y, u * (K y * g y) = Complex.exp (-(2 * Real.pi * Complex.I *
      ((R * (φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀) : ℝ) : ℂ))) * ψ x y := by
    intro y
    simp only [hu, hK, hg]
    rw [show ∀ (A B C : ℂ) (z : ℂ), Complex.exp A * (Complex.exp B * z * Complex.exp C) =
      Complex.exp (A + B + C) * z from fun A B C z => by rw [Complex.exp_add, Complex.exp_add]; ring]
    congr 2; push_cast; ring
  have hφx := hφc x
  have hφx₀ := hφc x₀
  have hψx := hψc x
  have hcont : Continuous (fun y => u * (K y * g y)) := by
    simp only [hK, hg]; fun_prop
  have hint : IntegrableOn (fun y => u * (K y * g y)) Y volume :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall y₀ 1)).mono_set hYsub
  set c := ψ x₀ y₀ with hc
  have hΨ0 : 0 ≤ Ψ := (norm_nonneg _).trans (hΨ y₀)
  have hdiff : ‖∫ y in Y, (u * (K y * g y) - c)‖ ≤ τ / 2 * volume.real Y := by
    refine norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 hYfin) (fun y hy => ?_)
    rw [huK]
    have hyb : y ∈ closedBall y₀ (2 * a * H) := by
      rw [mem_closedBall, dist_eq_norm]
      exact knappSet_norm_le y₀ e he β a H N hβ0 hβle hk y hy
    refine (pointwise_bound _ _ _ Ψ δ (hΨ y) (hψL y hyb)).trans ?_
    have hth := theta_bound φ hd y₀ e he x₀ x L₂ H a β N hL₂0 hL₂ hDw hDe hH hH1 ha ha8 ha2
      hβ0 hβL hβle hk y hy
    have : 2 * Real.pi * |R * (φ x y - φ x₀ y - φ x y₀ + φ x₀ y₀)| * Ψ ≤
        2 * Real.pi * (3 * a) * Ψ := by gcongr
    linarith
  have hsplit : ∫ y in Y, (u * (K y * g y) - c) =
      (∫ y in Y, u * (K y * g y)) - volume.real Y • c := by
    rw [integral_sub hint (integrableOn_const hYfin), setIntegral_const]
  have hmain : ‖∫ y in Y, u * (K y * g y)‖ = ‖oscillatoryOp φ ψ R (Y.indicator g) x‖ := by
    rw [hS, integral_const_mul, norm_mul, hu1, one_mul]
  rw [← hmain]
  have hnc : ‖volume.real Y • c‖ = volume.real Y * ‖c‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have tri : ‖volume.real Y • c‖ ≤ ‖∫ y in Y, u * (K y * g y)‖ +
      ‖∫ y in Y, (u * (K y * g y) - c)‖ := by
    rw [hsplit]
    calc ‖volume.real Y • c‖ = ‖(∫ y in Y, u * (K y * g y)) -
          ((∫ y in Y, u * (K y * g y)) - volume.real Y • c)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hV : 0 ≤ volume.real Y := measureReal_nonneg
  have : volume.real Y * τ ≤ volume.real Y * ‖c‖ := mul_le_mul_of_nonneg_left hτ hV
  nlinarith

/-! ## Arithmetic -/
lemma arith (m n : ℕ) (s s' : ℝ) (hs' : 0 < s') (hss : s + s' = 1)
    (κ L₂ V₁m V₁n C' : ℝ) (hκ : 0 < κ) (hL₂ : 1 ≤ L₂) (hV₁m : 0 < V₁m) (hV₁n : 0 < V₁n)
    (τ r H : ℝ) (hτ : 0 < τ) (hr : 0 < r) (hH : 0 < H) (N : ℝ) (hN : 1 / (2 * H) ≤ N)
    (key : τ / 2 * (N * ((κ * τ * H ^ 2 / L₂) ^ m * V₁m)) * (r ^ n * V₁n) ^ s ≤
      C' * ((H ^ 2)⁻¹) ^ (-((m : ℝ) * s') + s' / 4) *
        (N * ((κ * τ * H ^ 2 / L₂) ^ m * V₁m)) ^ s) :
    (1 / 2) * (V₁m / (2 * L₂ ^ m) * κ ^ m) ^ s' * V₁n ^ s * (τ ^ (1 + m * s') * r ^ (n * s)) ≤
      C' * H ^ (s' / 2) := by
  have hL₂0 : 0 < L₂ := by linarith
  set Vy := N * ((κ * τ * H ^ 2 / L₂) ^ m * V₁m) with hVy
  set Vb := r ^ n * V₁n with hVb
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hVy0 : 0 < Vy := by positivity
  have hsplitVy : Vy = Vy ^ s * Vy ^ s' := by rw [← Real.rpow_add hVy0, hss, Real.rpow_one]
  have k1 : τ / 2 * Vy ^ s' * Vb ^ s ≤ C' * ((H ^ 2)⁻¹) ^ (-((m : ℝ) * s') + s' / 4) := by
    have hpos : 0 < Vy ^ s := Real.rpow_pos_of_pos hVy0 s
    have : τ / 2 * Vy ^ s' * Vb ^ s * Vy ^ s ≤
        C' * ((H ^ 2)⁻¹) ^ (-((m : ℝ) * s') + s' / 4) * Vy ^ s := by
      calc τ / 2 * Vy ^ s' * Vb ^ s * Vy ^ s = τ / 2 * (Vy ^ s * Vy ^ s') * Vb ^ s := by ring
        _ = τ / 2 * Vy * Vb ^ s := by rw [← hsplitVy]
        _ ≤ _ := key
    exact le_of_mul_le_mul_right this hpos
  set P := V₁m / (2 * L₂ ^ m) * κ ^ m * τ ^ m with hP
  have hP0 : 0 < P := by positivity
  have hX : P * H ^ ((2 * m : ℝ) - 1) ≤ Vy := by
    have e1 : P * H ^ ((2 * m : ℝ) - 1) = 1 / (2 * H) * ((κ * τ * H ^ 2 / L₂) ^ m * V₁m) := by
      rw [Real.rpow_sub hH, Real.rpow_one,
        show (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, hP]
      rw [div_pow, mul_pow, mul_pow, ← pow_mul]
      field_simp
    rw [e1, hVy]
    exact mul_le_mul_of_nonneg_right hN (by positivity)
  have hX' : (P * H ^ ((2 * m : ℝ) - 1)) ^ s' ≤ Vy ^ s' :=
    Real.rpow_le_rpow (by positivity) hX hs'.le
  rw [Real.mul_rpow hP0.le (by positivity), ← Real.rpow_mul hH.le] at hX'
  have hRpow : ((H ^ 2)⁻¹) ^ (-((m : ℝ) * s') + s' / 4) =
      H ^ (((2 * m : ℝ) - 1) * s') * H ^ (s' / 2) := by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), ← Real.rpow_add hH]
    rw [show (H ^ 2 : ℝ) = H ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_mul hH.le]
    congr 1; push_cast; ring
  rw [hRpow] at k1
  have hHp : 0 < H ^ (((2 * m : ℝ) - 1) * s') := Real.rpow_pos_of_pos hH _
  have k2 : τ / 2 * P ^ s' * Vb ^ s * H ^ (((2 * m : ℝ) - 1) * s') ≤
      C' * H ^ (s' / 2) * H ^ (((2 * m : ℝ) - 1) * s') := by
    calc τ / 2 * P ^ s' * Vb ^ s * H ^ (((2 * m : ℝ) - 1) * s') =
          τ / 2 * (P ^ s' * H ^ (((2 * m : ℝ) - 1) * s')) * Vb ^ s := by ring
      _ ≤ τ / 2 * Vy ^ s' * Vb ^ s := by gcongr
      _ ≤ C' * (H ^ (((2 * m : ℝ) - 1) * s') * H ^ (s' / 2)) := k1
      _ = _ := by ring
  have k3 := le_of_mul_le_mul_right k2 hHp
  have hL : τ / 2 * P ^ s' * Vb ^ s = (1 / 2) * (V₁m / (2 * L₂ ^ m) * κ ^ m) ^ s' * V₁n ^ s *
      (τ ^ (1 + m * s') * r ^ (n * s)) := by
    rw [hP, hVb, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hV₁n.le,
      ← Real.rpow_natCast_mul hτ.le, ← Real.rpow_natCast_mul hr.le, Real.rpow_add hτ,
      Real.rpow_one]
    ring
  rw [← hL]; exact k3

lemma contra (s s' c₂ C' c₀ τ r : ℝ) (m n : ℕ) (hs' : 0 < s') (hc₂ : 0 < c₂) (hC' : 0 < C')
    (hc₀ : 0 < c₀) (hc₀le : c₀ ≤ (c₂ / (2 * C')) ^ (2 / s')) (hτ : 0 < τ) (hr : 0 < r)
    (h : c₂ * (τ ^ (1 + m * s') * r ^ (n * s)) ≤
      C' * (c₀ * τ ^ (2 * (1 + m * s') / s') * r ^ (2 * (n * s) / s')) ^ (s' / 2)) : False := by
  have hT : 0 < τ ^ (1 + m * s') * r ^ (n * s) := by positivity
  have e1 : (c₀ * τ ^ (2 * (1 + m * s') / s') * r ^ (2 * (n * s) / s')) ^ (s' / 2) =
      c₀ ^ (s' / 2) * (τ ^ (1 + m * s') * r ^ (n * s)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hc₀.le (by positivity),
      ← Real.rpow_mul hτ.le, ← Real.rpow_mul hr.le]
    have a1 : 2 * (1 + m * s') / s' * (s' / 2) = 1 + m * s' := by field_simp
    have a2 : 2 * (n * s) / s' * (s' / 2) = n * s := by field_simp
    rw [a1, a2]; ring
  have e2 : c₀ ^ (s' / 2) ≤ c₂ / (2 * C') := by
    calc c₀ ^ (s' / 2) ≤ ((c₂ / (2 * C')) ^ (2 / s')) ^ (s' / 2) :=
          Real.rpow_le_rpow hc₀.le hc₀le (by positivity)
      _ = c₂ / (2 * C') := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show 2 / s' * (s' / 2) = 1 by field_simp, Real.rpow_one]
  rw [e1] at h
  have h4 : C' * (c₀ ^ (s' / 2) * (τ ^ (1 + m * s') * r ^ (n * s))) ≤
      C' * (c₂ / (2 * C') * (τ ^ (1 + m * s') * r ^ (n * s))) := by gcongr
  have e3 : C' * (c₂ / (2 * C') * (τ ^ (1 + m * s') * r ^ (n * s))) =
      c₂ / 2 * (τ ^ (1 + m * s') * r ^ (n * s)) := by field_simp
  nlinarith

/-! ## The Knapp example -/
/-- The Knapp example: the operator bound forces `⟪e, Φ⟫` to oscillate near every point where
`ψ(·, y₀)` is not small. -/
theorem knapp (n m : ℕ) (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (p : ℝ≥0∞) (hp : 1 < p)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      opNorm p p (oscillatoryOp φ ψ R) ≤
        ENNReal.ofReal (C * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε)))
    (y₀ : E m) :
    ∃ A B c₀ r₀ : ℝ, 0 < c₀ ∧ 0 < r₀ ∧ 0 ≤ A ∧ 0 ≤ B ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x₀ : E n, τ ≤ ‖ψ x₀ y₀‖ → ∀ e : E m, ‖e‖ = 1 →
        ∀ r : ℝ, 0 < r → r ≤ r₀ * τ →
          ∃ x ∈ closedBall x₀ r,
            c₀ * τ ^ A * r ^ B ≤ |inner ℝ e (Phi φ y₀ x) - inner ℝ e (Phi φ y₀ x₀)| := by
  -- exponents
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpinv : p⁻¹ < 1 := ENNReal.inv_lt_one.2 hp
  have hs0 : 0 ≤ p⁻¹.toReal := ENNReal.toReal_nonneg
  have hs1 : p⁻¹.toReal < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hpinv
    simpa using this
  have hconj : (conjExp p)⁻¹.toReal = 1 - p⁻¹.toReal := by
    rw [conjExp, inv_inv, ENNReal.toReal_sub_of_le hpinv.le ENNReal.one_ne_top, ENNReal.toReal_one]
  obtain ⟨s, hsdef⟩ : ∃ s, s = p⁻¹.toReal := ⟨_, rfl⟩
  obtain ⟨s', hs'def⟩ : ∃ s', s' = 1 - s := ⟨_, rfl⟩
  rw [← hsdef] at hs0 hs1 hconj
  rw [← hs'def] at hconj
  have hs' : 0 < s' := by rw [hs'def]; linarith only [hs1]
  have hss : s + s' = 1 := by rw [hs'def]; ring
  obtain ⟨C, hC⟩ := hS (s' / 4) (by positivity)
  obtain ⟨C', hC'def⟩ : ∃ C', C' = |C| + 1 := ⟨_, rfl⟩
  have hC'0 : 0 < C' := by rw [hC'def]; positivity
  have hCC' : C ≤ C' := by rw [hC'def]; linarith only [le_abs_self C]
  -- regularity
  have hφx : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x) := fun x =>
    hφ.comp (contDiff_const.prodMk contDiff_id)
  have hφc : ∀ x, Continuous (φ x) := fun x => (hφx x).continuous
  have hd : ∀ x, Differentiable ℝ (φ x) := fun x => (hφx x).differentiable (by simp)
  have hψx : ∀ x, Continuous (ψ x) := fun x =>
    hψ.continuous.comp (continuous_const.prodMk continuous_id)
  -- support radius
  obtain ⟨ρ', hρ'⟩ := hψc.isCompact.isBounded.exists_norm_le
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = max ρ' 0 := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact le_max_right _ _
  have hsupp : ∀ x y, ψ x y ≠ 0 → ‖x‖ ≤ ρ := by
    intro x y h
    have hmem : (x, y) ∈ tsupport (Function.uncurry ψ) :=
      subset_tsupport _ (by simpa using h)
    rw [hρdef]
    exact (norm_fst_le (x, y)).trans ((hρ' _ hmem).trans (le_max_left _ _))
  -- sup bound for ψ
  obtain ⟨Ψ, hΨ⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hΨ0 : 0 ≤ Ψ := (norm_nonneg _).trans (hΨ (0, y₀))
  -- Lipschitz bound for ψ
  obtain ⟨Lψn, hLψn⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ (by simp)
  obtain ⟨Lψ, hLψdef⟩ : ∃ Lψ : ℝ, Lψ = Lψn := ⟨_, rfl⟩
  have hLψ0 : 0 ≤ Lψ := by rw [hLψdef]; exact Lψn.2
  have hψL : ∀ x y x' y', ‖ψ x y - ψ x' y'‖ ≤ Lψ * max (dist x x') (dist y y') := by
    intro x y x' y'
    rw [← dist_eq_norm, hLψdef]
    have := hLψn.dist_le_mul (x, y) (x', y')
    rwa [Prod.dist_eq] at this
  -- Lipschitz bound for `∂_y φ`
  have hgcd : ContDiff ℝ 1 (fun q : E n × E m => fderiv ℝ (φ q.1) q.2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry fun (q : E n × E m) (y : E m) => φ q.1 y) :=
      hφ.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact ContDiff.fderiv h1 contDiff_snd (WithTop.coe_le_coe.2 le_top)
  obtain ⟨Kl, hKl⟩ := hgcd.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall ((0 : E n), y₀) (ρ + 1)) (isCompact_closedBall _ _)
  obtain ⟨L₂, hL₂def⟩ : ∃ L₂ : ℝ, L₂ = Kl + 1 := ⟨_, rfl⟩
  have hKlL₂ : (Kl : ℝ) ≤ L₂ := by rw [hL₂def]; linarith only []
  have hL₂1 : 1 ≤ L₂ := by rw [hL₂def]; linarith only [Kl.2]
  have hL₂0 : 0 < L₂ := by linarith only [hL₂1]
  have memK : ∀ (x : E n) (y : E m), ‖x‖ ≤ ρ + 1 → ‖y - y₀‖ ≤ ρ + 1 →
      ((x, y) : E n × E m) ∈ closedBall ((0 : E n), y₀) (ρ + 1) := by
    intro x y hx hy
    rw [mem_closedBall, Prod.dist_eq, dist_eq_norm, dist_eq_norm, sub_zero]
    exact max_le hx hy
  have hgL : ∀ (x : E n) (y : E m) (x' : E n) (y' : E m), ‖x‖ ≤ ρ + 1 → ‖y - y₀‖ ≤ ρ + 1 →
      ‖x'‖ ≤ ρ + 1 → ‖y' - y₀‖ ≤ ρ + 1 →
      ‖fderiv ℝ (φ x) y - fderiv ℝ (φ x') y'‖ ≤ L₂ * max ‖x - x'‖ ‖y - y'‖ := by
    intro x y x' y' hx hy hx' hy'
    have := hKl.dist_le_mul (x, y) (memK x y hx hy) (x', y') (memK x' y' hx' hy')
    rw [dist_eq_norm, Prod.dist_eq, dist_eq_norm, dist_eq_norm] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right hKlL₂ (le_max_of_le_left (norm_nonneg _))
  -- unit-ball volumes
  obtain ⟨V₁m, hV₁mdef⟩ : ∃ V, V = (volume (ball (0 : E m) 1)).toReal := ⟨_, rfl⟩
  obtain ⟨V₁n, hV₁ndef⟩ : ∃ V, V = (volume (ball (0 : E n) 1)).toReal := ⟨_, rfl⟩
  have hV₁m : 0 < V₁m := by
    rw [hV₁mdef]; exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne'
      measure_ball_lt_top.ne
  have hV₁n : 0 < V₁n := by
    rw [hV₁ndef]; exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne'
      measure_ball_lt_top.ne
  -- constants
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 1 / (100 * (L₂ + Ψ + Lψ + 1)) := ⟨_, rfl⟩
  have hsum : 1 ≤ L₂ + Ψ + Lψ + 1 := by linarith only [hL₂1, hΨ0, hLψ0]
  have hκ0 : 0 < κ := by rw [hκdef]; apply div_pos one_pos; linarith only [hsum]
  have hκsum : κ * (L₂ + Ψ + Lψ + 1) = 1 / 100 := by rw [hκdef]; field_simp
  have hκL₂ : κ * L₂ ≤ 1 / 100 := by
    rw [← hκsum]; exact mul_le_mul_of_nonneg_left (by linarith only [hΨ0, hLψ0, hL₂1]) hκ0.le
  have hκΨ : κ * Ψ ≤ 1 / 100 := by
    rw [← hκsum]; exact mul_le_mul_of_nonneg_left (by linarith only [hΨ0, hLψ0, hL₂1]) hκ0.le
  have hκLψ : κ * Lψ ≤ 1 / 100 := by
    rw [← hκsum]; exact mul_le_mul_of_nonneg_left (by linarith only [hΨ0, hLψ0, hL₂1]) hκ0.le
  have hκ1 : κ ≤ 1 / 100 := by
    rw [← hκsum]; exact le_mul_of_one_le_right hκ0.le hsum
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀ : ℝ, r₀ = 1 / (8 * (Lψ + 1)) := ⟨_, rfl⟩
  have hr₀ : 0 < r₀ := by rw [hr₀def]; positivity
  have hr₀1 : r₀ ≤ 1 := by
    rw [hr₀def, div_le_one (by positivity)]; linarith only [hLψ0]
  have hLψr₀ : Lψ * r₀ ≤ 1 / 8 := by
    rw [hr₀def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hLψ0]
  obtain ⟨c₂, hc₂def⟩ : ∃ c₂ : ℝ,
      c₂ = (1 / 2) * (V₁m / (2 * L₂ ^ m) * κ ^ m) ^ s' * V₁n ^ s := ⟨_, rfl⟩
  have hc₂ : 0 < c₂ := by rw [hc₂def]; positivity
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = min 1 ((c₂ / (2 * C')) ^ (2 / s')) := ⟨_, rfl⟩
  have hc₀ : 0 < c₀ := by
    rw [hc₀def]; exact lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hc₀1 : c₀ ≤ 1 := by rw [hc₀def]; exact min_le_left _ _
  have hc₀le : c₀ ≤ (c₂ / (2 * C')) ^ (2 / s') := by rw [hc₀def]; exact min_le_right _ _
  have hA : 0 ≤ 2 * (1 + m * s') / s' := by
    apply div_nonneg _ hs'.le; have := hs'.le; positivity
  have hB : 0 ≤ 2 * (n * s) / s' := by
    apply div_nonneg _ hs'.le; positivity
  refine ⟨2 * (1 + m * s') / s', 2 * (n * s) / s', c₀, r₀, hc₀, hr₀, hA, hB, ?_⟩
  intro τ hτ hτ1 x₀ hx₀ e he r hr hrτ
  by_contra hcon
  push Not at hcon
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = c₀ * τ ^ (2 * (1 + m * s') / s') * r ^ (2 * (n * s) / s') :=
    ⟨_, rfl⟩
  rw [← hHdef] at hcon
  have hH0 : 0 < H := by rw [hHdef]; positivity
  have hr1 : r ≤ 1 := by
    calc r ≤ r₀ * τ := hrτ
      _ ≤ 1 * 1 := mul_le_mul hr₀1 hτ1 hτ.le zero_le_one
      _ = 1 := one_mul 1
  have hH1 : H ≤ 1 := by
    rw [hHdef]
    have h1 : τ ^ (2 * (1 + m * s') / s') ≤ 1 := Real.rpow_le_one hτ.le hτ1 hA
    have h2 : r ^ (2 * (n * s) / s') ≤ 1 := Real.rpow_le_one hr.le hr1 hB
    have h3 : c₀ * τ ^ (2 * (1 + m * s') / s') ≤ 1 :=
      mul_le_one₀ hc₀1 (by positivity) h1
    exact mul_le_one₀ h3 (by positivity) h2
  have hx₀n : ‖x₀‖ ≤ ρ := hsupp x₀ y₀ (by
    intro h0; rw [h0, norm_zero] at hx₀; linarith only [hx₀, hτ])
  -- the parameters of the Knapp set
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = κ * τ := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [hadef]; positivity
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = κ * τ * H ^ 2 / L₂ := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊1 / (2 * H)⌋₊ + 1 := ⟨_, rfl⟩
  have hNge : 1 / (2 * H) ≤ (N : ℝ) := by
    rw [hNdef]; push_cast; exact (Nat.lt_floor_add_one _).le
  have hk : ∀ k : ℕ, k < N → 2 * (k : ℝ) * β ≤ a * H := by
    intro k hk
    have hk' : (k : ℝ) ≤ 1 / (2 * H) := by
      have : k ≤ ⌊1 / (2 * H)⌋₊ := by omega
      exact (Nat.cast_le.2 this).trans (Nat.floor_le (by positivity))
    calc 2 * (k : ℝ) * β ≤ 2 * (1 / (2 * H)) * β := by gcongr
      _ = κ * τ * H / L₂ := by rw [hβdef]; field_simp
      _ ≤ κ * τ * H := div_le_self (by positivity) hL₂1
      _ = a * H := by rw [hadef]
  have hβL : L₂ * β ≤ a * H ^ 2 := by
    rw [hβdef, hadef]; field_simp; exact le_refl _
  have hβle : β ≤ a * H := by
    rw [hβdef, hadef]
    have hH2 : H ^ 2 ≤ H := by
      calc H ^ 2 = H * H := sq H
        _ ≤ H * 1 := mul_le_mul_of_nonneg_left hH1 hH0.le
        _ = H := mul_one H
    have hpos : (0 : ℝ) ≤ κ * τ * H ^ 2 := by positivity
    calc κ * τ * H ^ 2 / L₂ ≤ κ * τ * H ^ 2 := div_le_self hpos hL₂1
      _ ≤ κ * τ * H := mul_le_mul_of_nonneg_left hH2 (by positivity)
  have ha8 : 8 * L₂ * a ≤ 1 := by
    have : κ * L₂ * τ ≤ 1 / 100 * 1 := mul_le_mul hκL₂ hτ1 hτ.le (by norm_num)
    rw [hadef]; linarith only [this]
  have ha2 : a ≤ 1 / 2 := by
    have : κ * τ ≤ 1 / 100 * 1 := mul_le_mul hκ1 hτ1 hτ.le (by norm_num)
    rw [hadef]; linarith only [this]
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = Lψ * (r + 2 * a * H) := ⟨_, rfl⟩
  have hsmall : 2 * Real.pi * (3 * a) * Ψ + δ ≤ τ / 2 := by
    have p1 : Real.pi * (κ * Ψ) ≤ 4 * (1 / 100) :=
      mul_le_mul Real.pi_lt_four.le hκΨ (by positivity) (by norm_num)
    have p2 : τ * (Real.pi * (κ * Ψ)) ≤ τ * (4 * (1 / 100)) := mul_le_mul_of_nonneg_left p1 hτ.le
    have p3 : (κ * Lψ) * (τ * H) ≤ 1 / 100 * (τ * 1) :=
      mul_le_mul hκLψ (mul_le_mul_of_nonneg_left hH1 hτ.le) (by positivity) (by norm_num)
    have p4 : Lψ * r ≤ Lψ * (r₀ * τ) := mul_le_mul_of_nonneg_left hrτ hLψ0
    have p5 : Lψ * r₀ * τ ≤ 1 / 8 * τ := mul_le_mul_of_nonneg_right hLψr₀ hτ.le
    rw [hδdef, hadef]
    linarith only [p2, p3, p4, p5, hτ]
  -- the test function
  set Y := knappSet y₀ e β N with hY
  have hYm : MeasurableSet Y := (knappSet_open y₀ e β N).measurableSet
  have hYvol := knappSet_volume y₀ e he β hβ0 N
  have hYfin : volume Y ≠ ⊤ := by
    rw [hYvol]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top N)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) ⌊1 / (2 * H)⌋₊]
  have hVy : volume.real Y = N * ((κ * τ * H ^ 2 / L₂) ^ m * V₁m) := by
    rw [measureReal_def, hYvol, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity), hV₁mdef, hβdef]
  have hVy0 : 0 < volume.real Y := by rw [hVy]; positivity
  have hYpos : volume Y ≠ 0 := by
    intro h0; rw [measureReal_def, h0, ENNReal.toReal_zero] at hVy0; exact lt_irrefl _ hVy0
  have hVb : volume.real (closedBall x₀ r) = r ^ n * V₁n := by
    rw [measureReal_def, Measure.addHaar_closedBall volume x₀ hr.le, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hV₁ndef]
  -- the pointwise lower bound
  have hlow : ∀ x ∈ closedBall x₀ r, τ / 2 * volume.real Y ≤
      ‖oscillatoryOp φ ψ (H ^ 2)⁻¹ (Y.indicator
        (fun y => Complex.exp (2 * Real.pi * Complex.I * (((H ^ 2)⁻¹ * φ x₀ y : ℝ) : ℂ)))) x‖ := by
    intro x hx
    have hxx₀ : ‖x - x₀‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hx
    have hxn : ‖x‖ ≤ ρ + 1 := by
      calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
        _ ≤ ρ + 1 := by linarith only [hxx₀, hr1, hx₀n]
    have hx₀n' : ‖x₀‖ ≤ ρ + 1 := by linarith only [hx₀n]
    have hy₀ : ‖y₀ - y₀‖ ≤ ρ + 1 := by rw [sub_self, norm_zero]; linarith only [hρ0]
    have hL₂x : ∀ y ∈ closedBall y₀ 1,
        ‖fderiv ℝ (φ x) y - fderiv ℝ (φ x) y₀‖ ≤ L₂ * ‖y - y₀‖ ∧
        ‖fderiv ℝ (φ x₀) y - fderiv ℝ (φ x₀) y₀‖ ≤ L₂ * ‖y - y₀‖ := by
      intro y hy
      have hy' : ‖y - y₀‖ ≤ ρ + 1 := by
        rw [mem_closedBall, dist_eq_norm] at hy; linarith only [hy, hρ0]
      constructor
      · have := hgL x y x y₀ hxn hy' hxn hy₀
        rwa [sub_self, norm_zero, max_eq_right (norm_nonneg _)] at this
      · have := hgL x₀ y x₀ y₀ hx₀n' hy' hx₀n' hy₀
        rwa [sub_self, norm_zero, max_eq_right (norm_nonneg _)] at this
    have hDw : ∀ w : E m, |(fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀) w| ≤ L₂ * ‖w‖ := by
      intro w
      have h1 := hgL x y₀ x₀ y₀ hxn hy₀ hx₀n' hy₀
      rw [sub_self, norm_zero, max_eq_left (norm_nonneg _)] at h1
      rw [← Real.norm_eq_abs]
      refine ((fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀).le_opNorm w).trans ?_
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      refine h1.trans ?_
      calc L₂ * ‖x - x₀‖ ≤ L₂ * 1 := mul_le_mul_of_nonneg_left (hxx₀.trans hr1) hL₂0.le
        _ = L₂ := mul_one _
    have hDe : |(fderiv ℝ (φ x) y₀ - fderiv ℝ (φ x₀) y₀) e| ≤ H := by
      have := hcon x hx
      rw [inner_Phi, inner_Phi] at this
      rw [sub_apply]
      exact this.le
    have hψL' : ∀ y ∈ closedBall y₀ (2 * a * H), ‖ψ x y - ψ x₀ y₀‖ ≤ δ := by
      intro y hy
      rw [mem_closedBall] at hy
      refine (hψL x y x₀ y₀).trans ?_
      rw [hδdef]
      apply mul_le_mul_of_nonneg_left _ hLψ0
      have h1 : dist x x₀ ≤ r := by rwa [mem_closedBall] at hx
      apply max_le
      · have : 0 ≤ 2 * a * H := by positivity
        linarith only [h1, this]
      · linarith only [hy, hr]
    exact lower_pointwise φ ψ hφc hψx hd y₀ e he x₀ x L₂ Ψ τ H a β δ N hL₂0.le hL₂x hDw hDe
      (fun y => hΨ (x, y)) hψL' hH0 hH1 ha0 ha8 ha2 hβ0 hβL hβle hk hsmall hx₀ hYfin
  -- the operator bound
  have hR1 : 1 ≤ (H ^ 2)⁻¹ := by
    rw [one_le_inv₀ (by positivity)]
    calc H ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hH0.le hH1 2
      _ = 1 := one_pow 2
  have hT := hC (H ^ 2)⁻¹ hR1
  rw [hconj] at hT
  have hT' : opNorm p p (oscillatoryOp φ ψ (H ^ 2)⁻¹) ≤
      ENNReal.ofReal (C' * ((H ^ 2)⁻¹) ^ (-((m : ℝ) * s') + s' / 4)) := by
    refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg (by positivity) _)
  have hg : Continuous (fun y => Complex.exp (2 * Real.pi * Complex.I *
      (((H ^ 2)⁻¹ * φ x₀ y : ℝ) : ℂ))) := by
    have := hφc x₀; fun_prop
  have hg1 : ∀ y, ‖Complex.exp (2 * Real.pi * Complex.I * (((H ^ 2)⁻¹ * φ x₀ y : ℝ) : ℂ))‖ = 1 := by
    intro y
    generalize ((H ^ 2)⁻¹ * φ x₀ y) = t
    have e1 : 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ) =
        ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e1, Complex.norm_exp_ofReal_mul_I]
  have hch := chain p hp0 (oscillatoryOp φ ψ (H ^ 2)⁻¹) _ hT' Y hYm hYfin hYpos _ hg hg1 x₀ r
    (τ / 2 * volume.real Y) hr (by positivity) hlow
  rw [← hsdef, hVb, hVy] at hch
  have har := arith m n s s' hs' hss κ L₂ V₁m V₁n C' hκ0 hL₂1 hV₁m hV₁n τ r H hτ hr hH0 N hNge hch
  rw [← hc₂def, hHdef] at har
  exact contra s s' c₂ C' c₀ τ r m n hs' hc₂ hC'0 hc₀ hc₀le hτ hr har

end TaoBR.TaoDecay.PartK
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
/-! ## Part K: the Knapp example -/
alias knapp := TaoBR.TaoDecay.PartK.knapp

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartR
/-! ## The weight -/
lemma rpow_lip {q B a b : ℝ} (hq : 1 ≤ q) (ha : a ∈ Set.Icc 0 B)
    (hb : b ∈ Set.Icc 0 B) : |a ^ q - b ^ q| ≤ q * B ^ (q - 1) * |a - b| := by
  have hder : ∀ x ∈ Set.Icc 0 B, HasDerivAt (fun x : ℝ => x ^ q) (q * x ^ (q - 1)) x :=
    fun x _ => Real.hasDerivAt_rpow_const (Or.inr hq)
  have := (convex_Icc (0 : ℝ) B).norm_image_sub_le_of_norm_deriv_le
    (f := fun x : ℝ => x ^ q) (C := q * B ^ (q - 1))
    (fun x hx => (hder x hx).differentiableAt)
    (fun x hx => by
      rw [(hder x hx).deriv, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith),
        abs_of_nonneg (Real.rpow_nonneg hx.1 _)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1 hx.2 (by linarith))
        (by linarith)) hb ha
  simpa [Real.norm_eq_abs] using this

/-- The weight `‖ψ(·, y₀)‖^q` is Lipschitz and has bounded support. -/
theorem weight_props (n m : ℕ) (ψ : E n → E m → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (y₀ : E m) (q : ℝ) (hq : 1 ≤ q) :
    (∃ L : ℝ≥0, LipschitzWith L (fun x => ‖ψ x y₀‖ ^ q)) ∧
      ∃ ρ₀ : ℝ, ∀ x, ‖ψ x y₀‖ ^ q ≠ 0 → ‖x‖ ≤ ρ₀ := by
  constructor
  · obtain ⟨K, hK⟩ := hψ.lipschitzWith_of_hasCompactSupport hψc (by simp)
    obtain ⟨B, hB⟩ := hψ.continuous.bounded_above_of_compact_support hψc
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hg : LipschitzWith K (fun x => ψ x y₀) := by
      have h2 : LipschitzWith 1 (fun x : E n => (x, y₀)) :=
        LipschitzWith.of_dist_le_mul fun a b => by simp [Prod.dist_eq]
      have h3 := hK.comp h2
      rw [mul_one] at h3
      exact h3
    refine ⟨Real.toNNReal (q * B ^ (q - 1)) * K, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have hmem : ∀ x, ‖ψ x y₀‖ ∈ Set.Icc 0 B := fun x => ⟨norm_nonneg _, hB (x, y₀)⟩
    rw [Real.dist_eq]
    refine (rpow_lip hq (hmem a) (hmem b)).trans ?_
    have hqB : 0 ≤ q * B ^ (q - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg hB0 _)
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hqB, mul_assoc (q * B ^ (q - 1))]
    refine mul_le_mul_of_nonneg_left ?_ hqB
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← dist_eq_norm]
    exact hg.dist_le_mul a b
  · obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hψc.isCompact.isBounded
    refine ⟨R, fun x hx => ?_⟩
    have hne : ψ x y₀ ≠ 0 := by
      intro h0
      apply hx
      rw [h0, norm_zero, Real.zero_rpow (by linarith)]
    have hmem : (x, y₀) ∈ tsupport (Function.uncurry ψ) :=
      subset_tsupport _ (by simpa using hne)
    exact (norm_fst_le (x, y₀)).trans (hR _ hmem)

end TaoBR.TaoDecay.PartR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
/-! ## Part W: the weight -/
alias weight_props := TaoBR.TaoDecay.PartR.weight_props

end TaoBR.TaoDecay
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay.PartR
/-! ## The map `Φ` -/
/-- The inverse Riesz map as a continuous `ℝ`-linear map. -/
noncomputable def rieszL (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] : StrongDual ℝ F →L[ℝ] F where
  toFun := (InnerProductSpace.toDual ℝ F).symm
  map_add' := map_add _
  map_smul' r x := by simp
  cont := (InnerProductSpace.toDual ℝ F).symm.continuous

theorem Phi_contDiff {n m : ℕ} (φ : E n → E m → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ)) (y₀ : E m) :
    ContDiff ℝ (⊤ : ℕ∞) (Phi φ y₀) := by
  have hpart : ∀ x : E n, fderiv ℝ (fun y => φ x y) y₀ =
      (fderiv ℝ (Function.uncurry φ) (x, y₀)).comp (ContinuousLinearMap.inr ℝ (E n) (E m)) := by
    intro x
    have hd : HasFDerivAt (fun y : E m => (x, y)) (ContinuousLinearMap.inr ℝ (E n) (E m)) y₀ :=
      hasFDerivAt_prodMk_right x y₀
    have := ((hφ.differentiable (by simp)) (x, y₀)).hasFDerivAt.comp y₀ hd
    exact this.fderiv
  have hfun : Phi φ y₀ = fun x => rieszL (E m)
      ((fderiv ℝ (Function.uncurry φ) (x, y₀)).comp (ContinuousLinearMap.inr ℝ (E n) (E m))) := by
    funext x
    rw [Phi, gradient, ← hpart]
    rfl
  rw [hfun]
  refine (rieszL (E m)).contDiff.comp ?_
  refine ContDiff.clm_comp ?_ contDiff_const
  refine (hφ.fderiv_right (m := (⊤ : ℕ∞)) ?_).comp (contDiff_id.prodMk contDiff_const)
  exact le_of_eq (by rfl)

end TaoBR.TaoDecay.PartR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace TaoBR.TaoDecay
alias Phi_contDiff := TaoBR.TaoDecay.PartR.Phi_contDiff

/-! ## Assembly -/
theorem linearizedMeasure_fourier_decay_of_oscillatoryOp_le (n m : ℕ) (hnm : m - 1 ≤ n)
    (hmn : n ≤ m) (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (hrank : HasConstantRank φ ψ (m - 1)) (p : ℝ≥0∞) (hp : 1 < p)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      opNorm p p (oscillatoryOp φ ψ R) ≤
        ENNReal.ofReal (C * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε))) :
    ∀ y₀ : E m, ∀ q : ℝ, 1 ≤ q → ENNReal.ofReal q < p → ∃ C c : ℝ, 0 < c ∧ ∀ ξ : E m,
      ‖∫ x, Complex.exp (-(2 * Real.pi * Complex.I *
          (inner ℝ ξ (gradient (fun y => φ x y) y₀) : ℝ))) * ((‖ψ x y₀‖ ^ q : ℝ) : ℂ)‖ ≤
        C * (1 + ‖ξ‖) ^ (-c) := by
  intro y₀ q hq _
  obtain ⟨⟨L, hL⟩, ρ₀, hρ₀⟩ := weight_props n m ψ hψ hψc y₀ q hq
  obtain ⟨A, B, c₀, r₀, hc₀, hr₀, hA, hB, hK⟩ := knapp n m φ ψ hφ hψ hψc p hp hS y₀
  have hK' : ∃ A B c₀ r₀ : ℝ, 0 < c₀ ∧ 0 < r₀ ∧ 0 ≤ A ∧ 0 ≤ B ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x₀ : E n, τ ≤ ‖ψ x₀ y₀‖ ^ q → ∀ e : E m, ‖e‖ = 1 →
        ∀ r : ℝ, 0 < r → r ≤ r₀ * τ →
          ∃ x ∈ closedBall x₀ r, c₀ * τ ^ A * r ^ B ≤
            |inner ℝ e (Phi φ y₀ x) - inner ℝ e (Phi φ y₀ x₀)| := by
    refine ⟨A, B, c₀, r₀, hc₀, hr₀, hA, hB, ?_⟩
    intro τ hτ hτ1 x₀ hx₀ e he r hr hrτ
    have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
    -- `τ ≤ τ^(1/q) ≤ ‖ψ x₀ y₀‖`
    have hτq : τ ≤ τ ^ (1 / q) := by
      apply Real.self_le_rpow_of_le_one hτ.le hτ1
      rw [div_le_one hq0]; exact hq
    have hτq1 : τ ^ (1 / q) ≤ 1 := Real.rpow_le_one hτ.le hτ1 (by positivity)
    have hψτ : τ ^ (1 / q) ≤ ‖ψ x₀ y₀‖ := by
      have := Real.rpow_le_rpow hτ.le hx₀ (by positivity : (0:ℝ) ≤ 1 / q)
      rwa [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hq0.ne', Real.rpow_one] at this
    obtain ⟨x, hx, hbound⟩ := hK (τ ^ (1 / q)) (by positivity) hτq1 x₀ hψτ e he r hr
      (hrτ.trans (mul_le_mul_of_nonneg_left hτq hr₀.le))
    refine ⟨x, hx, le_trans ?_ hbound⟩
    gcongr
  obtain ⟨C, c, hc, h⟩ := decay_of_knapp (Phi φ y₀) (Phi_contDiff φ hφ y₀)
    (fun x => ‖ψ x y₀‖ ^ q) (fun x => by positivity) ρ₀ hρ₀ L hL hK'
  exact ⟨C, c, hc, fun ξ => h ξ⟩

end TaoBR.TaoDecay
end

open MeasureTheory in
open scoped ENNReal NNReal in
theorem solution : type_of% @TaoBR.TaoDecay.linearizedMeasure_fourier_decay_of_oscillatoryOp_le :=
  @TaoBR.TaoDecay.linearizedMeasure_fourier_decay_of_oscillatoryOp_le
