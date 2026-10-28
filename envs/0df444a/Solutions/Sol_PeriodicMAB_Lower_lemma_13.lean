-- Prove2me | solution 1 for PeriodicMAB.Lower.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T22:14:49.527427+00:00
-- url     : https://prove2.me/submissions/8e2021ff-3fec-4907-abd8-482dc4169857

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm PeriodicMAB.Lower
open scoped ENNReal

namespace PMABKeyAux


lemma pd_pos (m y : ℝ) : 0 < gaussianPDFReal m 1 y := gaussianPDFReal_pos _ _ _ one_ne_zero

lemma pd_eq (m y : ℝ) : gaussianPDFReal m 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y - m) ^ 2 / 2) := by
  simp [gaussianPDFReal]

lemma sqrt_pd_mul (a b y : ℝ) :
    Real.sqrt (gaussianPDFReal a 1 y * gaussianPDFReal b 1 y) = Real.exp (-(a - b) ^ 2 / 8) * gaussianPDFReal ((a + b) / 2) 1 y := by
  rw [pd_eq, pd_eq, pd_eq]
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have : (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y - a) ^ 2 / 2) *
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y - b) ^ 2 / 2)) =
      ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(a - b) ^ 2 / 8) *
        Real.exp (-(y - (a + b) / 2) ^ 2 / 2))) ^ 2 := by
    have e1 : Real.exp (-(y - a) ^ 2 / 2) * Real.exp (-(y - b) ^ 2 / 2) =
        (Real.exp (-(a - b) ^ 2 / 8) * Real.exp (-(y - (a + b) / 2) ^ 2 / 2)) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [mul_pow, ← e1]; ring
  rw [this, Real.sqrt_sq (by positivity)]
  ring

/-- Gaussian change of measure, lintegral form. -/
lemma gauss_lintegral_change (m₁ m₂ : ℝ) (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ y, ψ y ∂(gaussianReal m₁ 1) =
      ∫⁻ y, ψ y * ENNReal.ofReal (gaussianPDFReal m₁ 1 y / gaussianPDFReal m₂ 1 y) ∂(gaussianReal m₂ 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hψ,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _)]
  · congr 1
    funext y
    simp only [Pi.mul_apply, gaussianPDF]
    have : gaussianPDFReal m₂ 1 y * (gaussianPDFReal m₁ 1 y / gaussianPDFReal m₂ 1 y) =
        gaussianPDFReal m₁ 1 y := by
      have := (pd_pos m₂ y).ne'; field_simp
    rw [mul_comm (ψ y), ← mul_assoc, ← ENNReal.ofReal_mul (pd_pos _ _).le, this]
  · exact hψ.mul (ENNReal.measurable_ofReal.comp
      ((measurable_gaussianPDFReal m₁ 1).div (measurable_gaussianPDFReal m₂ 1)))

/-- Bhattacharyya coefficient of two unit Gaussians. -/
lemma gauss_bc (a b : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.sqrt (gaussianPDFReal a 1 y / gaussianPDFReal b 1 y)) ∂(gaussianReal b 1) =
      ENNReal.ofReal (Real.exp (-(a - b) ^ 2 / 8)) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _)]
  · have : ∀ y, (gaussianPDF b 1 * fun y => ENNReal.ofReal (Real.sqrt (gaussianPDFReal a 1 y / gaussianPDFReal b 1 y))) y =
        ENNReal.ofReal (Real.exp (-(a - b) ^ 2 / 8)) * ENNReal.ofReal (gaussianPDFReal ((a + b) / 2) 1 y) := by
      intro y
      simp only [Pi.mul_apply, gaussianPDF]
      rw [← ENNReal.ofReal_mul (pd_pos _ _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← sqrt_pd_mul]
      congr 1
      have hb := pd_pos b y
      rw [Real.sqrt_div' _ hb.le]
      rw [show gaussianPDFReal a 1 y * gaussianPDFReal b 1 y = (gaussianPDFReal a 1 y / gaussianPDFReal b 1 y) * (gaussianPDFReal b 1 y) ^ 2 by field_simp]
      rw [Real.sqrt_mul (div_nonneg (pd_pos _ _).le hb.le), Real.sqrt_sq hb.le,
        Real.sqrt_div' _ hb.le]
      show gaussianPDFReal b 1 y * _ = _
      field_simp
    simp_rw [this]
    rw [lintegral_const_mul _ (f := fun y => ENNReal.ofReal (gaussianPDFReal ((a + b) / 2) 1 y))
      (ENNReal.measurable_ofReal.comp (measurable_gaussianPDFReal _ _))]
    rw [lintegral_gaussianPDFReal_eq_one _ one_ne_zero, mul_one]
  · exact ENNReal.measurable_ofReal.comp (((measurable_gaussianPDFReal a 1).div
      (measurable_gaussianPDFReal b 1)).sqrt)


section Measures

variable {K : ℕ}

/-- one-step likelihood ratio at epoch `t`. -/
noncomputable def lr (μ ν : Fin K → ℕ → ℝ) (t : ℕ) (x : Fin K × ℝ) : ℝ :=
  gaussianPDFReal (μ x.1 t) 1 x.2 / gaussianPDFReal (ν x.1 t) 1 x.2

/-- likelihood ratio of a history of length `n`. -/
noncomputable def LR (μ ν : Fin K → ℕ → ℝ) (n : ℕ) (h : BanditHistory K n) : ℝ :=
  ∏ i : Fin n, lr μ ν ((i : ℕ) + 1) (h i)

lemma lr_pos (μ ν : Fin K → ℕ → ℝ) (t : ℕ) (x : Fin K × ℝ) : 0 < lr μ ν t x :=
  div_pos (pd_pos _ _) (pd_pos _ _)

lemma LR_pos (μ ν : Fin K → ℕ → ℝ) (n : ℕ) (h : BanditHistory K n) : 0 < LR μ ν n h :=
  Finset.prod_pos (fun i _ => lr_pos _ _ _ _)

lemma measurable_pdf_arm (m : Fin K → ℝ) :
    Measurable (fun x : Fin K × ℝ => gaussianPDFReal (m x.1) 1 x.2) :=
  measurable_uncurry_gaussianPDFReal.comp
    (((Measurable.of_discrete (f := m)).comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))

lemma measurable_lr (μ ν : Fin K → ℕ → ℝ) (t : ℕ) : Measurable (lr μ ν t) :=
  (measurable_pdf_arm (fun a => μ a t)).div (measurable_pdf_arm (fun a => ν a t))

lemma measurable_LR (μ ν : Fin K → ℕ → ℝ) (n : ℕ) : Measurable (LR μ ν n) := by
  unfold LR
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_lr μ ν _).comp (measurable_pi_apply i))

lemma LR_snoc (μ ν : Fin K → ℕ → ℝ) (n : ℕ) (h : BanditHistory K n) (x : Fin K × ℝ) :
    LR μ ν (n + 1) (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h x) = LR μ ν n h * lr μ ν (n + 1) x := by
  unfold LR
  rw [Fin.prod_univ_castSucc]
  simp

lemma step_lintegral (π : BanditPolicy K) (m : Fin K → ℝ) (n : ℕ) (h : BanditHistory K n)
    (φ : Fin K × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂(banditStepKernel (gaussianBandit m) π n h) =
      ∫⁻ a, ∫⁻ y, φ (a, y) ∂(gaussianReal (m a) 1) ∂(π.select n h) := by
  simp only [banditStepKernel]
  rw [Kernel.lintegral_compProd _ _ _ hφ]
  rfl

lemma step_change (π : BanditPolicy K) (m₁ m₂ : Fin K → ℝ) (n : ℕ) (h : BanditHistory K n)
    (φ : Fin K × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂(banditStepKernel (gaussianBandit m₁) π n h) =
      ∫⁻ x, φ x * ENNReal.ofReal (gaussianPDFReal (m₁ x.1) 1 x.2 / gaussianPDFReal (m₂ x.1) 1 x.2)
        ∂(banditStepKernel (gaussianBandit m₂) π n h) := by
  rw [step_lintegral π m₁ n h φ hφ, step_lintegral π m₂ n h
    (fun x => φ x * ENNReal.ofReal (gaussianPDFReal (m₁ x.1) 1 x.2 / gaussianPDFReal (m₂ x.1) 1 x.2))
    (hφ.mul (ENNReal.measurable_ofReal.comp
      ((measurable_pdf_arm m₁).div (measurable_pdf_arm m₂))))]
  congr 1
  funext a
  exact gauss_lintegral_change (m₁ a) (m₂ a) _ (hφ.comp measurable_prodMk_left)

lemma periodicMeasure_lintegral (π : BanditPolicy K) (μ : Fin K → ℕ → ℝ) (n : ℕ)
    (g : BanditHistory K (n + 1) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ h, g h ∂(periodicMeasure μ π (n + 1)) =
      ∫⁻ h, ∫⁻ x, g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h x)
        ∂(banditStepKernel (gaussianBandit (fun a ↦ μ a (n + 1))) π n h)
        ∂(periodicMeasure μ π n) := by
  simp only [periodicMeasure]
  rw [lintegral_map hg measurable_banditHistorySnoc,
    Measure.lintegral_compProd (f := fun p : BanditHistory K n × (Fin K × ℝ) =>
      g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) p.1 p.2)) (hg.comp measurable_banditHistorySnoc)]

lemma lr_identity (π : BanditPolicy K) (μ ν : Fin K → ℕ → ℝ) (n : ℕ) :
    ∀ g : BanditHistory K n → ℝ≥0∞, Measurable g →
      ∫⁻ h, g h ∂(periodicMeasure μ π n) =
        ∫⁻ h, g h * ENNReal.ofReal (LR μ ν n h) ∂(periodicMeasure ν π n) := by
  induction n with
  | zero =>
    intro g hg
    simp only [periodicMeasure]
    rw [lintegral_dirac' _ hg, lintegral_dirac' (f := fun h => g h * ENNReal.ofReal (LR μ ν 0 h))
      _ (hg.mul (ENNReal.measurable_ofReal.comp (measurable_LR μ ν 0)))]
    simp [LR]
  | succ n ih =>
    intro g hg
    have hgs : Measurable (fun p : BanditHistory K n × (Fin K × ℝ) =>
        g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) p.1 p.2)) := hg.comp measurable_banditHistorySnoc
    have hLs : Measurable (fun h : BanditHistory K (n + 1) =>
        g h * ENNReal.ofReal (LR μ ν (n + 1) h)) :=
      hg.mul (ENNReal.measurable_ofReal.comp (measurable_LR μ ν _))
    rw [periodicMeasure_lintegral π μ n g hg, periodicMeasure_lintegral π ν n _ hLs]
    rw [ih _ (hgs.lintegral_kernel_prod_right'
      (κ := banditStepKernel (gaussianBandit (fun a ↦ μ a (n + 1))) π n))]
    congr 1
    funext h
    rw [step_change π (fun a ↦ μ a (n + 1)) (fun a ↦ ν a (n + 1)) n h
      (fun x => g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h x))
      (hgs.comp (measurable_const.prodMk measurable_id)),
      ← lintegral_mul_const (f := fun x => g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h x) *
        ENNReal.ofReal (gaussianPDFReal (μ x.1 (n + 1)) 1 x.2 /
          gaussianPDFReal (ν x.1 (n + 1)) 1 x.2)) _ ((hgs.comp (measurable_const.prodMk measurable_id)).mul
        (ENNReal.measurable_ofReal.comp (measurable_lr μ ν (n + 1))))]
    congr 1
    funext x
    rw [LR_snoc, ENNReal.ofReal_mul (LR_pos _ _ _ _).le]
    simp only [lr]
    ring

lemma affinity (π : BanditPolicy K) (μ ν : Fin K → ℕ → ℝ) (D : ℕ → ℝ)
    (hD : ∀ a t, |μ a t - ν a t| ≤ D t) (n : ℕ) :
    ENNReal.ofReal (Real.exp (-(∑ i ∈ Finset.range n, D (i + 1) ^ 2) / 8)) ≤
      ∫⁻ h, ENNReal.ofReal (Real.sqrt (LR μ ν n h)) ∂(periodicMeasure ν π n) := by
  induction n with
  | zero =>
    simp only [periodicMeasure]
    rw [lintegral_dirac' (f := fun h => ENNReal.ofReal (Real.sqrt (LR μ ν 0 h))) _
      (ENNReal.measurable_ofReal.comp (measurable_LR μ ν 0).sqrt)]
    simp [LR]
  | succ n ih =>
    have hm : Measurable (fun h : BanditHistory K (n + 1) =>
        ENNReal.ofReal (Real.sqrt (LR μ ν (n + 1) h))) :=
      ENNReal.measurable_ofReal.comp (measurable_LR μ ν _).sqrt
    rw [periodicMeasure_lintegral π ν n _ hm]
    set e := Real.exp (-(D (n + 1)) ^ 2 / 8) with he
    have hinner : ∀ h : BanditHistory K n,
        ENNReal.ofReal (Real.sqrt (LR μ ν n h)) * ENNReal.ofReal e ≤
        ∫⁻ x, ENNReal.ofReal (Real.sqrt (LR μ ν (n + 1)
          (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h x)))
          ∂(banditStepKernel (gaussianBandit (fun a ↦ ν a (n + 1))) π n h) := by
      intro h
      simp_rw [LR_snoc, Real.sqrt_mul (LR_pos _ _ _ _).le, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      rw [lintegral_const_mul (f := fun x => ENNReal.ofReal (Real.sqrt (lr μ ν (n + 1) x))) _
        (ENNReal.measurable_ofReal.comp (measurable_lr μ ν _).sqrt)]
      gcongr
      rw [step_lintegral π _ n h (fun x => ENNReal.ofReal (Real.sqrt (lr μ ν (n + 1) x)))
        (ENNReal.measurable_ofReal.comp (measurable_lr μ ν _).sqrt)]
      have : ∀ a, ENNReal.ofReal e ≤ ∫⁻ y, ENNReal.ofReal (Real.sqrt (lr μ ν (n + 1) (a, y)))
          ∂(gaussianReal (ν a (n + 1)) 1) := by
        intro a
        simp only [lr]
        rw [gauss_bc]
        apply ENNReal.ofReal_le_ofReal
        rw [he]
        apply Real.exp_le_exp.mpr
        have h1 := hD a (n + 1)
        have h2 : (μ a (n + 1) - ν a (n + 1)) ^ 2 ≤ D (n + 1) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        linarith
      calc ENNReal.ofReal e = ∫⁻ a, ENNReal.ofReal e ∂(π.select n h) := by simp
        _ ≤ _ := lintegral_mono this
    calc ENNReal.ofReal (Real.exp (-(∑ i ∈ Finset.range (n + 1), D (i + 1) ^ 2) / 8))
        = ENNReal.ofReal (Real.exp (-(∑ i ∈ Finset.range n, D (i + 1) ^ 2) / 8)) *
            ENNReal.ofReal e := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, he, ← Real.exp_add,
            Finset.sum_range_succ]
          congr 2; ring
      _ ≤ (∫⁻ h, ENNReal.ofReal (Real.sqrt (LR μ ν n h)) ∂(periodicMeasure ν π n)) *
            ENNReal.ofReal e := by gcongr
      _ = ∫⁻ h, ENNReal.ofReal (Real.sqrt (LR μ ν n h)) * ENNReal.ofReal e
            ∂(periodicMeasure ν π n) := by
          rw [lintegral_mul_const (f := fun h => ENNReal.ofReal (Real.sqrt (LR μ ν n h))) _
            (ENNReal.measurable_ofReal.comp (measurable_LR μ ν n).sqrt)]
      _ ≤ _ := lintegral_mono hinner

lemma sqrt_le_amgm (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    Real.sqrt x ≤ (t * min x 1 + (x + 1 - min x 1) / t) / 2 := by
  have hs := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg x
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  rcases le_total x 1 with h | h
  · rw [min_eq_left h]
    have : x + 1 - x = 1 := by ring
    rw [this, add_div' _ _ _ ht.ne', le_div_iff₀ ht]
    have e : t * x * t = (t * Real.sqrt x) ^ 2 := by rw [mul_pow, hs]; ring
    nlinarith [sq_nonneg (t * Real.sqrt x - 1)]
  · rw [min_eq_right h]
    have : x + 1 - 1 = x := by ring
    rw [this, add_div' _ _ _ ht.ne', le_div_iff₀ ht]
    nlinarith [sq_nonneg (t - Real.sqrt x)]

/-- **Testing bound.** For two periodic Gaussian instances whose means differ by at most `D t`
at epoch `t`, and any `[0,1]`-valued statistic `f` of the history, the difference of expectations
is at most `1 - exp(-∑ D_t² / 4) / 2`. -/
theorem testing_bound (π : BanditPolicy K) (μ ν : Fin K → ℕ → ℝ) (D : ℕ → ℝ)
    (hD : ∀ a t, |μ a t - ν a t| ≤ D t) (n : ℕ) (f : BanditHistory K n → ℝ)
    (hf : Measurable f) (hf0 : ∀ h, 0 ≤ f h) (hf1 : ∀ h, f h ≤ 1) :
    ∫ h, f h ∂(periodicMeasure μ π n) - ∫ h, f h ∂(periodicMeasure ν π n) ≤
      1 - Real.exp (-(∑ i ∈ Finset.range n, D (i + 1) ^ 2) / 4) / 2 := by
  set P := periodicMeasure ν π n with hP
  set L := LR μ ν n with hLdef
  have hL0 : ∀ h, 0 ≤ L h := fun h => (LR_pos μ ν n h).le
  have hLm : Measurable L := measurable_LR μ ν n
  -- total mass
  have hL1 : ∫⁻ h, ENNReal.ofReal (L h) ∂P = 1 := by
    have := lr_identity π μ ν n (fun _ => 1) measurable_const
    simp only [one_mul, lintegral_const, measure_univ] at this
    exact this.symm
  have hLint : Integrable L P := by
    refine ⟨hLm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hL0), hL1]
    exact ENNReal.one_lt_top
  have hLI : ∫ h, L h ∂P = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hL0) hLm.aestronglyMeasurable, hL1]
    rfl
  -- change of measure for f
  have hfL : ∫ h, f h ∂(periodicMeasure μ π n) = ∫ h, f h * L h ∂P := by
    have := lr_identity π μ ν n (fun h => ENNReal.ofReal (f h))
      (ENNReal.measurable_ofReal.comp hf)
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun h => mul_nonneg (hf0 h) (hL0 h)))
        (hf.mul hLm).aestronglyMeasurable, this]
    congr 1
    congr 1
    funext h
    rw [ENNReal.ofReal_mul (hf0 h)]
  have hfint : Integrable f P := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ (fun h => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 h)]; exact hf1 h))
  have hfLint : Integrable (fun h => f h * L h) P := by
    refine Integrable.mono' hLint (hf.mul hLm).aestronglyMeasurable (ae_of_all _ (fun h => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 h) (hL0 h))]
    nlinarith [hf1 h, hL0 h]
  have hminm : Measurable (fun h => min (L h) 1) := hLm.min measurable_const
  have hminint : Integrable (fun h => min (L h) 1) P := Integrable.of_bound
    hminm.aestronglyMeasurable 1 (ae_of_all _ (fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hL0 h) zero_le_one)]; exact min_le_right _ _))
  set m := ∫ h, min (L h) 1 ∂P with hm
  have hm0 : 0 ≤ m := integral_nonneg (fun h => le_min (hL0 h) zero_le_one)
  -- step 1: difference ≤ 1 - m
  have hstep1 : ∫ h, f h ∂(periodicMeasure μ π n) - ∫ h, f h ∂P ≤ 1 - m := by
    rw [hfL, ← integral_sub hfLint hfint, ← hLI, hm, ← integral_sub hLint hminint]
    refine integral_mono (hfLint.sub hfint) (hLint.sub hminint) (fun h => ?_)
    simp only
    rcases le_total (L h) 1 with hl | hl
    · rw [min_eq_left hl]; nlinarith [hf0 h, hL0 h]
    · rw [min_eq_right hl]; nlinarith [hf1 h, hL0 h]
  -- step 2: affinity
  set A := ∫ h, Real.sqrt (L h) ∂P with hA
  have hsqrtm : Measurable (fun h => Real.sqrt (L h)) := hLm.sqrt
  have hsqrtint : Integrable (fun h => Real.sqrt (L h)) P := by
    refine Integrable.mono' (hLint.add (integrable_const 1)) hsqrtm.aestronglyMeasurable
      (ae_of_all _ (fun h => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [Real.sq_sqrt (hL0 h), Real.sqrt_nonneg (L h), sq_nonneg (Real.sqrt (L h) - 1)]
  have hAff : Real.exp (-(∑ i ∈ Finset.range n, D (i + 1) ^ 2) / 8) ≤ A := by
    have h1 := affinity π μ ν D hD n
    rw [hA, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun h => Real.sqrt_nonneg _))
      hsqrtm.aestronglyMeasurable]
    have hfin : ∫⁻ h, ENNReal.ofReal (Real.sqrt (L h)) ∂P ≠ ⊤ :=
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun h => Real.sqrt_nonneg _))).mp
        hsqrtint.2 |>.ne
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
    exact h1
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hAff
  -- step 3: A^2 ≤ 2 m
  have hA2 : A ^ 2 ≤ 2 * m := by
    set t := 2 / A with ht
    have htpos : 0 < t := div_pos two_pos hApos
    have hpt : A ≤ ∫ h, (t * min (L h) 1 + (L h + 1 - min (L h) 1) / t) / 2 ∂P :=
      integral_mono hsqrtint
        ((((hminint.const_mul t).add (((hLint.add (integrable_const 1)).sub
          hminint).div_const t)).div_const 2))
        (fun h => sqrt_le_amgm (L h) t (hL0 h) htpos)
    have heval : ∫ h, (t * min (L h) 1 + (L h + 1 - min (L h) 1) / t) / 2 ∂P =
        (t * m + (2 - m) / t) / 2 := by
      rw [integral_div, integral_add (f := fun h => t * min (L h) 1)
        (g := fun h => (L h + 1 - min (L h) 1) / t) (hminint.const_mul t)
        (((hLint.add (integrable_const 1)).sub hminint).div_const t),
        integral_const_mul, integral_div, integral_sub (f := fun h => L h + 1)
        (g := fun h => min (L h) 1) (hLint.add (integrable_const 1)) hminint,
        integral_add (f := L) (g := fun _ => (1 : ℝ)) hLint (integrable_const 1), hLI]
      simp [hm]
      try ring
    rw [heval] at hpt
    have h3 : A ≤ (t * m + 2 / t) / 2 := by
      have : (2 - m) / t ≤ 2 / t := div_le_div_of_nonneg_right (by linarith) htpos.le
      linarith
    rw [ht] at h3
    have e : (2 / A * m + 2 / (2 / A)) / 2 = m / A + A / 2 := by field_simp
    rw [e] at h3
    have : A * A ≤ m + A * A / 2 := by
      have := mul_le_mul_of_nonneg_left h3 hApos.le
      rw [mul_add, mul_div_cancel₀ _ hApos.ne'] at this
      linarith
    nlinarith
  -- conclude
  have hexp : Real.exp (-(∑ i ∈ Finset.range n, D (i + 1) ^ 2) / 4) =
      Real.exp (-(∑ i ∈ Finset.range n, D (i + 1) ^ 2) / 8) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have : Real.exp (-(∑ i ∈ Finset.range n, D (i + 1) ^ 2) / 8) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hAff 2
  rw [hexp]
  linarith

end Measures

end PMABKeyAux



namespace PMABKeyAux

/-- the phase `(t - 1) mod T₁` of epoch `t`. -/
def phase (T₁ : ℕ) (hT₁ : 1 ≤ T₁) (t : ℕ) : Fin T₁ := ⟨(t - 1) % T₁, Nat.mod_lt _ hT₁⟩

/-- the hard instance indexed by a sign pattern `c`. -/
noncomputable def hardInst {K : ℕ} [NeZero K] (T₁ : ℕ) (hT₁ : 1 ≤ T₁) (Δ : ℝ) (c : Fin T₁ → Bool) :
    Fin K → ℕ → ℝ :=
  fun k t => if k = 0 then
    1 / 2 + (if c (phase T₁ hT₁ t) then Δ else -Δ) +
      (if ((phase T₁ hT₁ t : ℕ) = 0) then Δ / 4 else 0)
    else 1 / 2

lemma phase_add (T₁ : ℕ) (hT₁ : 1 ≤ T₁) (t : ℕ) (ht : 1 ≤ t) :
    phase T₁ hT₁ (t + T₁) = phase T₁ hT₁ t := by
  ext
  simp only [phase]
  have : t + T₁ - 1 = (t - 1) + T₁ := by omega
  rw [this, Nat.add_mod_right]

lemma hardInst_E2 {K : ℕ} [NeZero K] (T T₁ : ℕ) (hT₁ : 1 ≤ T₁) (Δ : ℝ) (hΔ : 0 < Δ)
    (hΔ3 : Δ ≤ 1 / 3) (c : Fin T₁ → Bool) :
    InE2 T T₁ (hardInst (K := K) T₁ hT₁ Δ c) ∧
      (∀ k, k ≠ 0 → ∀ t, hardInst (K := K) T₁ hT₁ Δ c k t = 1 / 2) := by
  refine ⟨⟨⟨hT₁, fun t ht => ?_, fun q hq0 hqT h => ?_⟩, fun k hk t _ => ?_, fun k t _ _ => ?_⟩,
    fun k hk t => ?_⟩
  · simp only [hardInst, if_pos rfl, phase_add T₁ hT₁ t ht]
  · have h1 := h 1 le_rfl
    simp only [hardInst, if_pos rfl] at h1
    have hp1 : (phase T₁ hT₁ 1 : ℕ) = 0 := by simp [phase]
    have hpq : (phase T₁ hT₁ (1 + q) : ℕ) = q := by
      simp [phase, Nat.mod_eq_of_lt hqT]
    have hpq0 : (phase T₁ hT₁ (1 + q) : ℕ) ≠ 0 := by omega
    rw [if_pos hp1, if_neg hpq0] at h1
    rcases hb1 : c (phase T₁ hT₁ (1 + q)) <;> rcases hb2 : c (phase T₁ hT₁ 1) <;>
      simp only [hb1, hb2] at h1 <;> simp at h1 <;> linarith
  · simp [hardInst, hk]
  · simp only [hardInst]
    split_ifs <;> constructor <;> linarith
  · simp [hardInst, hk]

lemma card_phase_le (T T₁ : ℕ) (hT₁ : 1 ≤ T₁) (j : ℕ) :
    ((((Finset.range T).filter (fun i => i % T₁ = j)).card : ℕ) : ℝ) ≤ (T : ℝ) / T₁ + 1 := by
  have h1 : ((Finset.range T).filter (fun i => i % T₁ = j)).card ≤ T / T₁ + 1 := by
    have := Finset.card_le_card_of_injOn (fun i => i / T₁)
      (s := (Finset.range T).filter (fun i => i % T₁ = j)) (t := Finset.range (T / T₁ + 1))
      (fun i hi => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
        simp only [Finset.coe_range, Set.mem_Iio]
        have := Nat.div_le_div_right (c := T₁) hi.1.le
        omega)
      (fun i hi i' hi' hii' => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hi'
        simp only at hii'
        rw [← Nat.div_add_mod i T₁, ← Nat.div_add_mod i' T₁, hii', hi.2, hi'.2])
    simpa using this
  calc ((((Finset.range T).filter (fun i => i % T₁ = j)).card : ℕ) : ℝ)
      ≤ ((T / T₁ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (T : ℝ) / T₁ + 1 := by push_cast; linarith [Nat.cast_div_le (m := T) (n := T₁) (α := ℝ)]

/-- indicator that arm `0` is pulled in round `i`. -/
noncomputable def ind0 {K : ℕ} [NeZero K] {n : ℕ} (i : Fin n) (h : BanditHistory K n) : ℝ :=
  if (h i).1 = 0 then 1 else 0

lemma measurable_ind0 {K : ℕ} [NeZero K] {n : ℕ} (i : Fin n) :
    Measurable (ind0 (K := K) i) :=
  (Measurable.of_discrete (f := fun a : Fin K => if a = 0 then (1 : ℝ) else 0)).comp
    (measurable_fst.comp (measurable_pi_apply i))

lemma ind0_nonneg {K : ℕ} [NeZero K] {n : ℕ} (i : Fin n) (h : BanditHistory K n) :
    0 ≤ ind0 i h := by unfold ind0; split_ifs <;> norm_num

lemma ind0_le_one {K : ℕ} [NeZero K] {n : ℕ} (i : Fin n) (h : BanditHistory K n) :
    ind0 i h ≤ 1 := by unfold ind0; split_ifs <;> norm_num

lemma integral_mean_eq {K T : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (P : Measure (BanditHistory K T))
    [IsProbabilityMeasure P] (i : Fin T) (t : ℕ) (hk : ∀ k, k ≠ 0 → μ k t = 1 / 2) :
    ∫ h, μ (h i).1 t ∂P = 1 / 2 + (μ 0 t - 1 / 2) * ∫ h, ind0 i h ∂P := by
  have : ∀ h : BanditHistory K T, μ (h i).1 t = 1 / 2 + (μ 0 t - 1 / 2) * ind0 i h := by
    intro h
    unfold ind0
    by_cases ha : (h i).1 = 0
    · rw [if_pos ha, ha]; ring
    · rw [if_neg ha, hk _ ha]; ring
  simp_rw [this]
  have hint : Integrable (ind0 (K := K) i) P := Integrable.of_bound
    (measurable_ind0 i).aestronglyMeasurable 1 (ae_of_all _ (fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ind0_nonneg i h)]; exact ind0_le_one i h))
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul]
  simp

lemma hardInst_diff {K : ℕ} [NeZero K] (T₁ : ℕ) (hT₁ : 1 ≤ T₁) (Δ : ℝ) (hΔ : 0 < Δ)
    (c c' : Fin T₁ → Bool) (j : Fin T₁) (hcc' : ∀ j', j' ≠ j → c j' = c' j') (a : Fin K)
    (t : ℕ) :
    |hardInst T₁ hT₁ Δ c a t - hardInst T₁ hT₁ Δ c' a t| ≤
      (if phase T₁ hT₁ t = j then 2 * Δ else 0) := by
  unfold hardInst
  by_cases ha : a = 0
  · simp only [if_pos ha]
    by_cases hp : phase T₁ hT₁ t = j
    · rw [if_pos hp]
      rcases c (phase T₁ hT₁ t) <;> rcases c' (phase T₁ hT₁ t) <;> simp <;>
        first | linarith | (rw [abs_le]; constructor <;> linarith)
    · rw [if_neg hp, hcc' _ hp]; simp
  · simp only [if_neg ha, sub_self, abs_zero]
    split_ifs <;> linarith

lemma pr_diff {K : ℕ} [NeZero K] (T T₁ : ℕ) (hT₁ : 1 ≤ T₁) (Δ : ℝ) (hΔ : 0 < Δ)
    (π : BanditPolicy K) (c c' : Fin T₁ → Bool) (j : Fin T₁)
    (hcc' : ∀ j', j' ≠ j → c j' = c' j') (i : Fin T) :
    ∫ h, ind0 i h ∂(periodicMeasure (hardInst T₁ hT₁ Δ c) π T) -
      ∫ h, ind0 i h ∂(periodicMeasure (hardInst T₁ hT₁ Δ c') π T) ≤
      1 - Real.exp (-(Δ ^ 2 * ((T : ℝ) / T₁ + 1))) / 2 := by
  have hb := testing_bound π (hardInst T₁ hT₁ Δ c) (hardInst T₁ hT₁ Δ c')
    (fun t => if phase T₁ hT₁ t = j then 2 * Δ else 0)
    (fun a t => hardInst_diff T₁ hT₁ Δ hΔ c c' j hcc' a t) T (ind0 i) (measurable_ind0 i)
    (ind0_nonneg i) (ind0_le_one i)
  refine hb.trans ?_
  have hsum : (∑ x ∈ Finset.range T, (if phase T₁ hT₁ (x + 1) = j then 2 * Δ else 0) ^ 2) ≤
      4 * Δ ^ 2 * ((T : ℝ) / T₁ + 1) := by
    have e : ∀ x, (if phase T₁ hT₁ (x + 1) = j then 2 * Δ else 0) ^ 2 =
        if x % T₁ = (j : ℕ) then 4 * Δ ^ 2 else 0 := by
      intro x
      have : (phase T₁ hT₁ (x + 1) = j) ↔ x % T₁ = (j : ℕ) := by
        simp [phase, Fin.ext_iff]
      by_cases hx : x % T₁ = (j : ℕ)
      · rw [if_pos (this.mpr hx), if_pos hx]; ring
      · rw [if_neg (fun h => hx (this.mp h)), if_neg hx]; ring
    simp_rw [e]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := card_phase_le T T₁ hT₁ j
    nlinarith [sq_nonneg Δ]
  have : Real.exp (-(Δ ^ 2 * ((T : ℝ) / T₁ + 1))) ≤
      Real.exp (-(∑ x ∈ Finset.range T, (if phase T₁ hT₁ (x + 1) = j then 2 * Δ else 0) ^ 2) / 4) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

end PMABKeyAux

open PMABKeyAux in
theorem solution (K T T₁ : ℕ) [NeZero K] (hK : 2 ≤ K) (hT₁ : 1 ≤ T₁)
    (hA3 : Assumption3 K T (Function.update (fun _ ↦ 1) 0 T₁)) (π : BanditPolicy K) :
    ∃ μ : Fin K → ℕ → ℝ, InE2 T T₁ μ ∧ (∀ k, k ≠ 0 → ∀ t, μ k t = 1 / 2) ∧
      Real.sqrt ((T : ℝ) * T₁) / (16 * Real.exp 1) ≤ periodicRegret μ π T := by
  obtain ⟨hA1, hA2, hA3k⟩ := hA3
  have hT1 : 1 ≤ T := by omega
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hT₁r : (1 : ℝ) ≤ T₁ := by exact_mod_cast hT₁
  -- T₁ ≤ T
  have hT₁T : (T₁ : ℝ) ≤ T := by
    have h0 := hA3k 0
    simp only [Function.update_self] at h0
    set n := stageOneLength K T
    set g := gParam n
    have hg : (2 : ℝ) ≤ g := by exact_mod_cast hA2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h1 : (n : ℝ) / (2 * g) ≤ n := div_le_self hn0 (by linarith)
    have h2 : (n : ℝ) ≤ Real.sqrt ((T : ℝ) / K) := Nat.floor_le (Real.sqrt_nonneg _)
    have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    have h3 : Real.sqrt ((T : ℝ) / K) ≤ Real.sqrt T :=
      Real.sqrt_le_sqrt (div_le_self (by linarith) hKr)
    have h4 : Real.sqrt (T : ℝ) ≤ T := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith
  set N : ℝ := (T : ℝ) / T₁ + 1 with hN
  have hT₁pos : (0 : ℝ) < T₁ := by linarith
  have hN1 : 1 ≤ N := by have := div_nonneg (by linarith : (0:ℝ) ≤ T) hT₁pos.le; linarith
  have hNle : N ≤ 2 * T / T₁ := by
    have : 1 ≤ (T : ℝ) / T₁ := by rw [le_div_iff₀ hT₁pos]; linarith
    rw [hN]; field_simp at this ⊢; linarith
  have hsN : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  set Δ : ℝ := 1 / (3 * Real.sqrt N) with hΔ
  have hΔpos : 0 < Δ := by positivity
  have hΔ3 : Δ ≤ 1 / 3 := by
    rw [hΔ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hΔN : Δ ^ 2 * N = 1 / 9 := by
    rw [hΔ, div_pow, mul_pow, Real.sq_sqrt (by linarith)]; field_simp; norm_num
  -- notation
  set μc : (Fin T₁ → Bool) → Fin K → ℕ → ℝ := fun c => hardInst T₁ hT₁ Δ c with hμc
  set pr : (Fin T₁ → Bool) → Fin T → ℝ := fun c i =>
    ∫ h, ind0 i h ∂(periodicMeasure (μc c) π T) with hpr
  set gg : (Fin T₁ → Bool) → Fin T → ℝ := fun c i =>
    if c (phase T₁ hT₁ ((i : ℕ) + 1)) then 1 - pr c i else pr c i with hgg
  have hpr01 : ∀ c i, 0 ≤ pr c i ∧ pr c i ≤ 1 := by
    intro c i
    constructor
    · exact integral_nonneg (ind0_nonneg i)
    · calc pr c i ≤ ∫ _h, (1 : ℝ) ∂(periodicMeasure (μc c) π T) :=
            integral_mono (Integrable.of_bound (measurable_ind0 i).aestronglyMeasurable 1
              (ae_of_all _ (fun h => by
                rw [Real.norm_eq_abs, abs_of_nonneg (ind0_nonneg i h)]; exact ind0_le_one i h)))
              (integrable_const 1) (ind0_le_one i)
        _ = 1 := by simp
  -- per-epoch lower bound
  have hterm : ∀ c (i : Fin T), (3 * Δ / 4) * gg c i ≤
      Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μc c k ((i : ℕ) + 1)) -
        ∫ h, μc c (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure (μc c) π T) := by
    intro c i
    have hk : ∀ k, k ≠ 0 → μc c k ((i : ℕ) + 1) = 1 / 2 :=
      fun k hk => (hardInst_E2 (K := K) T T₁ hT₁ Δ hΔpos hΔ3 c).2 k hk _
    rw [integral_mean_eq (μc c) _ i _ hk]
    have hs0 := Finset.le_sup' (fun k ↦ μc c k ((i : ℕ) + 1)) (Finset.mem_univ 0)
    have hs1 := Finset.le_sup' (fun k ↦ μc c k ((i : ℕ) + 1))
      (Finset.mem_univ (⟨1, by omega⟩ : Fin K))
    have hne : (⟨1, by omega⟩ : Fin K) ≠ 0 := by
      intro h; have := congrArg Fin.val h; simp at this
    rw [hk _ hne] at hs1
    obtain ⟨hp0, hp1⟩ := hpr01 c i
    simp only [hgg]
    change (3 * Δ / 4) * (if c (phase T₁ hT₁ ((i : ℕ) + 1)) then 1 - pr c i else pr c i) ≤ _
    have hm0 : μc c 0 ((i : ℕ) + 1) = 1 / 2 +
        (if c (phase T₁ hT₁ ((i : ℕ) + 1)) then Δ else -Δ) +
        (if ((phase T₁ hT₁ ((i : ℕ) + 1) : ℕ) = 0) then Δ / 4 else 0) := by
      simp [hμc, hardInst]
    change _ ≤ _ - (1 / 2 + (_ - 1 / 2) * pr c i)
    set m₀ := μc c 0 ((i : ℕ) + 1) with hm₀
    set S := Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μc c k ((i : ℕ) + 1)) with hS
    have hbump : 0 ≤ (if ((phase T₁ hT₁ ((i : ℕ) + 1) : ℕ) = 0) then Δ / 4 else 0) ∧
        (if ((phase T₁ hT₁ ((i : ℕ) + 1) : ℕ) = 0) then Δ / 4 else 0) ≤ Δ / 4 := by
      split_ifs <;> constructor <;> linarith
    by_cases hcb : c (phase T₁ hT₁ ((i : ℕ) + 1)) = true
    · rw [if_pos hcb]
      have : Δ ≤ m₀ - 1 / 2 := by rw [hm0, if_pos hcb]; linarith [hbump.1]
      nlinarith
    · rw [if_neg hcb]
      have : m₀ - 1 / 2 ≤ -(3 * Δ / 4) := by rw [hm0, if_neg hcb]; linarith [hbump.2]
      nlinarith
  -- regret lower bound for each instance
  have hreg : ∀ c, ∑ i : Fin T, (3 * Δ / 4) * gg c i ≤ periodicRegret (μc c) π T :=
    fun c => Finset.sum_le_sum (fun i _ => hterm c i)
  -- pairing
  set κ : ℝ := Real.exp (-(Δ ^ 2 * N)) / 2 with hκ
  have hpair : ∀ i : Fin T, (Fintype.card (Fin T₁ → Bool) : ℝ) * (κ / 2) ≤ ∑ c, gg c i := by
    intro i
    set j := phase T₁ hT₁ ((i : ℕ) + 1) with hj
    let fl : (Fin T₁ → Bool) → (Fin T₁ → Bool) := fun c => Function.update c j (!(c j))
    have hfl : Function.Involutive fl := by
      intro c; simp [fl]
    have hdiff : ∀ c, ∀ j', j' ≠ j → c j' = fl c j' := by
      intro c j' hj'; simp [fl, Function.update_of_ne hj']
    have hsum2 : ∑ c, gg c i = ∑ c, gg (fl c) i :=
      (Equiv.sum_comp hfl.toPerm (fun c => gg c i)).symm
    have hle : ∀ c, κ ≤ gg c i + gg (fl c) i := by
      intro c
      have hflj : fl c j = !(c j) := by simp [fl]
      simp only [hgg]
      rw [hflj]
      rcases hc : c j
      · simp only [Bool.not_false, if_true]
        rw [← hj] at *
        simp only [hc, Bool.false_eq_true, if_false]
        have := pr_diff T T₁ hT₁ Δ hΔpos π (fl c) c j
          (fun j' hj' => (hdiff c j' hj').symm) i
        simp only [hκ]
        have : pr (fl c) i - pr c i ≤ 1 - Real.exp (-(Δ ^ 2 * N)) / 2 := this
        linarith
      · simp only [Bool.not_true, Bool.false_eq_true, if_false]
        rw [← hj] at *
        simp only [hc, if_true]
        have := pr_diff T T₁ hT₁ Δ hΔpos π c (fl c) j (hdiff c) i
        have : pr c i - pr (fl c) i ≤ 1 - Real.exp (-(Δ ^ 2 * N)) / 2 := this
        simp only [hκ]
        linarith
    have : (Fintype.card (Fin T₁ → Bool) : ℝ) * κ ≤ ∑ c, gg c i + ∑ c, gg (fl c) i := by
      rw [← Finset.sum_add_distrib]
      calc (Fintype.card (Fin T₁ → Bool) : ℝ) * κ = ∑ _c : Fin T₁ → Bool, κ := by
            simp [Finset.sum_const, Finset.card_univ]
        _ ≤ _ := Finset.sum_le_sum (fun c _ => hle c)
    rw [← hsum2] at this
    linarith
  -- average
  set Cn : ℝ := (Fintype.card (Fin T₁ → Bool) : ℝ) with hCn
  have hCnpos : 0 < Cn := by rw [hCn]; exact_mod_cast Fintype.card_pos
  set B : ℝ := T * (3 * Δ / 4) * (κ / 2) with hB
  have htot : Cn * B ≤ ∑ c, periodicRegret (μc c) π T := by
    calc Cn * B = ∑ i : Fin T, (3 * Δ / 4) * (Cn * (κ / 2)) := by
          simp [Finset.sum_const, hB]; ring
      _ ≤ ∑ i : Fin T, (3 * Δ / 4) * ∑ c, gg c i :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpair i) (by positivity))
      _ = ∑ c, ∑ i : Fin T, (3 * Δ / 4) * gg c i := by
          rw [Finset.sum_comm]; simp [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun c _ => hreg c)
  obtain ⟨c, hc⟩ : ∃ c, B ≤ periodicRegret (μc c) π T := by
    by_contra hcon
    push Not at hcon
    have : ∑ c, periodicRegret (μc c) π T < ∑ _c : Fin T₁ → Bool, B :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => hcon c)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hCn] at this
    linarith
  refine ⟨μc c, (hardInst_E2 T T₁ hT₁ Δ hΔpos hΔ3 c).1, (hardInst_E2 T T₁ hT₁ Δ hΔpos hΔ3 c).2,
    le_trans ?_ hc⟩
  -- numerics
  rw [hB, hκ, hΔN, hΔ]
  have hsq : Real.sqrt ((T : ℝ) * T₁) * Real.sqrt N ≤ 3 / 2 * T := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_le_left (by positivity)]
    have : (T : ℝ) * T₁ * N = T * T + T * T₁ := by rw [hN]; field_simp
    rw [this]; nlinarith
  have hexp : 3 / 2 ≤ Real.exp 1 * Real.exp (-(1 / 9)) := by
    rw [← Real.exp_add]
    have := Real.add_one_le_exp (1 + -(1 / 9) : ℝ)
    linarith
  have hsNpos : 0 < Real.sqrt N := by linarith
  have he1 : 0 < Real.exp 1 := Real.exp_pos 1
  rw [div_le_iff₀ (by positivity)]
  have : (T : ℝ) * (3 * (1 / (3 * Real.sqrt N)) / 4) * (Real.exp (-(1 / 9)) / 2 / 2) *
      (16 * Real.exp 1) = T * (Real.exp 1 * Real.exp (-(1 / 9))) / Real.sqrt N := by
    field_simp; ring
  rw [this, le_div_iff₀ hsNpos]
  nlinarith
