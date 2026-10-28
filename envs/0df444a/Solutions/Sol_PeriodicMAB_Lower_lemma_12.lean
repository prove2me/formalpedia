-- Prove2me | solution 1 for PeriodicMAB.Lower.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T22:20:13.417638+00:00
-- url     : https://prove2.me/submissions/efe9e428-5c25-47c2-a7b6-def0043e6cb6

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model
import Definitions.Def_banditRegret
import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition

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

lemma banditMeasure_eq_periodic {K : ℕ} (m : Fin K → ℝ) (π : BanditPolicy K) (n : ℕ) :
    banditMeasure (gaussianBandit m) π n = periodicMeasure (fun a _ => m a) π n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [banditMeasure, periodicMeasure, ih]

lemma armPullCount_eq_sum {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    (armPullCount i h : ℝ) = ∑ t : Fin n, (if (h t).1 = i then (1 : ℝ) else 0) := by
  unfold armPullCount
  rw [Set.toFinset_setOf, Finset.card_filter]
  push_cast
  rfl

lemma measurable_armPullCount {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => (armPullCount i h : ℝ)) := by
  simp_rw [armPullCount_eq_sum]
  exact Finset.measurable_sum _ (fun t _ =>
    (Measurable.of_discrete (f := fun a : Fin K => if a = i then (1 : ℝ) else 0)).comp
      (measurable_fst.comp (measurable_pi_apply t)))

lemma sum_armPullCount {K n : ℕ} (h : BanditHistory K n) :
    ∑ i : Fin K, (armPullCount i h : ℝ) = n := by
  simp_rw [armPullCount_eq_sum]
  rw [Finset.sum_comm]
  simp

lemma armPullCount_le {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    (armPullCount i h : ℝ) ≤ n := by
  rw [armPullCount_eq_sum]
  calc ∑ t : Fin n, (if (h t).1 = i then (1 : ℝ) else 0) ≤ ∑ _t : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun t _ => by split_ifs <;> norm_num)
    _ = n := by simp

lemma gaussianBandit_mean {K : ℕ} (m : Fin K → ℝ) (i : Fin K) :
    banditArmMean (gaussianBandit m) i = m i := by
  simp [banditArmMean, gaussianBandit, integral_id_gaussianReal]

lemma gaussianBandit_int {K : ℕ} (m : Fin K → ℝ) (i : Fin K) :
    Integrable id ((gaussianBandit m).P i) := by
  simp only [gaussianBandit]
  exact memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)

lemma optMean_eq {K : ℕ} [NeZero K] (m : Fin K → ℝ) (M : ℝ) (hle : ∀ i, m i ≤ M)
    (hex : ∃ i, m i = M) : banditOptimalMean (gaussianBandit m) = M := by
  unfold banditOptimalMean
  simp_rw [gaussianBandit_mean]
  obtain ⟨i, hi⟩ := hex
  apply le_antisymm (ciSup_le hle)
  rw [← hi]
  exact le_ciSup (Set.finite_range m).bddAbove i

end PMABKeyAux

open PMABKeyAux in
theorem solution (K T : ℕ) [NeZero K] (hK : 2 ≤ K) (π : BanditPolicy K) :
    ∃ μ₁ ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt T / (8 * Real.sqrt 2 * Real.exp 1) ≤
        banditRegret (gaussianBandit (Function.update (fun _ ↦ (1 / 2 : ℝ)) 0 μ₁)) π T := by
  have hne : (⟨1, by omega⟩ : Fin K) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  -- regret formula for instance 1/2 + s
  set E : ℝ → ℝ := fun μ₁ => ∫ h, (armPullCount 0 h : ℝ)
    ∂(banditMeasure (gaussianBandit (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 μ₁)) π T) with hE
  have hsumE : ∀ μ₁ : ℝ, ∑ i : Fin K, ∫ h, (armPullCount i h : ℝ)
      ∂(banditMeasure (gaussianBandit (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 μ₁)) π T) = T := by
    intro μ₁
    rw [← integral_finset_sum _ (fun i _ => Integrable.of_bound
      (measurable_armPullCount i).aestronglyMeasurable T (ae_of_all _ (fun h => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]; exact armPullCount_le i h)))]
    simp_rw [sum_armPullCount]
    simp
  have hregPlus : ∀ Δ : ℝ, 0 ≤ Δ →
      banditRegret (gaussianBandit (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 (1 / 2 + Δ))) π T =
        Δ * (T - E (1 / 2 + Δ)) := by
    intro Δ hΔ
    rw [bandit_regret_decomposition _ (gaussianBandit_int _) π T]
    have hopt := optMean_eq (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 (1 / 2 + Δ)) (1 / 2 + Δ)
      (fun i => by
        by_cases hi : i = 0
        · subst hi; simp
        · simp [Function.update_of_ne hi]; linarith) ⟨0, by simp⟩
    have hgap : ∀ i, banditGap (gaussianBandit (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0
        (1 / 2 + Δ))) i = if i = 0 then 0 else Δ := by
      intro i
      unfold banditGap
      rw [hopt, gaussianBandit_mean]
      by_cases hi : i = 0
      · subst hi; simp
      · simp [Function.update_of_ne hi, hi]
    simp_rw [hgap]
    have := hsumE (1 / 2 + Δ)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin K))] at this
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin K))]
    simp only [if_true, zero_mul, zero_add]
    rw [Finset.sum_congr rfl (fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi)]),
      ← Finset.mul_sum]
    congr 1
    simp only [hE]
    linarith
  have hregMinus : ∀ Δ : ℝ, 0 ≤ Δ →
      banditRegret (gaussianBandit (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 (1 / 2 - Δ))) π T =
        Δ * E (1 / 2 - Δ) := by
    intro Δ hΔ
    rw [bandit_regret_decomposition _ (gaussianBandit_int _) π T]
    have hopt := optMean_eq (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 (1 / 2 - Δ)) (1 / 2)
      (fun i => by
        by_cases hi : i = 0
        · subst hi; simp; linarith
        · simp [Function.update_of_ne hi]) ⟨⟨1, by omega⟩, by simp [Function.update_of_ne hne]⟩
    have hgap : ∀ i, banditGap (gaussianBandit (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0
        (1 / 2 - Δ))) i = if i = 0 then Δ else 0 := by
      intro i
      unfold banditGap
      rw [hopt, gaussianBandit_mean]
      by_cases hi : i = 0
      · subst hi; simp
      · simp [Function.update_of_ne hi, hi]
    simp_rw [hgap]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin K))]
    simp only [if_true]
    rw [Finset.sum_congr rfl (fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi)])]
    simp [hE]
  -- trivial case T = 0
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · refine ⟨1 / 2 + 0, by constructor <;> norm_num, ?_⟩
    rw [hregPlus 0 le_rfl]
    subst hT0
    simp
  -- main case
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  set Δ : ℝ := 1 / (2 * Real.sqrt T) with hΔ
  have hsT : 1 ≤ Real.sqrt T := by rw [Real.one_le_sqrt]; exact hTr
  have hΔpos : 0 < Δ := by positivity
  have hΔ2 : Δ ≤ 1 / 2 := by
    rw [hΔ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hΔT : Δ ^ 2 * T = 1 / 4 := by
    rw [hΔ, div_pow, mul_pow, Real.sq_sqrt (by linarith)]; field_simp; norm_num
  -- testing bound
  set f : BanditHistory K T → ℝ := fun h => (armPullCount 0 h : ℝ) / T with hf
  have hfm : Measurable f := (measurable_armPullCount 0).div_const _
  have hf0 : ∀ h, 0 ≤ f h := fun h => div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hf1 : ∀ h, f h ≤ 1 := fun h => (div_le_one (by linarith)).mpr (armPullCount_le 0 h)
  have htest := testing_bound π
    (fun a _ => Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 (1 / 2 + Δ) a)
    (fun a _ => Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 (1 / 2 - Δ) a)
    (fun _ => 2 * Δ) (fun a t => by
      by_cases ha : a = 0
      · subst ha; simp; rw [abs_of_nonneg (by linarith)]; linarith
      · simp [Function.update_of_ne ha]; linarith) T f hfm hf0 hf1
  rw [← banditMeasure_eq_periodic, ← banditMeasure_eq_periodic] at htest
  have hEf : ∀ μ₁ : ℝ, ∫ h, f h ∂(banditMeasure (gaussianBandit
      (Function.update (fun _ : Fin K ↦ (1 / 2 : ℝ)) 0 μ₁)) π T) = E μ₁ / T := by
    intro μ₁; simp only [hf, hE]; rw [integral_div]
  rw [hEf, hEf] at htest
  have hsumD : (∑ i ∈ Finset.range T, (2 * Δ) ^ 2) / 4 = 1 / 4 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hΔT]; ring
  rw [show -(∑ i ∈ Finset.range T, (fun _ => 2 * Δ) (i + 1) ^ 2) / 4 =
    -((∑ i ∈ Finset.range T, (2 * Δ) ^ 2) / 4) by simp; ring, hsumD] at htest
  have hsum2 : Δ * T * (Real.exp (-(1 / 4)) / 2) ≤
      Δ * (T - E (1 / 2 + Δ)) + Δ * E (1 / 2 - Δ) := by
    have h1 : E (1 / 2 + Δ) - E (1 / 2 - Δ) ≤ T * (1 - Real.exp (-(1 / 4)) / 2) := by
      have := mul_le_mul_of_nonneg_left htest (by linarith : (0 : ℝ) ≤ T)
      rw [mul_sub, mul_div_cancel₀ _ (by linarith), mul_div_cancel₀ _ (by linarith)] at this
      linarith
    nlinarith
  -- pick the better instance
  set B : ℝ := Δ * T * (Real.exp (-(1 / 4)) / 2) / 2 with hB
  have hgoal : Real.sqrt T / (8 * Real.sqrt 2 * Real.exp 1) ≤ B := by
    rw [hB, hΔ]
    have hs2 : 1 ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
    have he : 1 ≤ Real.exp 1 * Real.exp (-(1 / 4)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by norm_num)
    have hsTpos : 0 < Real.sqrt T := by linarith
    have : 1 / (2 * Real.sqrt T) * T * (Real.exp (-(1 / 4)) / 2) / 2 =
        Real.sqrt T * Real.exp (-(1 / 4)) / 8 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ T by linarith)
      field_simp
      nlinarith
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    have h3 : Real.sqrt T * 8 ≤ Real.sqrt T * Real.exp (-(1 / 4)) * (8 * Real.sqrt 2 * Real.exp 1) := by
      have : 1 ≤ Real.exp (-(1 / 4)) * Real.exp 1 * Real.sqrt 2 := by nlinarith [Real.exp_pos (-(1/4))]
      nlinarith
    linarith
  by_cases hcase : B ≤ Δ * (T - E (1 / 2 + Δ))
  · refine ⟨1 / 2 + Δ, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hregPlus Δ hΔpos.le]; linarith
  · refine ⟨1 / 2 - Δ, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hregMinus Δ hΔpos.le]; linarith
