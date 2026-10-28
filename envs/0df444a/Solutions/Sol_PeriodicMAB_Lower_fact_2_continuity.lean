-- Prove2me | solution 1 for PeriodicMAB.Lower.fact_2_continuity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:56:04.884338+00:00
-- url     : https://prove2.me/submissions/df72ad3e-85d4-48fc-80ad-2f8d58625e06

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm PeriodicMAB.Lower

namespace PMABContAux

lemma abs_sub_eq_add_sub_min (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

lemma continuous_gaussianPDFReal_mean (y : ℝ) :
    Continuous (fun c : ℝ => gaussianPDFReal c 1 y) := by
  unfold gaussianPDFReal; fun_prop

lemma integrable_min_pdf (a b : ℝ) :
    Integrable (fun y => min (gaussianPDFReal a 1 y) (gaussianPDFReal b 1 y)) := by
  refine Integrable.mono' (integrable_gaussianPDFReal a 1)
    ((measurable_gaussianPDFReal a 1).min (measurable_gaussianPDFReal b 1)).aestronglyMeasurable
    (ae_of_all _ (fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (gaussianPDFReal_nonneg _ _ _)
    (gaussianPDFReal_nonneg _ _ _))]
  exact min_le_left _ _

lemma integral_abs_pdf_eq (a b : ℝ) :
    ∫ y, |gaussianPDFReal a 1 y - gaussianPDFReal b 1 y| =
      2 - 2 * ∫ y, min (gaussianPDFReal a 1 y) (gaussianPDFReal b 1 y) := by
  simp_rw [abs_sub_eq_add_sub_min]
  rw [integral_sub (f := fun y => gaussianPDFReal a 1 y + gaussianPDFReal b 1 y)
      (g := fun y => 2 * min (gaussianPDFReal a 1 y) (gaussianPDFReal b 1 y))
      ((integrable_gaussianPDFReal a 1).add (integrable_gaussianPDFReal b 1))
      ((integrable_min_pdf a b).const_mul 2),
    integral_add (integrable_gaussianPDFReal a 1) (integrable_gaussianPDFReal b 1),
    integral_gaussianPDFReal_eq_one a one_ne_zero, integral_gaussianPDFReal_eq_one b one_ne_zero,
    integral_const_mul]
  ring

lemma tendsto_integral_abs_pdf :
    Tendsto (fun c : ℝ => ∫ y, |gaussianPDFReal 0 1 y - gaussianPDFReal c 1 y|) (𝓝 0) (𝓝 0) := by
  simp_rw [integral_abs_pdf_eq]
  have hlim : Tendsto (fun c : ℝ => ∫ y, min (gaussianPDFReal 0 1 y) (gaussianPDFReal c 1 y))
      (𝓝 0) (𝓝 (∫ y, min (gaussianPDFReal 0 1 y) (gaussianPDFReal 0 1 y))) := by
    refine tendsto_integral_filter_of_dominated_convergence (gaussianPDFReal 0 1) ?_ ?_
      (integrable_gaussianPDFReal 0 1) ?_
    · exact Eventually.of_forall (fun c => ((measurable_gaussianPDFReal 0 1).min
        (measurable_gaussianPDFReal c 1)).aestronglyMeasurable)
    · refine Eventually.of_forall (fun c => ae_of_all _ (fun y => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (gaussianPDFReal_nonneg _ _ _)
        (gaussianPDFReal_nonneg _ _ _))]
      exact min_le_left _ _
    · exact ae_of_all _ (fun y => tendsto_const_nhds.min
        ((continuous_gaussianPDFReal_mean y).tendsto 0))
  simp only [min_self, integral_gaussianPDFReal_eq_one 0 one_ne_zero] at hlim
  convert (tendsto_const_nhds (x := (2 : ℝ))).sub (hlim.const_mul 2) using 2
  norm_num

lemma integral_abs_pdf_shift (a b : ℝ) :
    ∫ y, |gaussianPDFReal a 1 y - gaussianPDFReal b 1 y| =
      ∫ y, |gaussianPDFReal 0 1 y - gaussianPDFReal (b - a) 1 y| := by
  rw [← integral_sub_right_eq_self
    (fun y => |gaussianPDFReal 0 1 y - gaussianPDFReal (b - a) 1 y|) a]
  congr 1
  funext y
  simp only [gaussianPDFReal_sub]
  congr 3 <;> ring

lemma gauss_unif (η : ℝ) (hη : 0 < η) :
    ∃ d > 0, ∀ a b : ℝ, |a - b| < d →
      ∫ y, |gaussianPDFReal a 1 y - gaussianPDFReal b 1 y| < η := by
  obtain ⟨d, hd, hball⟩ := Metric.tendsto_nhds_nhds.mp tendsto_integral_abs_pdf η hη
  refine ⟨d, hd, fun a b hab => ?_⟩
  rw [integral_abs_pdf_shift]
  have := hball (x := b - a) (by rw [Real.dist_eq, sub_zero, abs_sub_comm]; exact hab)
  rw [Real.dist_eq, sub_zero] at this
  exact lt_of_abs_lt this

lemma gauss_integral_diff (a b M : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hM : ∀ y, |φ y| ≤ M) :
    |∫ y, φ y ∂(gaussianReal a 1) - ∫ y, φ y ∂(gaussianReal b 1)| ≤
      M * ∫ y, |gaussianPDFReal a 1 y - gaussianPDFReal b 1 y| := by
  have hint : ∀ c, Integrable (fun y => gaussianPDFReal c 1 y • φ y) := fun c =>
    Integrable.mono' ((integrable_gaussianPDFReal c 1).const_mul M)
      ((measurable_gaussianPDFReal c 1).mul hφ).aestronglyMeasurable
      (ae_of_all _ (fun y => by
        rw [smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
          mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM y) (gaussianPDFReal_nonneg _ _ _)))
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_sub (hint a) (hint b),
    ← integral_const_mul]
  have := norm_integral_le_of_norm_le
    (f := fun y => gaussianPDFReal a 1 y • φ y - gaussianPDFReal b 1 y • φ y)
    (((integrable_gaussianPDFReal a 1).sub (integrable_gaussianPDFReal b 1)).abs.const_mul M)
    (ae_of_all _ (fun y => by
      rw [smul_eq_mul, smul_eq_mul, ← sub_mul, Real.norm_eq_abs, abs_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _)))
  rwa [Real.norm_eq_abs] at this


lemma step_integral_diff {K : ℕ} (π : BanditPolicy K) (m₁ m₂ : Fin K → ℝ) (n : ℕ)
    (h : BanditHistory K n) (g : Fin K × ℝ → ℝ) (hg : Measurable g) (M η : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x, |g x| ≤ M)
    (hη : ∀ a, ∫ y, |gaussianPDFReal (m₁ a) 1 y - gaussianPDFReal (m₂ a) 1 y| ≤ η) :
    |∫ x, g x ∂(banditStepKernel (gaussianBandit m₁) π n h) -
      ∫ x, g x ∂(banditStepKernel (gaussianBandit m₂) π n h)| ≤ M * η := by
  have hint : ∀ m : Fin K → ℝ, Integrable g (banditStepKernel (gaussianBandit m) π n h) :=
    fun m => Integrable.of_bound hg.aestronglyMeasurable M
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hM x))
  have hrw : ∀ m : Fin K → ℝ, ∫ x, g x ∂(banditStepKernel (gaussianBandit m) π n h) =
      ∫ a, ∫ y, g (a, y) ∂(gaussianReal (m a) 1) ∂(π.select n h) := by
    intro m
    have := hint m
    simp only [banditStepKernel] at this ⊢
    rw [ProbabilityTheory.integral_compProd this]
    rfl
  rw [hrw, hrw, ← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  have := norm_integral_le_of_norm_le_const (μ := π.select n h)
    (f := fun a => ∫ y, g (a, y) ∂(gaussianReal (m₁ a) 1) - ∫ y, g (a, y) ∂(gaussianReal (m₂ a) 1))
    (C := M * η) (ae_of_all _ (fun a => by
      rw [Real.norm_eq_abs]
      refine le_trans (gauss_integral_diff (m₁ a) (m₂ a) M (fun y => g (a, y))
        (hg.comp measurable_prodMk_left) (fun y => hM _)) ?_
      exact mul_le_mul_of_nonneg_left (hη a) hM0))
  simpa [Real.norm_eq_abs] using this

lemma periodicMeasure_integral_diff {K : ℕ} (π : BanditPolicy K) (μ₁ μ₂ : Fin K → ℕ → ℝ)
    (η : ℝ)
    (hη : ∀ a t, 1 ≤ t →
      ∫ y, |gaussianPDFReal (μ₁ a t) 1 y - gaussianPDFReal (μ₂ a t) 1 y| ≤ η) (n : ℕ) :
    ∀ (f : BanditHistory K n → ℝ) (M : ℝ), 0 ≤ M → Measurable f → (∀ h, |f h| ≤ M) →
      |∫ h, f h ∂(periodicMeasure μ₁ π n) - ∫ h, f h ∂(periodicMeasure μ₂ π n)| ≤
        n * (M * η) := by
  induction n with
  | zero =>
    intro f M _ _ _
    simp [periodicMeasure]
  | succ n ih =>
    intro f M hM0 hf hM
    have hfs : Measurable (fun p : BanditHistory K n × (Fin K × ℝ) =>
        f (Fin.snoc (α := fun _ ↦ Fin K × ℝ) p.1 p.2)) := hf.comp measurable_banditHistorySnoc
    have key : ∀ μ : Fin K → ℕ → ℝ, ∫ h, f h ∂(periodicMeasure μ π (n + 1)) =
        ∫ h, (∫ x, f (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h x)
          ∂(banditStepKernel (gaussianBandit (fun a ↦ μ a (n + 1))) π n h))
          ∂(periodicMeasure μ π n) := by
      intro μ
      simp only [periodicMeasure]
      rw [integral_map measurable_banditHistorySnoc.aemeasurable hf.aestronglyMeasurable,
        Measure.integral_compProd (Integrable.of_bound hfs.aestronglyMeasurable M
          (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hM _)))]
    rw [key, key]
    set F : (Fin K → ℕ → ℝ) → BanditHistory K n → ℝ := fun μ h =>
      ∫ x, f (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h x)
          ∂(banditStepKernel (gaussianBandit (fun a ↦ μ a (n + 1))) π n h) with hF
    have hFm : ∀ μ, Measurable (F μ) := fun μ =>
      (hfs.stronglyMeasurable.integral_kernel_prod_right'
        (κ := banditStepKernel (gaussianBandit (fun a ↦ μ a (n + 1))) π n)).measurable
    have hFb : ∀ μ h, |F μ h| ≤ M := by
      intro μ h
      have := norm_integral_le_of_norm_le_const
        (μ := banditStepKernel (gaussianBandit (fun a ↦ μ a (n + 1))) π n h)
        (f := fun x => f (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h x)) (C := M)
        (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hM _))
      simpa [Real.norm_eq_abs] using this
    have h1 := ih (F μ₁) M hM0 (hFm μ₁) (hFb μ₁)
    have hdiff : ∀ h, |F μ₁ h - F μ₂ h| ≤ M * η := by
      intro h
      exact step_integral_diff π _ _ n h _ (hf.comp (measurable_banditHistorySnoc.comp
        (measurable_const.prodMk measurable_id))) M η hM0 (fun x => hM _)
        (fun a => hη a (n + 1) (by omega))
    have hint : ∀ μ, Integrable (F μ) (periodicMeasure μ₂ π n) := fun μ =>
      Integrable.of_bound (hFm μ).aestronglyMeasurable M
        (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hFb μ x))
    have h2 : |∫ h, F μ₁ h ∂(periodicMeasure μ₂ π n) - ∫ h, F μ₂ h ∂(periodicMeasure μ₂ π n)|
        ≤ M * η := by
      rw [← integral_sub (hint μ₁) (hint μ₂)]
      have := norm_integral_le_of_norm_le_const (μ := periodicMeasure μ₂ π n)
        (f := fun h => F μ₁ h - F μ₂ h) (C := M * η)
        (ae_of_all _ (fun h => by rw [Real.norm_eq_abs]; exact hdiff h))
      simpa [Real.norm_eq_abs] using this
    have := abs_sub_le (∫ h, F μ₁ h ∂(periodicMeasure μ₁ π n))
      (∫ h, F μ₁ h ∂(periodicMeasure μ₂ π n)) (∫ h, F μ₂ h ∂(periodicMeasure μ₂ π n))
    push_cast
    linarith

lemma periodic_rep (f : ℕ → ℝ) (P : ℕ) (hP : 0 < P) (h : ∀ t, 1 ≤ t → f (t + P) = f t) :
    ∀ t, 1 ≤ t → f t = f ((t - 1) % P + 1) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    by_cases hlt : t - 1 < P
    · rw [Nat.mod_eq_of_lt hlt]; congr 1; omega
    · have ht' : 1 ≤ t - P := by omega
      have e1 : t = (t - P) + P := by omega
      rw [e1, h _ ht', ih (t - P) (by omega) ht']
      congr 2
      have : t - P + P - 1 = (t - P - 1) + P := by omega
      rw [this, Nat.add_mod_right]

lemma pointwise_of_instDist {K : ℕ} (Tper : Fin K → ℕ) (hTper : ∀ k, 1 ≤ Tper k)
    (μ₁ μ₂ : Fin K → ℕ → ℝ)
    (hp₁ : ∀ k t, 1 ≤ t → μ₁ k (t + Tper k) = μ₁ k t)
    (hp₂ : ∀ k t, 1 ≤ t → μ₂ k (t + Tper k) = μ₂ k t) :
    ∀ k t, 1 ≤ t → |μ₁ k t - μ₂ k t| ≤ instDist Tper μ₁ μ₂ := by
  intro k t ht
  rw [periodic_rep (μ₁ k) (Tper k) (hTper k) (hp₁ k) t ht,
    periodic_rep (μ₂ k) (Tper k) (hTper k) (hp₂ k) t ht]
  set p := (t - 1) % Tper k + 1 with hp
  have hpmem : p ∈ Finset.Icc 1 (Tper k) := by
    rw [Finset.mem_Icc]
    have := Nat.mod_lt (t - 1) (hTper k)
    omega
  unfold instDist
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  calc (μ₁ k p - μ₂ k p) ^ 2 ≤ ∑ q ∈ Finset.Icc 1 (Tper k), (μ₁ k q - μ₂ k q) ^ 2 :=
        Finset.single_le_sum (f := fun q => (μ₁ k q - μ₂ k q) ^ 2)
          (fun q _ => sq_nonneg _) hpmem
    _ ≤ ∑ j, ∑ q ∈ Finset.Icc 1 (Tper j), (μ₁ j q - μ₂ j q) ^ 2 :=
        Finset.single_le_sum (f := fun j => ∑ q ∈ Finset.Icc 1 (Tper j), (μ₁ j q - μ₂ j q) ^ 2)
          (fun j _ => Finset.sum_nonneg (fun q _ => sq_nonneg _)) (Finset.mem_univ k)

lemma props_of_class {K T : ℕ} [NeZero K] (Tper : Fin K → ℕ) (μ : Fin K → ℕ → ℝ)
    (hμ : InE2 T (Tper 0) μ ∨ InE3 T Tper μ) :
    (∀ k t, 1 ≤ t → μ k (t + Tper k) = μ k t) ∧
      (∀ k t, 1 ≤ t → t ≤ T → μ k t ∈ Set.Icc (0 : ℝ) 1) := by
  rcases hμ with ⟨h0, hst, hb⟩ | ⟨hper, hb⟩
  · refine ⟨fun k t ht => ?_, hb⟩
    by_cases hk : k = 0
    · subst hk; exact h0.2.1 t ht
    · rw [hst k hk (t + Tper k) (by omega), hst k hk t ht]
  · exact ⟨fun k t ht => (hper k).2.1 t ht, hb⟩

lemma sup'_diff {K : ℕ} [NeZero K] (f g : Fin K → ℝ) (d : ℝ) (h : ∀ k, |f k - g k| ≤ d) :
    |Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.sup' Finset.univ_nonempty g| ≤ d := by
  rw [abs_le]
  constructor
  · have : Finset.univ.sup' Finset.univ_nonempty g ≤
        Finset.univ.sup' Finset.univ_nonempty f + d := by
      refine Finset.sup'_le _ _ (fun k _ => ?_)
      have := Finset.le_sup' f (Finset.mem_univ k)
      have := (abs_le.mp (h k)).1
      linarith
    linarith
  · have : Finset.univ.sup' Finset.univ_nonempty f ≤
        Finset.univ.sup' Finset.univ_nonempty g + d := by
      refine Finset.sup'_le _ _ (fun k _ => ?_)
      have := Finset.le_sup' g (Finset.mem_univ k)
      have := (abs_le.mp (h k)).2
      linarith
    linarith

end PMABContAux

open PMABContAux in
theorem solution (K T : ℕ) [NeZero K] (Tper : Fin K → ℕ) (hK : 2 ≤ K)
    (hTper : ∀ k, 1 ≤ Tper k) (μ₁ : Fin K → ℕ → ℝ)
    (hμ₁ : InE2 T (Tper 0) μ₁ ∨ InE3 T Tper μ₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (π : BanditPolicy K) (μ₂ : Fin K → ℕ → ℝ),
      (InE2 T (Tper 0) μ₂ ∨ InE3 T Tper μ₂) → instDist Tper μ₁ μ₂ < δ →
        |periodicRegret μ₁ π T - periodicRegret μ₂ π T| < ε := by
  set Tr : ℝ := (T : ℝ) with hTr
  have hTr0 : 0 ≤ Tr := by positivity
  set η : ℝ := ε / (4 * (Tr * Tr + 1)) with hη
  have hηpos : 0 < η := div_pos hε (by positivity)
  obtain ⟨d₀, hd₀, hgauss⟩ := gauss_unif η hηpos
  set d : ℝ := min d₀ (ε / (4 * (Tr + 1))) with hd
  have hdpos : 0 < d := lt_min hd₀ (div_pos hε (by positivity))
  refine ⟨d, hdpos, fun π μ₂ hμ₂ hdist => ?_⟩
  obtain ⟨hp₁, hb₁⟩ := props_of_class Tper μ₁ hμ₁
  obtain ⟨hp₂, hb₂⟩ := props_of_class Tper μ₂ hμ₂
  have hpt : ∀ k t, 1 ≤ t → |μ₁ k t - μ₂ k t| ≤ d := fun k t ht =>
    ((pointwise_of_instDist Tper hTper μ₁ μ₂ hp₁ hp₂ k t ht).trans hdist.le)
  have hηall : ∀ a t, 1 ≤ t →
      ∫ y, |gaussianPDFReal (μ₁ a t) 1 y - gaussianPDFReal (μ₂ a t) 1 y| ≤ η := fun a t ht =>
    (hgauss _ _ (lt_of_lt_of_le (lt_of_le_of_lt
      (pointwise_of_instDist Tper hTper μ₁ μ₂ hp₁ hp₂ a t ht) hdist) (min_le_left _ _))).le
  have hterm : ∀ i : Fin T,
      |(Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₁ k ((i : ℕ) + 1)) -
          ∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T)) -
        (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₂ k ((i : ℕ) + 1)) -
          ∫ h, μ₂ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₂ π T))| ≤ d + d + Tr * η := by
    intro i
    have hi1 : 1 ≤ (i : ℕ) + 1 := by omega
    have hiT : (i : ℕ) + 1 ≤ T := i.isLt
    have hA := sup'_diff (fun k ↦ μ₁ k ((i : ℕ) + 1)) (fun k ↦ μ₂ k ((i : ℕ) + 1)) d
      (fun k => hpt k _ hi1)
    have hgm : ∀ μ : Fin K → ℕ → ℝ,
        Measurable (fun h : BanditHistory K T => μ (h i).1 ((i : ℕ) + 1)) := fun μ =>
      (Measurable.of_discrete (f := fun a : Fin K => μ a ((i : ℕ) + 1))).comp
        (measurable_fst.comp (measurable_pi_apply i))
    have hbd : ∀ μ : Fin K → ℕ → ℝ, (∀ k t, 1 ≤ t → t ≤ T → μ k t ∈ Set.Icc (0 : ℝ) 1) →
        ∀ h : BanditHistory K T, |μ (h i).1 ((i : ℕ) + 1)| ≤ 1 := by
      intro μ hb h
      obtain ⟨h0, h1⟩ := hb (h i).1 _ hi1 hiT
      rw [abs_le]; constructor <;> linarith
    have hB := periodicMeasure_integral_diff π μ₁ μ₂ η hηall T
      (fun h => μ₂ (h i).1 ((i : ℕ) + 1)) 1 zero_le_one (hgm μ₂) (hbd μ₂ hb₂)
    have hint : ∀ μ : Fin K → ℕ → ℝ, (∀ k t, 1 ≤ t → t ≤ T → μ k t ∈ Set.Icc (0 : ℝ) 1) →
        Integrable (fun h : BanditHistory K T => μ (h i).1 ((i : ℕ) + 1))
          (periodicMeasure μ₁ π T) := fun μ hb =>
      Integrable.of_bound (hgm μ).aestronglyMeasurable 1
        (ae_of_all _ (fun h => by rw [Real.norm_eq_abs]; exact hbd μ hb h))
    have hC : |∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T) -
        ∫ h, μ₂ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T)| ≤ d := by
      rw [← integral_sub (hint μ₁ hb₁) (hint μ₂ hb₂)]
      have := norm_integral_le_of_norm_le_const (μ := periodicMeasure μ₁ π T)
        (f := fun h : BanditHistory K T => μ₁ (h i).1 ((i : ℕ) + 1) - μ₂ (h i).1 ((i : ℕ) + 1))
        (C := d) (ae_of_all _ (fun h => by rw [Real.norm_eq_abs]; exact hpt _ _ hi1))
      simpa [Real.norm_eq_abs] using this
    rw [one_mul] at hB
    have e := abs_sub_le (∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T))
      (∫ h, μ₂ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T))
      (∫ h, μ₂ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₂ π T))
    have e2 := abs_sub_le (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₁ k ((i : ℕ) + 1)) -
          ∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T))
      (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₂ k ((i : ℕ) + 1)) -
          ∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T))
      (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₂ k ((i : ℕ) + 1)) -
          ∫ h, μ₂ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₂ π T))
    have e3 : (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₁ k ((i : ℕ) + 1)) -
          ∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T)) -
        (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₂ k ((i : ℕ) + 1)) -
          ∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T)) =
        Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₁ k ((i : ℕ) + 1)) -
          Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₂ k ((i : ℕ) + 1)) := by ring
    have e4 : (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₂ k ((i : ℕ) + 1)) -
          ∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T)) -
        (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ₂ k ((i : ℕ) + 1)) -
          ∫ h, μ₂ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₂ π T)) =
        -(∫ h, μ₁ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₁ π T) -
          ∫ h, μ₂ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ₂ π T)) := by ring
    rw [e3, e4, abs_neg] at e2
    linarith
  unfold periodicRegret
  rw [← Finset.sum_sub_distrib]
  refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
  refine lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => hterm i)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd2 : d ≤ ε / (4 * (Tr + 1)) := min_le_right _ _
  have h1 : Tr * d ≤ ε / 4 := by
    calc Tr * d ≤ Tr * (ε / (4 * (Tr + 1))) := mul_le_mul_of_nonneg_left hd2 hTr0
      _ = ε / 4 * (Tr / (Tr + 1)) := by field_simp
      _ ≤ ε / 4 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = ε / 4 := by ring
  have h2 : Tr * (Tr * η) ≤ ε / 4 := by
    calc Tr * (Tr * η) = ε / 4 * (Tr * Tr / (Tr * Tr + 1)) := by rw [hη]; field_simp
      _ ≤ ε / 4 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = ε / 4 := by ring
  rw [← hTr]
  nlinarith
