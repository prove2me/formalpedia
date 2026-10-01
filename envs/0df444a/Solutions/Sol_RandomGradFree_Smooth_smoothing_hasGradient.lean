-- Prove2me | solution 1 for RandomGradFree.Smooth.smoothing_hasGradient
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:48:25.770015+00:00
-- url     : https://prove2.me/submissions/8746ab3b-454d-4ea6-a6d8-06f0896a24ef

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Shared_oracle
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory ProbabilityTheory
namespace RandomStein

lemma pdf_deriv (x : ℝ) : HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt (fun y : ℝ => -y^2/2) (-x) x := by
    convert! ((hasDerivAt_pow 2 x).neg.div_const 2) using 1 <;> ring
  change HasDerivAt (fun y : ℝ => (Real.sqrt (2*Real.pi*1))⁻¹ * Real.exp (-(y-0)^2/(2*1)))
    (-x*((Real.sqrt (2*Real.pi*1))⁻¹ * Real.exp (-(x-0)^2/(2*1)))) x
  simp only [sub_zero,mul_one]
  convert! h.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1 <;> ring

lemma density_integrable (f : ℝ → ℝ) (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x*f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (Filter.Eventually.of_forall (fun x => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

lemma scalar (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x)
    (hf : Integrable f (gaussianReal 0 1)) (hg : Integrable g (gaussianReal 0 1))
    (hxf : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    ∫ x, g x ∂(gaussianReal 0 1) = ∫ x, x*f x ∂(gaussianReal 0 1) := by
  have h1 : Integrable (f * (fun x => -x*gaussianPDFReal 0 1 x)) := by
    convert! (density_integrable _ hxf).neg using 1
    ext x
    simp only [Pi.mul_apply,Pi.neg_apply]
    ring
  have h2 : Integrable (g * gaussianPDFReal 0 1) := by
    convert! density_integrable g hg using 1
    ext x
    simp [mul_comm]
  have h3 : Integrable (f * gaussianPDFReal 0 1) := by
    convert! density_integrable f hf using 1
    ext x
    simp [mul_comm]
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd x) (fun x _ => pdf_deriv x) h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul (by norm_num),
    integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  have heq : (fun x => f x*(-x*gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x*(x*f x))) := by ext x; ring
  rw [heq,integral_neg] at hh
  have heq2 : (fun x => g x*gaussianPDFReal 0 1 x) =
      (fun x => gaussianPDFReal 0 1 x*g x) := by ext x; ring
  rw [heq2] at hh
  linarith

end RandomStein

namespace RandomStein
open MeasureTheory ProbabilityTheory

lemma pi_scalar {n : ℕ} (i : Fin (n+1)) (F G : (Fin (n+1) → ℝ) → ℝ)
    (hd : ∀ y t, HasDerivAt (fun a => F (i.insertNth a y)) (G (i.insertNth t y)) t)
    (hF : Integrable F (Measure.pi fun _ => gaussianReal 0 1))
    (hG : Integrable G (Measure.pi fun _ => gaussianReal 0 1))
    (hiF : Integrable (fun z => z i*F z) (Measure.pi fun _ => gaussianReal 0 1)) :
    ∫ z, G z ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, z i*F z ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hFc := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  have hGc := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hG
  have hic := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hiF
  simp only [Function.comp_def] at hFc hGc hic
  rw [←he.integral_comp' G,←he.integral_comp' (fun z => z i*F z),
    integral_prod_symm _ hGc,integral_prod_symm _ hic]
  apply integral_congr_ae
  filter_upwards [hFc.prod_left_ae,hGc.prod_left_ae,hic.prod_left_ae] with y hf hg hi
  have hef (a : ℝ) : e.symm (a,y) = i.insertNth a y := rfl
  change Integrable (fun x : ℝ => (i.insertNth (α := fun _ => ℝ) x y) i*F (i.insertNth x y)) (gaussianReal 0 1) at hi
  change (∫ x, G (i.insertNth x y) ∂(gaussianReal 0 1)) =
    (∫ x : ℝ, (i.insertNth (α := fun _ => ℝ) x y) i*F (i.insertNth x y) ∂(gaussianReal 0 1))
  simp only [Fin.insertNth_apply_same] at hi ⊢
  exact scalar _ _ (hd y) hf hg hi

end RandomStein

namespace RandomStein
open MeasureTheory ProbabilityTheory

lemma basis_scalar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (b : OrthonormalBasis (Fin (n+1)) ℝ E) (i : Fin (n+1))
    (f : E → ℝ) (hd : Differentiable ℝ f)
    (hf : Integrable f (stdGaussian E))
    (hg : Integrable (fun u => fderiv ℝ f u (b i)) (stdGaussian E))
    (huf : Integrable (fun u => inner ℝ (b i) u*f u) (stdGaussian E)) :
    ∫ u, fderiv ℝ f u (b i) ∂(stdGaussian E) =
      ∫ u, inner ℝ (b i) u*f u ∂(stdGaussian E) := by
  classical
  let T := fun z : Fin (n+1) → ℝ => ∑ j, z j • b j
  have hT : Measurable T := by fun_prop
  have hmap : stdGaussian E = (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1).map T :=
    stdGaussian_eq_map_pi_orthonormalBasis b
  have hf' := hf
  have hg' := hg
  have huf' := huf
  rw [hmap] at hf' hg' huf'
  have hfc := hf'.comp_measurable hT
  have hgc := hg'.comp_measurable hT
  have huc := huf'.comp_measurable hT
  have hi (z : Fin (n+1) → ℝ) : inner ℝ (b i) (T z) = z i := by
    exact b.orthonormal.inner_right_fintype z i
  simp only [Function.comp_def,hi] at hfc hgc huc
  have hpath (y : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun a => f (T (i.insertNth a y))) (fderiv ℝ f (T (i.insertNth t y)) (b i)) t := by
    have heq (a : ℝ) : T (i.insertNth a y) = a • b i+∑ j, y j • b (i.succAbove j) := by
      dsimp [T]
      rw [Fin.sum_univ_succAbove _ i]
      simp
    have hh : HasDerivAt (fun a : ℝ => T (i.insertNth a y)) (b i) t := by
      simp_rw [heq]
      simpa using ((hasDerivAt_id t).smul_const (b i)).add_const (∑ j, y j • b (i.succAbove j))
    convert! (hd (T (i.insertNth t y))).hasFDerivAt.comp_hasDerivAt t hh using 1
  have hh := pi_scalar i (fun z => f (T z)) (fun z => fderiv ℝ f (T z) (b i)) hpath hfc hgc huc
  rw [hmap,integral_map hT.aemeasurable hg'.aestronglyMeasurable,
    integral_map hT.aemeasurable huf'.aestronglyMeasurable]
  simp only [hi]
  exact hh

end RandomStein

namespace RandomStein
open MeasureTheory ProbabilityTheory

lemma basis_scalar_any {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n)
    (f : E → ℝ) (hd : Differentiable ℝ f)
    (hf : Integrable f (stdGaussian E))
    (hg : Integrable (fun u => fderiv ℝ f u (b i)) (stdGaussian E))
    (huf : Integrable (fun u => inner ℝ (b i) u*f u) (stdGaussian E)) :
    ∫ u, fderiv ℝ f u (b i) ∂(stdGaussian E) =
      ∫ u, inner ℝ (b i) u*f u ∂(stdGaussian E) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact basis_scalar b i f hd hf hg huf

lemma vector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hd : Differentiable ℝ f)
    (hf : Integrable f (stdGaussian E))
    (hg : Integrable (fun u => fderiv ℝ f u) (stdGaussian E))
    (huf : Integrable (fun u => f u • u) (stdGaussian E)) :
    (InnerProductSpace.toDual ℝ E).symm (∫ u, fderiv ℝ f u ∂(stdGaussian E)) =
      ∫ u, f u • u ∂(stdGaussian E) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  apply InnerProductSpace.ext_inner_left_basis b.toBasis
  intro i
  have hh := basis_scalar_any b i f hd hf (hg.apply_continuousLinearMap (b i))
    (by simpa only [inner_smul_right,smul_eq_mul,mul_comm] using huf.const_inner (𝕜 := ℝ) (b i))
  have heq : inner ℝ (b i) ((InnerProductSpace.toDual ℝ E).symm (∫ u, fderiv ℝ f u ∂(stdGaussian E))) =
      (∫ u, fderiv ℝ f u ∂(stdGaussian E)) (b i) := by
    rw [real_inner_comm]
    exact congrArg (fun L : E →L[ℝ] ℝ => L (b i)) ((InnerProductSpace.toDual ℝ E).apply_symm_apply _)
  change inner ℝ (b i) _ = inner ℝ (b i) _
  rw [heq,ContinuousLinearMap.integral_apply hg,←integral_inner huf]
  simpa only [inner_smul_right,smul_eq_mul,mul_comm] using hh

end RandomStein


open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

open scoped RealInnerProductSpace

theorem aux_sa_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖) (x v : E) :
    |f (x + v) - f x - ⟪gradient f x, v⟫| ≤ L₁ / 2 * ‖v‖ ^ 2 := by
  let g : ℝ → ℝ := fun t => f (x + t • v) - f x - t * ⟪gradient f x, v⟫
  let g' : ℝ → ℝ := fun t => ⟪gradient f (x + t • v), v⟫ - ⟪gradient f x, v⟫
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f (x + t • v)))
        (x + t • v) :=
      hasGradientAt_iff_hasFDerivAt.mp (hdiff (x + t • v)).hasGradientAt
    have h3 := h2.comp_hasDerivAt t h1
    have h4 : HasDerivAt g
        ((InnerProductSpace.toDual ℝ E (gradient f (x + t • v))) v - 1 * ⟪gradient f x, v⟫) t :=
      (h3.sub_const (f x)).sub ((hasDerivAt_id' t).mul_const _)
    refine h4.congr_deriv ?_
    simp [g']
  let B : ℝ → ℝ := fun t => L₁ / 2 * ‖v‖ ^ 2 * t ^ 2
  let B' : ℝ → ℝ := fun t => L₁ * ‖v‖ ^ 2 * t
  have hB : ∀ t, HasDerivAt B (B' t) t := by
    intro t
    have h : HasDerivAt B (L₁ / 2 * ‖v‖ ^ 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) t :=
      (hasDerivAt_pow 2 t).const_mul _
    refine h.congr_deriv ?_
    simp only [B']; norm_num; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := g)
    (f' := g')
    (fun t _ => (hg t).continuousAt.continuousWithinAt)
    (fun t _ => (hg t).hasDerivWithinAt) (B := B) (B' := B') (by simp [g, B]) hB ?_
    (x := 1) (by simp)
  · simpa [g, B, Real.norm_eq_abs] using key
  · intro t ht
    rw [Real.norm_eq_abs]
    have : g' t = ⟪gradient f (x + t • v) - gradient f x, v⟫ := by simp [g', inner_sub_left]
    rw [this]
    calc |⟪gradient f (x + t • v) - gradient f x, v⟫|
        ≤ ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (L₁ * ‖x + t • v - x‖) * ‖v‖ := by gcongr; exact hgrad _ _
      _ = B' t := by simp [B', norm_smul, abs_of_nonneg ht.1]; ring

theorem aux_sa_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ E
  have hmem : MemLp (id : E → E) 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hone : ∀ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h := covarianceBilin_apply hmem (b i) (b i)
    rw [covarianceBilin_stdGaussian] at h
    have hm : (stdGaussian E)[id] = 0 := by simp
    simp only [hm, sub_zero] at h
    change ⟪b i, b i⟫ = _ at h
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i] at h
    simp only [one_pow] at h
    rw [h]
    congr 1
    ext u
    ring
  have hint : ∀ i, Integrable (fun u => ⟪b i, u⟫ ^ 2) (stdGaussian E) := by
    intro i
    have : MemLp (fun u : E => ⟪b i, u⟫) 2 (stdGaussian E) :=
      (innerSL ℝ (b i)).comp_memLp' hmem
    exact this.integrable_sq
  calc ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E)
      = ∫ u, ∑ i, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := by
        congr 1; ext u; rw [b.sum_sq_inner_right]
    _ = ∑ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := integral_finsetSum _ (fun i _ => hint i)
    _ = Module.finrank ℝ E := by simp [hone]

end RandomGradFree.Smooth

open RandomGradFree.Smooth
open MeasureTheory ProbabilityTheory



open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem aux_sgl_fderiv_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x : E) :
    fderiv ℝ f x = InnerProductSpace.toDual ℝ E (gradient f x) := by
  simp [gradient]

theorem aux_sgl_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x₀ : E) :
    Integrable (fun u => fderiv ℝ f (x₀ + μ • u)) (stdGaussian E) ∧
    HasFDerivAt (RandomGradFree.Shared.smoothing f μ)
      (∫ u, fderiv ℝ f (x₀ + μ • u) ∂(stdGaussian E)) x₀ := by
  set γ := stdGaussian E with hγ
  set G := ‖fderiv ℝ f 0‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hfc : Continuous f := hdiff.continuous
  have hcont : Continuous (fderiv ℝ f) := by
    refine (LipschitzWith.of_dist_le_mul (K := L₁.toNNReal) fun a b => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL₁]
    exact hL a b
  have hfd : ∀ z, ‖fderiv ℝ f z‖ ≤ G + L₁ * ‖z‖ := by
    intro z
    have := hL z 0
    simp only [sub_zero] at this
    have h2 := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f 0)
    linarith
  have hfb : ∀ z, ‖f z‖ ≤ ‖f 0‖ + (G + L₁ * ‖z‖) * ‖z‖ := by
    intro z
    have h := (convex_closedBall (0:E) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
      (f := f) (C := G + L₁ * ‖z‖) (x := 0) (y := z) (fun w _ => hdiff w)
      (fun w hw => by
        have := hfd w
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        nlinarith)
      (Metric.mem_closedBall_self (norm_nonneg z)) (by simp)
    simp only [sub_zero] at h
    have h2 := norm_sub_norm_le (f z) (f 0)
    linarith
  have hint1 : Integrable (fun u : E => ‖u‖) γ := IsGaussian.integrable_id.norm
  have hint2 : Integrable (fun u : E => ‖u‖ ^ 2) γ := by
    have := IsGaussian.memLp_id γ ((2 : ℕ) : ENNReal) (by simp)
    exact this.integrable_norm_pow two_ne_zero
  -- integrability of the derivative
  have hF'int : ∀ x : E, Integrable (fun u => fderiv ℝ f (x + μ • u)) γ := by
    intro x
    refine Integrable.mono' ((integrable_const (G + L₁ * ‖x‖)).add (hint1.const_mul (L₁ * μ)))
      ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfd (x + μ • u)
    have h2 : ‖x + μ • u‖ ≤ ‖x‖ + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  refine ⟨hF'int x₀, ?_⟩
  show HasFDerivAt (fun x => ∫ u, f (x + μ • u) ∂γ) _ x₀
  have hF_int : Integrable (fun u => f (x₀ + μ • u)) γ := by
    refine Integrable.mono'
      (((integrable_const (‖f 0‖ + G * ‖x₀‖ + 2 * L₁ * ‖x₀‖ ^ 2)).add
        (hint1.const_mul (G * μ))).add (hint2.const_mul (2 * L₁ * μ ^ 2)))
      ((hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfb (x₀ + μ • u)
    have h2 : ‖x₀ + μ • u‖ ≤ ‖x₀‖ + μ * ‖u‖ := by
      calc ‖x₀ + μ • u‖ ≤ ‖x₀‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x₀‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    set n := ‖x₀ + μ • u‖
    set a := ‖x₀‖
    set t := ‖u‖
    have hn : 0 ≤ n := norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have ht : 0 ≤ t := norm_nonneg _
    have hs : 0 ≤ a + μ * t := by positivity
    have e1 : G * n ≤ G * (a + μ * t) := mul_le_mul_of_nonneg_left h2 hG0
    have e2 : n * n ≤ (a + μ * t) * (a + μ * t) := mul_le_mul h2 h2 hn hs
    have e3 : (a + μ * t) * (a + μ * t) ≤ 2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2 := by
      nlinarith [sq_nonneg (a - μ * t)]
    have e4 : L₁ * (n * n) ≤ L₁ * (2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left (e2.trans e3) hL₁
    nlinarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x u => f (x + μ • u)) (F' := fun x u => fderiv ℝ f (x + μ • u))
    (bound := fun u => G + L₁ * (‖x₀‖ + 1) + L₁ * μ * ‖u‖)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    hF_int
    ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u x hx => ?_)
    ((integrable_const _).add (hint1.const_mul (L₁ * μ)))
    (Filter.Eventually.of_forall fun u x _ => ?_)
  · have h1 := hfd (x + μ • u)
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have := norm_le_norm_add_norm_sub' x x₀
      calc ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
            have := norm_sub_norm_le x x₀
            linarith
        _ ≤ ‖x₀‖ + 1 := by linarith
    have h2 : ‖x + μ • u‖ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
        _ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  · exact (hasFDerivAt_comp_add_right (μ • u)).2 (hdiff _).hasFDerivAt

end RandomGradFree.Accelerated

open RandomGradFree.Accelerated
open MeasureTheory ProbabilityTheory


namespace RandomStein
open MeasureTheory ProbabilityTheory RandomGradFree.Accelerated RandomGradFree.Smooth RandomGradFree.Shared

lemma smooth_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (fun u => f (x+μ • u)) (stdGaussian E) ∧
    Integrable (fun u => f (x+μ • u) • u) (stdGaussian E) := by
  have h1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  have h2 : Integrable (fun u : E => ‖u‖^2) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (2:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  have h3 : Integrable (fun u : E => ‖u‖^3) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (3:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  have hc : Continuous (fun u => f (x+μ • u)) := hd.continuous.comp (by fun_prop)
  have hb (u : E) : ‖f (x+μ • u)‖ ≤ ‖f x‖+μ*‖gradient f x‖*‖u‖+L/2*μ^2*‖u‖^2 := by
    have hh := aux_sa_descent f L hd hgrad x (μ • u)
    rw [norm_smul,Real.norm_of_nonneg hμ,mul_pow] at hh
    have ht := abs_real_inner_le_norm (gradient f x) (μ • u)
    rw [norm_smul,Real.norm_of_nonneg hμ] at ht
    have hsum := norm_add_le (f x) (inner ℝ (gradient f x) (μ • u))
    have hrem := norm_sub_norm_le (f (x+μ • u)) (f x+inner ℝ (gradient f x) (μ • u))
    rw [Real.norm_eq_abs] at hrem
    have ha : |f (x+μ • u)-(f x+inner ℝ (gradient f x) (μ • u))| ≤ L/2*(μ^2*‖u‖^2) := by
      simpa only [sub_add_eq_sub_sub] using hh
    rw [Real.norm_eq_abs] at hsum
    simp only [Real.norm_eq_abs] at hsum hrem ⊢
    nlinarith [ha,ht,hsum,hrem]
  constructor
  · refine Integrable.mono' (((integrable_const ‖f x‖).add (h1.const_mul (μ*‖gradient f x‖))).add
      (h2.const_mul (L/2*μ^2))) hc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hb
  · refine Integrable.mono' (((h1.const_mul ‖f x‖).add (h2.const_mul (μ*‖gradient f x‖))).add
      (h3.const_mul (L/2*μ^2))) (hc.smul continuous_id).aestronglyMeasurable ?_
    filter_upwards [] with u
    rw [norm_smul]
    have hh := mul_le_mul_of_nonneg_right (hb u) (norm_nonneg u)
    dsimp only [Pi.add_apply]
    nlinarith

lemma smooth_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (smoothing f μ) (∫ u, oracle f μ x u ∂(stdGaussian E)) x := by
  have hfd : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ L*‖x-y‖ := by
    intro x y
    rw [aux_sgl_fderiv_eq f x,aux_sgl_fderiv_eq f y,←map_sub,LinearIsometryEquiv.norm_map]
    exact hgrad x y
  have hm := aux_sgl_main f L hL hd hfd μ hμ.le x
  have hi := smooth_integrable f L hL hd hgrad μ hμ.le x
  let F := fun u => f (x+μ • u)
  have hFder (u : E) : HasFDerivAt F (μ • fderiv ℝ f (x+μ • u)) u := by
    convert! (hd (x+μ • u)).hasFDerivAt.comp u (((hasFDerivAt_id u).const_smul μ).const_add x) using 1
    ext v
    simp
  have hFdeq : fderiv ℝ F = fun u => μ • fderiv ℝ f (x+μ • u) := funext (fun u => (hFder u).fderiv)
  have hFi : Integrable (fun u => fderiv ℝ F u) (stdGaussian E) := by rw [hFdeq]; exact hm.1.smul μ
  have hs := vector F (fun u => (hFder u).differentiableAt) hi.1 hFi hi.2
  rw [hFdeq,integral_smul,LinearIsometryEquiv.map_smul] at hs
  have horacle : (∫ u, oracle f μ x u ∂(stdGaussian E)) =
      μ⁻¹ • (∫ u, F u • u ∂(stdGaussian E)) := by
    have hid : Integrable (fun u : E => u) (stdGaussian E) := IsGaussian.integrable_id
    have hpoint (u : E) : oracle f μ x u = μ⁻¹ • (F u • u-f x • u) := by
      simp only [oracle,if_neg hμ.ne',F,div_eq_mul_inv,smul_sub,smul_smul]
      rw [←sub_smul]
      congr 1
      ring
    simp_rw [hpoint]
    have hfu : Integrable (fun u => F u • u) (stdGaussian E) := hi.2
    have hconst : Integrable (fun u : E => f x • u) (stdGaussian E) := hid.smul (f x)
    rw [integral_smul,integral_sub hfu hconst,integral_smul,integral_id_stdGaussian]
    simp
  rw [horacle,←hs,smul_smul,inv_mul_cancel₀ hμ.ne',one_smul]
  exact hasGradientAt_iff_hasFDerivAt.mpr (by simpa using hm.2)

end RandomStein

namespace RandomGradFree.Smooth

theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ)
    (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (RandomGradFree.Shared.smoothing f μ) (∫ u, RandomGradFree.Shared.oracle f μ x u ∂(stdGaussian E)) x := by
  exact RandomStein.smooth_identity f L₁ hL₁ hdiff hgrad μ hμ x

end RandomGradFree.Smooth
