-- Prove2me | solution 1 for TreatmentLocality.influence_score_covariance_iid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T17:06:22.147143+00:00
-- url     : https://prove2.me/submissions/e54d3571-33f3-446c-a54e-40ccf2c9f106

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Definitions.Def_TreatmentLocality
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_TreatmentLocalityPerturbation
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_TreatmentLocalityIID
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Ring.Units
import Definitions.Def_MarkovIterKernel
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovChainPathMeasure
import Theorems.Thm_MarkovChainCLT_setIntegral_next_coord_eq
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Definitions.Def_MarkovErgodicity
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.L2Space

-- === pert_scalar.lean ===
section



open Real

namespace Statistics

/-- The derivative of the scalar likelihood ratio. -/
theorem hasDerivAt_pertScalar (b A B t : ℝ) :
    HasDerivAt (fun u : ℝ => (1 + u * b) * rexp (u * A - u ^ 2 * B))
      (b * rexp (t * A - t ^ 2 * B)
        + (1 + t * b) * rexp (t * A - t ^ 2 * B) * (A - 2 * t * B)) t := by
  have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
  have h1 : HasDerivAt (fun u : ℝ => 1 + u * b) b t := by
    have h := (hid.mul_const b).const_add (1 : ℝ)
    rw [one_mul] at h
    exact h
  have h2 : HasDerivAt (fun u : ℝ => u * A - u ^ 2 * B) (A - 2 * t * B) t := by
    have ha : HasDerivAt (fun u : ℝ => u * A) A t := by
      have h := hid.mul_const A
      rw [one_mul] at h
      exact h
    have hb : HasDerivAt (fun u : ℝ => u ^ 2 * B) (2 * t * B) t := by
      have hp : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
        have h := hasDerivAt_pow 2 t
        norm_num at h
        exact h
      exact hp.mul_const B
    exact ha.sub hb
  have h3 : HasDerivAt (fun u : ℝ => rexp (u * A - u ^ 2 * B))
      (rexp (t * A - t ^ 2 * B) * (A - 2 * t * B)) t := h2.exp
  have h4 := h1.fun_mul h3
  refine h4.congr_deriv ?_
  ring

/-- The scalar likelihood ratio is bounded by `exp|A|` up to the factor `3/2`. -/
theorem abs_pertScalar_le (b A B t : ℝ) (hB : 0 ≤ B) (hb : |t * b| ≤ 1 / 2) (ht : |t| ≤ 1) :
    |(1 + t * b) * rexp (t * A - t ^ 2 * B)| ≤ 3 / 2 * rexp |A| := by
  have hexp : rexp (t * A - t ^ 2 * B) ≤ rexp |A| := by
    refine Real.exp_le_exp.2 ?_
    have h1 : t * A ≤ |A| := by
      calc t * A ≤ |t * A| := le_abs_self _
        _ = |t| * |A| := abs_mul t A
        _ ≤ 1 * |A| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
        _ = |A| := one_mul _
    nlinarith [sq_nonneg t]
  have h1b : |1 + t * b| ≤ 3 / 2 := by
    have := abs_le.1 hb
    rw [abs_le]; constructor <;> linarith
  calc |(1 + t * b) * rexp (t * A - t ^ 2 * B)|
      = |1 + t * b| * rexp (t * A - t ^ 2 * B) := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 3 / 2 * rexp |A| :=
        mul_le_mul h1b hexp (Real.exp_pos _).le (by norm_num)

/-- The derivative of the scalar likelihood ratio is bounded by `exp|A|` up to an explicit
factor. -/
theorem abs_pertScalarDeriv_le (b A B t : ℝ) (hB : 0 ≤ B) (hb : |t * b| ≤ 1 / 2)
    (ht : |t| ≤ 1) :
    |b * rexp (t * A - t ^ 2 * B)
        + (1 + t * b) * rexp (t * A - t ^ 2 * B) * (A - 2 * t * B)|
      ≤ (|b| + 3 / 2 * (|A| + 2 * B)) * rexp |A| := by
  have hexp : rexp (t * A - t ^ 2 * B) ≤ rexp |A| := by
    refine Real.exp_le_exp.2 ?_
    have h1 : t * A ≤ |A| := by
      calc t * A ≤ |t * A| := le_abs_self _
        _ = |t| * |A| := abs_mul t A
        _ ≤ 1 * |A| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
        _ = |A| := one_mul _
    nlinarith [sq_nonneg t]
  have h1b : |1 + t * b| ≤ 3 / 2 := by
    have := abs_le.1 hb
    rw [abs_le]; constructor <;> linarith
  have hlin : |A - 2 * t * B| ≤ |A| + 2 * B := by
    have h2 : |2 * t * B| ≤ 2 * B := by
      rw [abs_mul, abs_mul]
      have : |(2 : ℝ)| * |t| ≤ 2 := by
        rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
      calc |(2:ℝ)| * |t| * |B| ≤ 2 * |B| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = 2 * B := by rw [abs_of_nonneg hB]
    have habs : |A - 2 * t * B| ≤ |A| + |2 * t * B| := by
      rw [sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_neg]
    linarith
  have hnn : (0 : ℝ) ≤ rexp (t * A - t ^ 2 * B) := (Real.exp_pos _).le
  calc |b * rexp (t * A - t ^ 2 * B)
          + (1 + t * b) * rexp (t * A - t ^ 2 * B) * (A - 2 * t * B)|
      ≤ |b * rexp (t * A - t ^ 2 * B)|
          + |(1 + t * b) * rexp (t * A - t ^ 2 * B) * (A - 2 * t * B)| := abs_add_le _ _
    _ = |b| * rexp (t * A - t ^ 2 * B)
          + |1 + t * b| * rexp (t * A - t ^ 2 * B) * |A - 2 * t * B| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ |b| * rexp |A| + 3 / 2 * rexp |A| * (|A| + 2 * B) := by
        have hA0 : (0:ℝ) ≤ |A| + 2 * B := by positivity
        have hstep1 : |b| * rexp (t * A - t ^ 2 * B) ≤ |b| * rexp |A| :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        have hstep2 : |1 + t * b| * rexp (t * A - t ^ 2 * B) * |A - 2 * t * B|
            ≤ 3 / 2 * rexp |A| * (|A| + 2 * B) := by
          refine mul_le_mul ?_ hlin (abs_nonneg _) (by positivity)
          exact mul_le_mul h1b hexp hnn (by norm_num)
        linarith
    _ = (|b| + 3 / 2 * (|A| + 2 * B)) * rexp |A| := by ring

end Statistics

end

-- === gauss_dens.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace Statistics

/-- **The likelihood ratio of a Gaussian mean shift.**  Shifting the mean of a Gaussian by
`h` tilts it by the explicit exponential density `exp(h(r-m)/v - h²/(2v))`. -/
theorem gaussianReal_shift (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h : ℝ) :
    gaussianReal (m + h) v
      = (gaussianReal m v).withDensity
          (fun r => ENNReal.ofReal (rexp (h * (r - m) / v - h ^ 2 / (2 * v)))) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := lt_of_le_of_ne v.coe_nonneg (fun hc => hv (by
    exact NNReal.coe_eq_zero.mp hc.symm))
  have hpt : ∀ r : ℝ, gaussianPDF (m + h) v r
      = gaussianPDF m v r * ENNReal.ofReal (rexp (h * (r - m) / v - h ^ 2 / (2 * v))) := by
    intro r
    rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 1
    simp only [gaussianPDFReal]
    have key : rexp (-(r - m) ^ 2 / (2 * (v : ℝ)))
          * rexp (h * (r - m) / (v : ℝ) - h ^ 2 / (2 * (v : ℝ)))
        = rexp (-(r - (m + h)) ^ 2 / (2 * (v : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [← key]
    ring
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv]
  have hG : Measurable (fun r : ℝ => ENNReal.ofReal
      (rexp (h * (r - m) / (v : ℝ) - h ^ 2 / (2 * (v : ℝ))))) := by fun_prop
  rw [← withDensity_mul _ (measurable_gaussianPDF m v) hG]
  congr 1
  funext r
  exact hpt r

/-- Every Gaussian has finite exponential moments of the absolute value. -/
theorem integrable_exp_abs_gaussian (c m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => rexp (c * |x|)) (gaussianReal m v) := by
  have h1 : Integrable (fun x : ℝ => rexp (|c| * x)) (gaussianReal m v) :=
    integrable_exp_mul_gaussianReal _
  have h2 : Integrable (fun x : ℝ => rexp (-|c| * x)) (gaussianReal m v) :=
    integrable_exp_mul_gaussianReal _
  refine Integrable.mono (h1.add h2) (by fun_prop) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity : (0:ℝ) <
    rexp (|c| * x) + rexp (-|c| * x))]
  rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
  · have : c * |x| ≤ |c| * x := by
      rw [hx]; exact mul_le_mul_of_nonneg_right (le_abs_self c) (by rw [← hx]; positivity)
    have := Real.exp_le_exp.2 this
    linarith [Real.exp_pos (-|c| * x)]
  · have : c * |x| ≤ -|c| * x := by
      rw [hx]
      have : c * -x ≤ |c| * -x := mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
      linarith
    have := Real.exp_le_exp.2 this
    linarith [Real.exp_pos (|c| * x)]

/-- The exponential moment of a Gaussian is finite as an `ℝ≥0∞`-integral. -/
theorem lintegral_exp_abs_gaussian_lt_top (c m : ℝ) (v : ℝ≥0) :
    ∫⁻ x : ℝ, ENNReal.ofReal (rexp (c * |x|)) ∂(gaussianReal m v) < ⊤ := by
  have h := integrable_exp_abs_gaussian c m v
  have := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
    at this
  exact this

end Statistics

end

-- === dens_aux.lean ===
section



open MeasureTheory Measure
open scoped ENNReal

namespace Statistics

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Tilting the image of a section by a density is the image of the tilt. -/
theorem withDensity_map_prodMk (x : α) (η : Measure β) {g : α × β → ℝ≥0∞} (hg : Measurable g) :
    (η.map (Prod.mk x)).withDensity g
      = (η.withDensity (fun y => g (x, y))).map (Prod.mk x) := by
  ext A hA
  rw [withDensity_apply _ hA, Measure.map_apply measurable_prodMk_left hA,
    withDensity_apply _ (measurable_prodMk_left hA),
    Measure.restrict_map measurable_prodMk_left hA,
    lintegral_map hg measurable_prodMk_left]

/-- A product of tilted measures is the product tilted by the product density. -/
theorem prod_withDensity (η₁ : Measure α) (η₂ : Measure β) [SigmaFinite η₁] [SigmaFinite η₂]
    {f₁ : α → ℝ≥0∞} {f₂ : β → ℝ≥0∞} (h₁ : Measurable f₁) (h₂ : Measurable f₂)
    [SigmaFinite (η₁.withDensity f₁)] [SigmaFinite (η₂.withDensity f₂)] :
    (η₁.prod η₂).withDensity (fun z => f₁ z.1 * f₂ z.2)
      = (η₁.withDensity f₁).prod (η₂.withDensity f₂) := by
  refine (Measure.prod_eq (μ := η₁.withDensity f₁) (ν := η₂.withDensity f₂) fun s t hs ht => ?_).symm
  rw [withDensity_apply _ (hs.prod ht), ← Measure.prod_restrict,
    lintegral_prod_mul h₁.aemeasurable h₂.aemeasurable,
    withDensity_apply _ hs, withDensity_apply _ ht]

end Statistics

end

-- === tl_bell.lean ===
section



open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

lemma polTrans_nonneg (M : Model S) (a : Bool) (i j : S) : 0 ≤ M.polTrans a i j :=
  ENNReal.toReal_nonneg

lemma polTrans_row_sum (M : Model S) (a : Bool) (i : S) : ∑ j, M.polTrans a i j = 1 := by
  have h1 : ∀ j : S, (M.trans i (M.act a i)) j ≠ ⊤ := fun j => PMF.apply_ne_top _ _
  have h2 : ∑ j, (M.trans i (M.act a i)) j = 1 := by
    have := (M.trans i (M.act a i)).tsum_coe
    rwa [tsum_fintype] at this
  simp only [Model.polTrans, Matrix.of_apply]
  rw [← ENNReal.toReal_sum (fun j _ => h1 j), h2, ENNReal.toReal_one]

/-- The discounted transition matrix is a strict contraction in the `L∞` operator norm. -/
lemma norm_smul_polTrans_lt_one (M : Model S) (a : Bool) :
    ‖M.γdisc • M.polTrans a‖ < 1 := by
  have hrow : ∀ i : S, ((∑ j, ‖(M.γdisc • M.polTrans a) i j‖₊ : ℝ≥0) : ℝ) ≤ M.γdisc := by
    intro i
    rw [NNReal.coe_sum]
    have hcalc : ∀ j ∈ (Finset.univ : Finset S),
        ((‖(M.γdisc • M.polTrans a) i j‖₊ : ℝ≥0) : ℝ) = M.γdisc * M.polTrans a i j := by
      intro j _
      simp only [coe_nnnorm, Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg M.γdisc_nonneg (polTrans_nonneg M a i j))
    rw [Finset.sum_congr rfl hcalc, ← Finset.mul_sum, polTrans_row_sum M a i, mul_one]
  have hg : (Finset.univ : Finset S).sup
      (fun i => ∑ j, ‖(M.γdisc • M.polTrans a) i j‖₊)
      ≤ (⟨M.γdisc, M.γdisc_nonneg⟩ : ℝ≥0) :=
    Finset.sup_le fun i _ => NNReal.coe_le_coe.mp (hrow i)
  have hle : ‖M.γdisc • M.polTrans a‖ ≤ M.γdisc := by
    rw [Matrix.linfty_opNorm_def]
    calc (((Finset.univ : Finset S).sup
            fun i => ∑ j, ‖(M.γdisc • M.polTrans a) i j‖₊ : ℝ≥0) : ℝ)
        ≤ ((⟨M.γdisc, M.γdisc_nonneg⟩ : ℝ≥0) : ℝ) := NNReal.coe_le_coe.mpr hg
      _ = M.γdisc := rfl
  exact lt_of_le_of_lt hle M.γdisc_lt_one

/-- **The Bellman system is invertible.** -/
theorem isUnit_one_sub_smul_polTrans (M : Model S) (a : Bool) :
    IsUnit ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a) :=
  isUnit_one_sub_of_norm_lt_one (norm_smul_polTrans_lt_one M a)

/-- **The Bellman equation** `V^a = r^a + γ P^a V^a`. -/
theorem value_bellman (M : Model S) (a : Bool) :
    M.value a = M.polReward a + M.γdisc • (M.polTrans a).mulVec (M.value a) := by
  have hdet : IsUnit ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_smul_polTrans M a)
  have hmul : ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a) *
      ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have h : ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a).mulVec (M.value a)
      = M.polReward a := by
    rw [Model.value, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have h2 : M.value a - M.γdisc • (M.polTrans a).mulVec (M.value a) = M.polReward a := by
    rw [← h, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  exact sub_eq_iff_eq_add.mp h2

/-- The Bellman equation, in coordinates. -/
theorem value_bellman_apply (M : Model S) (a : Bool) (s : S) :
    M.value a s = M.polReward a s + M.γdisc * ∑ j, M.polTrans a s j * M.value a j := by
  have h := congrFun (value_bellman M a) s
  simpa [Matrix.mulVec, dotProduct] using h

end TreatmentLocality

end

-- === tl_cons.lean ===
section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

section Bind

variable {α : Type*} [MeasurableSpace α]

/-- The Bochner integral against a measure pushed through a Markov kernel. -/
lemma integral_bind_eq (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α α) [IsMarkovKernel κ]
    {f : α → ℝ} (hf : Integrable f (μ.bind κ)) :
    ∫ y, f y ∂(μ.bind κ) = ∫ x, (∫ y, f y ∂(κ x)) ∂μ := by
  have h1 : μ.bind κ = (κ ∘ₖ (Kernel.const Unit μ)) () := rfl
  rw [h1] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

end Bind

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The experiment kernel, evaluated. -/
lemma expKernel_apply (M : Model S) (z : Step S) :
    expKernel M z = (Measure.dirac (Step.next z)).prod (stepLaw M (Step.next z)) := by
  rw [expKernel, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply]
  rfl

/-- Integrating one experiment step. -/
lemma integral_expKernel (M : Model S) (z : Step S) {f : Step S → ℝ} (hf : Measurable f) :
    ∫ w, f w ∂(expKernel M z) = ∫ p, f (Step.next z, p) ∂(stepLaw M (Step.next z)) := by
  rw [expKernel_apply, Measure.dirac_prod,
    integral_map (measurable_prodMk_left).aemeasurable hf.aestronglyMeasurable]

/-- Under an invariant law, the current step can be resampled from the step law at its
*next* state. -/
lemma integral_stationary (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) {f : Step S → ℝ} (hf : Measurable f)
    (hint : Integrable f ν) :
    ∫ z, f z ∂ν = ∫ z, (∫ p, f (Step.next z, p) ∂(stepLaw M (Step.next z))) ∂ν := by
  conv_lhs => rw [← hinv]
  rw [integral_bind_eq ν (expKernel M) (by rwa [hinv])]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => integral_expKernel M z hf)

/-- Under an invariant law, the current state and the next state have the same
distribution. -/
lemma integral_state_eq_integral_next (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν) (g : S → ℝ) :
    ∫ z, g (Step.state z) ∂ν = ∫ z, g (Step.next z) ∂ν := by
  have hgm : Measurable g := measurable_of_countable g
  have hfm : Measurable (fun z : Step S => g (Step.state z)) :=
    hgm.comp (measurable_fst)
  obtain ⟨C, hC⟩ : ∃ C, ∀ s, |g s| ≤ C :=
    ⟨∑ t, |g t|, fun s => Finset.single_le_sum (fun t _ => abs_nonneg (g t)) (Finset.mem_univ s)⟩
  have hint : Integrable (fun z : Step S => g (Step.state z)) ν := by
    refine (integrable_const C).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using hC (Step.state z)
  have h := integral_stationary M ν hinv hfm hint
  have h2 : ∀ z : Step S,
      ∫ p : Bool × S × ℝ, g (Step.state (Step.next z, p)) ∂(stepLaw M (Step.next z))
        = g (Step.next z) := by
    intro z
    simp [Step.state]
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall h2)

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The stationary decomposition of an integral against an invariant law. -/
lemma integral_eq_integral_stepLaw (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) {f : Step S → ℝ} (hf : Measurable f)
    (hint : Integrable f ν) :
    ∫ z, f z ∂ν = ∫ z, (∫ p, f (Step.state z, p) ∂(stepLaw M (Step.state z))) ∂ν := by
  rw [integral_stationary M ν hinv hf hint]
  exact (integral_state_eq_integral_next M ν hinv
    (fun s => ∫ p, f (s, p) ∂(stepLaw M s))).symm

/-- Integrating a function of the first coordinate against a product with a probability
measure. -/
lemma integral_prod_fst (μ : Measure S) (ρ : Measure ℝ) [SFinite μ] [IsProbabilityMeasure ρ]
    (g : S → ℝ) :
    ∫ q : S × ℝ, g q.1 ∂(μ.prod ρ) = ∫ x, g x ∂μ := by
  have h1 : (μ.prod ρ).map Prod.fst = μ := by
    rw [Measure.map_fst_prod]; simp
  calc ∫ q : S × ℝ, g q.1 ∂(μ.prod ρ)
      = ∫ x, g x ∂((μ.prod ρ).map Prod.fst) :=
        (integral_map measurable_fst.aemeasurable
          (measurable_of_countable g).aestronglyMeasurable).symm
    _ = ∫ x, g x ∂μ := by rw [h1]

/-- Integrating a function of the last coordinate against a product with a probability
measure. -/
lemma integral_prod_snd (μ : Measure S) (ρ : Measure ℝ) [IsProbabilityMeasure μ] [SFinite ρ]
    {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ q : S × ℝ, g q.2 ∂(μ.prod ρ) = ∫ r, g r ∂ρ := by
  have h1 : (μ.prod ρ).map Prod.snd = ρ := by
    rw [Measure.map_snd_prod]; simp
  calc ∫ q : S × ℝ, g q.2 ∂(μ.prod ρ)
      = ∫ r, g r ∂((μ.prod ρ).map Prod.snd) :=
        (integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ r, g r ∂ρ := by rw [h1]

/-- Integrating against the one-step experiment law: a fair coin between the two arms. -/
lemma integral_stepLaw (M : Model S) (s : S) {F : Bool × S × ℝ → ℝ} (hF : Measurable F)
    (hint : ∀ γ : Bool, Integrable (fun q : S × ℝ => F (γ, q))
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) :
    ∫ p, F p ∂(stepLaw M s)
      = (2 : ℝ)⁻¹ *
        ((∫ q : S × ℝ, F (true, q)
            ∂(((M.trans s (M.act true s)).toMeasure).prod (M.reward s (M.act true s))))
          + (∫ q : S × ℝ, F (false, q)
            ∂(((M.trans s (M.act false s)).toMeasure).prod (M.reward s (M.act false s))))) := by
  have hmap : ∀ γ : Bool,
      ∫ p, F p ∂((Measure.dirac γ).prod
          (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))))
        = ∫ q : S × ℝ, F (γ, q)
          ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := by
    intro γ
    rw [Measure.dirac_prod,
      integral_map measurable_prodMk_left.aemeasurable hF.aestronglyMeasurable]
  have hintd : ∀ γ : Bool, Integrable F ((Measure.dirac γ).prod
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) := by
    intro γ
    rw [Measure.dirac_prod]
    exact (integrable_map_measure hF.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 (hint γ)
  rw [stepLaw, integral_smul_measure, integral_add_measure (hintd true) (hintd false),
    hmap true, hmap false]
  norm_num

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The inverse-probability weight of the information-sharing scheme, evaluated on the
step law, reproduces the arm-`a` transition probability. -/
lemma integral_stepLaw_indicator (M : Model S) (s j : S) (a : Bool) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
          * (if p.2.1 = j then (1 : ℝ) else 0)) ∂(stepLaw M s)
      = (M.trans s (M.act a s) j).toReal := by
  classical
  set F : Bool × S × ℝ → ℝ := fun p =>
    (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
      * (if p.2.1 = j then (1 : ℝ) else 0) with hF
  have hind1 : MeasurableSet {p : Bool × S × ℝ | p.1 = a} :=
    measurable_fst (measurableSet_singleton a)
  have hind2 : MeasurableSet {p : Bool × S × ℝ | p.2.1 = j} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton j)
  have hFmeas : Measurable F := by
    rw [hF]
    refine Measurable.mul ?_ (Measurable.ite hind2 measurable_const measurable_const)
    by_cases hs : s = M.crucial
    · simp only [if_pos hs]
      exact (Measurable.ite hind1 measurable_const measurable_const).const_mul 2
    · simp only [if_neg hs]
      exact measurable_const
  have hbd : ∀ p, |F p| ≤ 2 := by
    intro p
    rw [hF]
    simp only [abs_mul]
    have h1 : |if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1| ≤ 2 := by
      split_ifs <;> norm_num
    have h2 : |if p.2.1 = j then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    calc |if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1|
          * |if p.2.1 = j then (1 : ℝ) else 0| ≤ 2 * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hint : ∀ γ : Bool, Integrable (fun q : S × ℝ => F (γ, q))
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := by
    intro γ
    refine (integrable_const (2 : ℝ)).mono'
      ((hFmeas.comp measurable_prodMk_left).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => ?_)
    simpa [Real.norm_eq_abs] using hbd (γ, q)
  rw [integral_stepLaw M s hFmeas hint]
  -- each arm contributes its own transition probability
  have hcoord : ∀ γ : Bool,
      ∫ q : S × ℝ, F (γ, q)
          ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
        = (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
          * (M.trans s (M.act γ s) j).toReal := by
    intro γ
    have : (fun q : S × ℝ => F (γ, q))
        = fun q : S × ℝ =>
          ((if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
            * (if q.1 = j then (1 : ℝ) else 0)) := rfl
    rw [this, integral_prod_fst _ _
      (fun x : S => (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
        * (if x = j then (1 : ℝ) else 0)), PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
    ring
  rw [hcoord true, hcoord false]
  by_cases hs : s = M.crucial
  · subst hs
    cases a <;> simp [Model.act] <;> ring
  · simp [Model.act, hs]
    ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma pmf_sum_toReal (p : PMF S) : ∑ j, (p j).toReal = 1 := by
  have h := PMF.integral_eq_sum p (fun _ : S => (1 : ℝ))
  simpa using h.symm

/-- The information-sharing weight, integrated against the step law, reproduces the
arm-`a` mean reward. -/
lemma integral_stepLaw_rwd (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * p.2.2)
        ∂(stepLaw M s)
      = M.polReward a s := by
  classical
  set F : Bool × S × ℝ → ℝ := fun p =>
    (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * p.2.2 with hF
  have hind1 : MeasurableSet {p : Bool × S × ℝ | p.1 = a} :=
    measurable_fst (measurableSet_singleton a)
  have hFmeas : Measurable F := by
    rw [hF]
    refine Measurable.mul ?_ (measurable_snd.comp measurable_snd)
    by_cases hs : s = M.crucial
    · simp only [if_pos hs]
      exact (Measurable.ite hind1 measurable_const measurable_const).const_mul 2
    · simp only [if_neg hs]
      exact measurable_const
  have hsnd : ∀ γ : Bool, Integrable (fun q : S × ℝ => q.2)
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := by
    intro γ
    have h1 : (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))).map Prod.snd
        = M.reward s (M.act γ s) := by
      rw [Measure.map_snd_prod]; simp
    refine (integrable_map_measure (g := fun r : ℝ => r) (f := Prod.snd)
      (μ := ((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
      ?_ measurable_snd.aemeasurable).1 ?_
    · rw [h1]; exact measurable_id.aestronglyMeasurable
    · rw [h1]; exact hR s (M.act γ s)
  have hint : ∀ γ : Bool, Integrable (fun q : S × ℝ => F (γ, q))
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := by
    intro γ
    exact (hsnd γ).const_mul
      (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
  rw [integral_stepLaw M s hFmeas hint]
  have hcoord : ∀ γ : Bool,
      ∫ q : S × ℝ, F (γ, q)
          ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
        = (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
          * (∫ r, r ∂(M.reward s (M.act γ s))) := by
    intro γ
    have hEq : (fun q : S × ℝ => F (γ, q))
        = fun q : S × ℝ =>
          (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1) * q.2 := rfl
    rw [hEq, integral_const_mul,
      integral_prod_snd _ _ (g := fun r : ℝ => r) measurable_id]
  rw [hcoord true, hcoord false, Model.polReward]
  by_cases hs : s = M.crucial
  · subst hs
    cases a <;> simp [Model.act] <;> ring
  · simp [Model.act, hs]
    ring

/-- The population transition statistic of the information-sharing scheme. -/
lemma meanObs_IS_trans (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (a : Bool) (i j : S) :
    (meanObs M .IS ν a).1 i j
      = (∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν) * M.polTrans a i j := by
  classical
  have hind : MeasurableSet {z : Step S | Step.state z = i} :=
    measurable_fst (measurableSet_singleton i)
  have hind2 : MeasurableSet {z : Step S | Step.next z = j} :=
    ((measurable_fst.comp measurable_snd).comp measurable_snd) (measurableSet_singleton j)
  have hindarm : MeasurableSet {z : Step S | Step.arm z = a} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton a)
  set f : Step S → ℝ := fun z => (estObs M .IS z a).1 i j with hf
  have hfEq : ∀ z : Step S, f z
      = (if Step.state z = i then (1 : ℝ) else 0)
        * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
          * (if Step.next z = j then (1 : ℝ) else 0)) := by
    intro z
    rw [hf]
    simp only [estObs, schemeWeight]
    by_cases h1 : Step.state z = i <;> by_cases h2 : Step.next z = j <;>
      simp [h1, h2]
  have hfmeas : Measurable f := by
    rw [funext hfEq]
    refine Measurable.mul (Measurable.ite hind measurable_const measurable_const) ?_
    refine Measurable.mul ?_ (Measurable.ite hind2 measurable_const measurable_const)
    exact Measurable.ite (measurable_fst (measurableSet_singleton M.crucial))
      ((Measurable.ite hindarm measurable_const measurable_const).const_mul 2) measurable_const
  have hbd : ∀ z, |f z| ≤ 2 := by
    intro z
    rw [hfEq z, abs_mul, abs_mul]
    have b1 : |(if Step.state z = i then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    have c1 : |(if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0)
        else 1)| ≤ 2 := by split_ifs <;> norm_num
    have c2 : |(if Step.next z = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    have hinner := mul_le_mul c1 c2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have houter := mul_le_mul b1 hinner (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hfint : Integrable f ν :=
    (integrable_const (2 : ℝ)).mono' hfmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hbd z)
  show ∫ z, f z ∂ν = _
  rw [integral_eq_integral_stepLaw M ν hinv hfmeas hfint]
  have hstep : ∀ z : Step S,
      ∫ p, f (Step.state z, p) ∂(stepLaw M (Step.state z))
        = (if Step.state z = i then (1 : ℝ) else 0) * M.polTrans a i j := by
    intro z
    have h1 : ∀ p : Bool × S × ℝ, f (Step.state z, p)
        = (if Step.state z = i then (1 : ℝ) else 0)
          * ((if Step.state z = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
            * (if p.2.1 = j then (1 : ℝ) else 0)) := fun p => hfEq (Step.state z, p)
    rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul,
      integral_stepLaw_indicator M (Step.state z) j a]
    by_cases h : Step.state z = i
    · rw [h]; rfl
    · simp [h]
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep), integral_mul_const]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The population reward statistic of the information-sharing scheme. -/
lemma meanObs_IS_rwd (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν) (a : Bool) (i : S) :
    (meanObs M .IS ν a).2 i
      = (∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν) * M.polReward a i := by
  classical
  have hind : MeasurableSet {z : Step S | Step.state z = i} :=
    measurable_fst (measurableSet_singleton i)
  have hindarm : MeasurableSet {z : Step S | Step.arm z = a} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton a)
  set f : Step S → ℝ := fun z => (estObs M .IS z a).2 i with hf
  have hfEq : ∀ z : Step S, f z
      = (if Step.state z = i then (1 : ℝ) else 0)
        * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
          * Step.rwd z) := by
    intro z
    rw [hf]
    simp only [estObs, schemeWeight]
    by_cases h1 : Step.state z = i <;> simp [h1]
  have hrwdmeas : Measurable (fun z : Step S => Step.rwd z) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hfmeas : Measurable f := by
    rw [funext hfEq]
    refine Measurable.mul (Measurable.ite hind measurable_const measurable_const) ?_
    refine Measurable.mul ?_ hrwdmeas
    exact Measurable.ite (measurable_fst (measurableSet_singleton M.crucial))
      ((Measurable.ite hindarm measurable_const measurable_const).const_mul 2) measurable_const
  have hbd : ∀ z, |f z| ≤ 2 * |Step.rwd z| := by
    intro z
    rw [hfEq z, abs_mul, abs_mul]
    have b1 : |(if Step.state z = i then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    have c1 : |(if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0)
        else 1)| ≤ 2 := by split_ifs <;> norm_num
    have hinner : |(if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0)
        else 1)| * |Step.rwd z| ≤ 2 * |Step.rwd z| :=
      mul_le_mul_of_nonneg_right c1 (abs_nonneg _)
    have houter := mul_le_mul b1 hinner (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hfint : Integrable f ν := by
    refine (hrint.abs.const_mul 2).mono' hfmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using hbd z
  show ∫ z, f z ∂ν = _
  rw [integral_eq_integral_stepLaw M ν hinv hfmeas hfint]
  have hstep : ∀ z : Step S,
      ∫ p, f (Step.state z, p) ∂(stepLaw M (Step.state z))
        = (if Step.state z = i then (1 : ℝ) else 0) * M.polReward a i := by
    intro z
    have h1 : ∀ p : Bool × S × ℝ, f (Step.state z, p)
        = (if Step.state z = i then (1 : ℝ) else 0)
          * ((if Step.state z = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
            * p.2.2) := fun p => hfEq (Step.state z, p)
    rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul,
      integral_stepLaw_rwd M (Step.state z) a hR]
    by_cases h : Step.state z = i
    · rw [h]
    · simp [h]
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep), integral_mul_const]

/-- The total population count at a state is its stationary visit probability. -/
lemma meanObs_IS_visit (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (a : Bool) (i : S) :
    ∑ k, (meanObs M .IS ν a).1 i k
      = ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν := by
  simp_rw [meanObs_IS_trans M ν hinv a i]
  rw [← Finset.mul_sum]
  have h : ∑ k, M.polTrans a i k = 1 := pmf_sum_toReal (M.trans i (M.act a i))
  rw [h, mul_one]

/-- **Fisher consistency of the plug-in transition estimate.** -/
theorem mbTrans_meanObs_IS (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    mbTrans (meanObs M .IS ν) a = M.polTrans a := by
  ext i j
  rw [mbTrans, Matrix.of_apply, meanObs_IS_trans M ν hinv a i j,
    meanObs_IS_visit M ν hinv a i]
  exact mul_div_cancel_left₀ _ (hμ i)

/-- **Fisher consistency of the plug-in reward estimate.** -/
theorem mbReward_meanObs_IS (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    mbReward (meanObs M .IS ν) a = M.polReward a := by
  funext i
  rw [mbReward, meanObs_IS_rwd M ν hinv hR hrint a i, meanObs_IS_visit M ν hinv a i]
  exact mul_div_cancel_left₀ _ (hμ i)

/-- **Fisher consistency of the model-based estimator**: at the population statistics of
the information-sharing scheme the plug-in value function is the true value function. -/
theorem mbValue_meanObs_IS (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    mbValue M (meanObs M .IS ν) a = M.value a := by
  rw [mbValue, mbTrans_meanObs_IS M ν hinv hμ a,
    mbReward_meanObs_IS M ν hinv hR hrint hμ a, Model.value]

end TreatmentLocality

end

-- === tl_pert.lean ===
section



open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma perturbCoef_nonneg (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (s : S) (a : Bool) (j : S) :
    0 ≤ perturbCoef M β t s a j := by
  rw [perturbCoef]
  split_ifs
  · exact mul_nonneg ENNReal.toReal_nonneg (ht s a j)
  · exact ENNReal.toReal_nonneg

lemma perturbCoef_sum (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (s : S) (a : Bool) : ∑ j, perturbCoef M β t s a j = 1 := by
  simp only [perturbCoef]
  by_cases hact : M.act a s = a
  · simp only [if_pos hact]
    have hterm : ∀ j : S, (M.trans s a j).toReal * (1 + t * β s a j)
        = (M.trans s a j).toReal + t * ((M.trans s a j).toReal * β s a j) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum]
    have h0 : ∑ j, (M.trans s a j).toReal * β s a j = 0 := by
      have := hcent s a
      rwa [hact] at this
    rw [h0, pmf_sum_toReal (M.trans s a), mul_zero, add_zero]
  · simp only [if_neg hact]
    exact pmf_sum_toReal (M.trans s a)

lemma perturbTrans_eq (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (s : S) (a : Bool) (j : S) :
    perturbTrans M β t s a j = ENNReal.ofReal (perturbCoef M β t s a j) := by
  have hsum : (∑ j, ENNReal.ofReal (perturbCoef M β t s a j)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => perturbCoef_nonneg M β t ht s a j),
      perturbCoef_sum M β t hcent s a, ENNReal.ofReal_one]
  rw [perturbTrans, dif_pos hsum, PMF.ofFintype_apply]

/-- The perturbed transitions are strictly positive whenever the original ones are. -/
theorem perturbTrans_pos (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ht : ∀ s a j, 0 < 1 + t * β s a j)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j) (s : S) (a : Bool) (j : S) :
    0 < perturbTrans M β t s (M.act a s) j := by
  have ht' : ∀ s a j, 0 ≤ 1 + t * β s a j := fun s a j => (ht s a j).le
  rw [perturbTrans_eq M β t hcent ht']
  rw [ENNReal.ofReal_pos, perturbCoef]
  have hP : 0 < (M.trans s (M.act a s) j).toReal := by
    refine ENNReal.toReal_pos (ne_of_gt (hpos s a j)) ?_
    exact PMF.apply_ne_top _ _
  split_ifs
  · exact mul_pos hP (ht s (M.act a s) j)
  · exact hP

/-- For small perturbations the transition weights stay positive. -/
theorem exists_perturb_radius (β : S → Bool → S → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ s a j, 0 < 1 + t * β s a j := by
  classical
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ s a j, |β s a j| ≤ B :=
    ⟨∑ x : S, ∑ b : Bool, ∑ y : S, |β x b y|,
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun b _ =>
        Finset.sum_nonneg fun y _ => abs_nonneg _,
      fun s a j => by
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun x : S => ∑ b : Bool, ∑ y : S, |β x b y|)
          (fun x _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun y _ => abs_nonneg _)
          (Finset.mem_univ s))
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun b : Bool => ∑ y : S, |β s b y|)
          (fun b _ => Finset.sum_nonneg fun y _ => abs_nonneg _) (Finset.mem_univ a))
        exact Finset.single_le_sum (f := fun y : S => |β s a y|)
          (fun y _ => abs_nonneg _) (Finset.mem_univ j)⟩
  refine ⟨(B + 1)⁻¹, by positivity, fun t htlt s a j => ?_⟩
  have hbd : |t * β s a j| < 1 := by
    rw [abs_mul]
    calc |t| * |β s a j| ≤ |t| * B := mul_le_mul_of_nonneg_left (hB s a j) (abs_nonneg _)
      _ ≤ |t| * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ < (B + 1)⁻¹ * (B + 1) := mul_lt_mul_of_pos_right htlt (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have := abs_lt.1 hbd
  linarith [this.1]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The perturbation stays inside the SST family.** For all small enough `t` the
perturbed model has the same crucial state, discount factor and reward variances, keeps
strictly positive transitions, and its transition weights are the explicit perturbed
weights. -/
theorem perturbModel_isSST (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      (perturbModel M m v α β t).crucial = M.crucial ∧
      (perturbModel M m v α β t).γdisc = M.γdisc ∧
      (perturbModel M m v α β t).GaussianRewards
        (fun s a => m s a + t * α s a * (v s a : ℝ)) v ∧
      (∀ s a j, 0 < (perturbModel M m v α β t).trans s
        ((perturbModel M m v α β t).act a s) j) ∧
      (∀ s a j, ((perturbModel M m v α β t).trans s a j).toReal
        = perturbCoef M β t s a j) := by
  obtain ⟨ε, hε0, hε⟩ := exists_perturb_radius (S := S) β
  refine ⟨ε, hε0, fun t ht => ⟨rfl, rfl, perturbModel_gaussianRewards M m v α β t,
    fun s a j => perturbTrans_pos M β t hcent (hε t ht) hpos s a j, fun s a j => ?_⟩⟩
  rw [show (perturbModel M m v α β t).trans = perturbTrans M β t from rfl,
    perturbTrans_eq M β t hcent (fun s a j => (hε t ht s a j).le),
    ENNReal.toReal_ofReal (perturbCoef_nonneg M β t (fun s a j => (hε t ht s a j).le) s a j)]

end TreatmentLocality

end

-- === tl_iid.lean ===
section



open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma expKernel_eq_obsKernel (M : Model S) (z : Step S) :
    expKernel M z = obsKernel M (Step.next z) := by
  rw [expKernel_apply, obsKernel_apply]

/-- Under an invariant law the current state and the next state have the same law. -/
lemma map_next_eq_map_state (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) :
    Measure.map Step.next ν = Measure.map Step.state ν := by
  have hnx : Measurable (Step.next : Step S → S) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hst : Measurable (Step.state : Step S → S) := measurable_fst
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hnx hA, Measure.map_apply hst hA]
  have hgm : Measurable (fun s : S => Set.indicator A (fun _ => (1 : ℝ)) s) :=
    measurable_of_countable _
  have h := integral_state_eq_integral_next M ν hinv
    (fun s => Set.indicator A (fun _ => (1 : ℝ)) s)
  have hL : (fun z : Step S => Set.indicator A (fun _ => (1 : ℝ)) (Step.state z))
      = Set.indicator (Step.state ⁻¹' A) (fun _ => (1 : ℝ)) := by
    funext z; by_cases hz : Step.state z ∈ A <;> simp [Set.indicator, hz]
  have hR : (fun z : Step S => Set.indicator A (fun _ => (1 : ℝ)) (Step.next z))
      = Set.indicator (Step.next ⁻¹' A) (fun _ => (1 : ℝ)) := by
    funext z; by_cases hz : Step.next z ∈ A <;> simp [Set.indicator, hz]
  rw [hL, hR, integral_indicator_const (1 : ℝ) (hst hA),
    integral_indicator_const (1 : ℝ) (hnx hA)] at h
  simp only [smul_eq_mul, mul_one, Measure.real] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν _) (measure_ne_top ν _)).1 h.symm

/-- **An invariant law of the experiment chain is the observation law of its own state
marginal**: the observations of the stationary experiment are, one at a time, draws of a
state from `μ` followed by one step of the mixed policy. -/
theorem obsLaw_map_state (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) :
    obsLaw M (Measure.map Step.state ν) = ν := by
  have hnx : Measurable (Step.next : Step S → S) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  rw [obsLaw, ← map_next_eq_map_state M ν hinv]
  refine Measure.ext fun A hA => ?_
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hA) hnx]
  conv_rhs => rw [← hinv]
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  exact (lintegral_congr fun z => by rw [expKernel_eq_obsKernel]).symm

end TreatmentLocality

end

-- === tl_deriv.lean ===
section



open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma act_idem (M : Model S) (a : Bool) (s : S) : M.act (M.act a s) s = M.act a s := by
  cases a <;> simp [Model.act]

/-- The derivative of the transition matrix along the perturbation. -/
noncomputable def dTrans (M : Model S) (β : S → Bool → S → ℝ) (a : Bool) : Matrix S S ℝ :=
  Matrix.of fun i j => M.polTrans a i j * β i (M.act a i) j

/-- The derivative of the mean-reward vector along the perturbation. -/
noncomputable def dReward (M : Model S) (v : S → Bool → ℝ≥0) (α : S → Bool → ℝ) (a : Bool) :
    S → ℝ := fun i => α i (M.act a i) * (v i (M.act a i) : ℝ)

lemma perturbModel_polTrans (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    {t : ℝ} (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (a : Bool) :
    (perturbModel M m v α β t).polTrans a = M.polTrans a + t • dTrans M β a := by
  ext i j
  have hact : M.act (M.act a i) i = M.act a i := act_idem M a i
  rw [Model.polTrans, Matrix.of_apply,
    show (perturbModel M m v α β t).act a i = M.act a i from rfl,
    show (perturbModel M m v α β t).trans = perturbTrans M β t from rfl,
    perturbTrans_eq M β t hcent ht,
    ENNReal.toReal_ofReal (perturbCoef_nonneg M β t ht i (M.act a i) j), perturbCoef,
    if_pos hact]
  simp only [Matrix.add_apply, Matrix.smul_apply, dTrans, Matrix.of_apply, smul_eq_mul,
    Model.polTrans]
  ring

lemma perturbModel_polReward (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) (a : Bool) (i : S) :
    (perturbModel M m v α β t).polReward a i
      = m i (M.act a i) + t * (dReward M v α a i) := by
  rw [Model.polReward, show (perturbModel M m v α β t).act a i = M.act a i from rfl,
    show (perturbModel M m v α β t).reward = fun s b =>
      gaussianReal (m s b + t * α s b * (v s b : ℝ)) (v s b) from rfl]
  rw [integral_id_gaussianReal]
  rw [dReward]
  ring

lemma polReward_zero (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (a : Bool) (i : S) :
    M.polReward a i = m i (M.act a i) := by
  rw [Model.polReward, hgauss i (M.act a i), integral_id_gaussianReal]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The entry map of a matrix, as a continuous linear map. -/
noncomputable def entryCLM (i j : S) : Matrix S S ℝ →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

@[simp] lemma entryCLM_apply (i j : S) (A : Matrix S S ℝ) : entryCLM i j A = A i j := rfl

/-- **The derivative of the policy value along the perturbation.** -/
theorem hasDerivAt_perturbModel_value (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (a : Bool) (s : S) :
    HasDerivAt (fun t : ℝ => (perturbModel M m v α β t).value a s)
      ((((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹).mulVec
        (fun i => dReward M v α a i
          + M.γdisc * ((dTrans M β a).mulVec (M.value a) i)) s) 0 := by
  classical
  set A0 : Matrix S S ℝ := (1 : Matrix S S ℝ) - M.γdisc • M.polTrans a with hA0def
  set B : Matrix S S ℝ := -(M.γdisc • dTrans M β a) with hBdef
  set Ai : Matrix S S ℝ := A0⁻¹ with hAidef
  set A : ℝ → Matrix S S ℝ := fun t => A0 + t • B with hAdef
  set r : ℝ → S → ℝ := fun t i => m i (M.act a i) + t * dReward M v α a i with hrdef
  have hu : IsUnit A0 := isUnit_one_sub_smul_polTrans M a
  have hri : Ring.inverse A0 = Ai := (Matrix.nonsing_inv_eq_ringInverse A0).symm
  have hr0 : r 0 = M.polReward a := by
    funext i; rw [hrdef]; simp [polReward_zero M m v hgauss a i]
  have hV : Ai.mulVec (r 0) = M.value a := by rw [hr0, hAidef, hA0def, Model.value]
  -- the curve of matrices
  have hdA : HasDerivAt A B 0 := by
    rw [hAdef]
    have h1 : HasDerivAt (fun t : ℝ => t • B) ((1 : ℝ) • B) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const B
    rw [one_smul] at h1
    exact h1.const_add A0
  have hA00 : A 0 = A0 := by simp [hAdef]
  -- the derivative of the inverse
  have hdinv : HasDerivAt (fun t : ℝ => Ring.inverse (A t)) (-(Ai * B * Ai)) 0 := by
    have hval : (↑hu.unit : Matrix S S ℝ) = A0 := hu.unit_spec
    have hinvval : (↑hu.unit⁻¹ : Matrix S S ℝ) = Ai := by
      rw [← Ring.inverse_unit hu.unit, hval, hri]
    have hfd := hasFDerivAt_ringInverse (𝕜 := ℝ) (R := Matrix S S ℝ) hu.unit
    rw [hinvval] at hfd
    have hpt : A 0 = (↑hu.unit : Matrix S S ℝ) := by rw [hA00, hval]
    have hfd2 : HasFDerivAt (Ring.inverse : Matrix S S ℝ → Matrix S S ℝ)
        (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ) Ai Ai)) (A 0) := by
      rw [hpt]; exact hfd
    have hcomp := hfd2.comp_hasDerivAt (0 : ℝ) hdA
    have hval2 : (-ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ) Ai Ai) B
        = -(Ai * B * Ai) := by
      simp [ContinuousLinearMap.mulLeftRight_apply]
    rw [hval2] at hcomp
    exact hcomp
  -- entrywise derivatives
  have hentry : ∀ i : S, HasDerivAt (fun t : ℝ => (Ring.inverse (A t)) s i)
      ((-(Ai * B * Ai)) s i) 0 := fun i =>
    (entryCLM s i).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdinv
  have hdr : ∀ i : S, HasDerivAt (fun t : ℝ => r t i) (dReward M v α a i) 0 := by
    intro i
    have h1 : HasDerivAt (fun t : ℝ => t * dReward M v α a i)
        (1 * dReward M v α a i) 0 := (hasDerivAt_id (0 : ℝ)).mul_const _
    simpa [hrdef] using h1.const_add (m i (M.act a i))
  have hsum0 := HasDerivAt.sum (u := (Finset.univ : Finset S))
    (fun (i : S) (_ : i ∈ Finset.univ) => (hentry i).mul (hdr i))
  have heq : (∑ i ∈ (Finset.univ : Finset S),
      (fun t : ℝ => (Ring.inverse (A t)) s i) * fun t : ℝ => r t i)
      = fun t : ℝ => ∑ i, (Ring.inverse (A t)) s i * r t i := by
    funext t; simp
  rw [heq] at hsum0
  have hsum : HasDerivAt (fun t : ℝ => ∑ i, (Ring.inverse (A t)) s i * r t i)
      (∑ i, ((-(Ai * B * Ai)) s i * r 0 i + (Ring.inverse (A 0)) s i * dReward M v α a i))
      0 := hsum0
  -- identify the derivative
  have hkey : (∑ i, ((-(Ai * B * Ai)) s i * r 0 i + (Ring.inverse (A 0)) s i
        * dReward M v α a i))
      = (Ai.mulVec (fun i => dReward M v α a i
          + M.γdisc * ((dTrans M β a).mulVec (M.value a) i)) s) := by
    rw [hA00, hri]
    have e1 : ∑ i, ((-(Ai * B * Ai)) s i * r 0 i)
        = (-(Ai * B * Ai)).mulVec (r 0) s := rfl
    have e2 : (-(Ai * B * Ai)).mulVec (r 0)
        = fun x => -(Ai.mulVec (B.mulVec (Ai.mulVec (r 0))) x) := by
      funext x
      rw [Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp
    have e3 : B.mulVec (M.value a) = -(M.γdisc • (dTrans M β a).mulVec (M.value a)) := by
      rw [hBdef, Matrix.neg_mulVec, Matrix.smul_mulVec]
    rw [Finset.sum_add_distrib, e1, e2, hV, e3]
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Matrix.smul_mulVec,
      Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hkey] at hsum
  -- transfer along the eventual equality
  obtain ⟨ε, hε0, hε⟩ := exists_perturb_radius (S := S) β
  have hball : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε0] with t ht
    simpa [Real.dist_eq] using ht
  refine hsum.congr_of_eventuallyEq ?_
  · filter_upwards [hball] with t ht
    have hpos : ∀ s a j, 0 ≤ 1 + t * β s a j := fun s a j => (hε t ht s a j).le
    rw [Model.value, show (perturbModel M m v α β t).γdisc = M.γdisc from rfl,
      perturbModel_polTrans M m v α β hcent hpos a]
    have hrw : (perturbModel M m v α β t).polReward a = r t := by
      funext i
      rw [perturbModel_polReward, hrdef]
    rw [hrw]
    have hAeq : (1 : Matrix S S ℝ) - M.γdisc • (M.polTrans a + t • dTrans M β a) = A t := by
      rw [hAdef, hBdef, hA0def]
      rw [smul_add, smul_smul]
      simp [sub_add_eq_sub_sub, mul_comm]
      ring_nf
      module
    rw [hAeq, Matrix.nonsing_inv_eq_ringInverse]
    rfl

end TreatmentLocality

end

-- === tl_dens.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The likelihood ratio carried by one observation under the perturbation
`(α, β)` at parameter `t`. -/
noncomputable def pertDens (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) (z : Step S) : ℝ :=
  (1 + t * β (Step.state z) (M.act (Step.arm z) (Step.state z)) (Step.next z))
    * rexp (t * α (Step.state z) (M.act (Step.arm z) (Step.state z))
        * (Step.rwd z - m (Step.state z) (M.act (Step.arm z) (Step.state z)))
      - t ^ 2 * (α (Step.state z) (M.act (Step.arm z) (Step.state z))) ^ 2
        * (v (Step.state z) (M.act (Step.arm z) (Step.state z)) : ℝ) / 2)

/-- **The transition tilt.**  On an executed state-action pair the perturbed transition law
is the true one tilted by the affine density `1 + tβ`. -/
theorem perturbTrans_toMeasure (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (s : S) (γ : Bool) :
    (perturbTrans M β t s (M.act γ s)).toMeasure
      = ((M.trans s (M.act γ s)).toMeasure).withDensity
          (fun j => ENNReal.ofReal (1 + t * β s (M.act γ s) j)) := by
  have hmeas : Measurable (fun j : S => ENNReal.ofReal (1 + t * β s (M.act γ s) j)) :=
    measurable_of_countable _
  refine Measure.ext_of_singleton fun j => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j),
    withDensity_apply _ (measurableSet_singleton j), lintegral_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j),
    perturbTrans_eq M β t hcent ht,
    show perturbCoef M β t s (M.act γ s) j
      = (M.trans s (M.act γ s) j).toReal * (1 + t * β s (M.act γ s) j) by
      rw [perturbCoef, if_pos (act_idem M γ s)],
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  ring

/-- **The reward tilt.**  The perturbed reward law is the true one tilted by the Gaussian
likelihood ratio of the mean shift `t α v`. -/
theorem perturbModel_reward_withDensity (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) (s : S) (a : Bool) :
    (perturbModel M m v α β t).reward s a
      = (M.reward s a).withDensity (fun r => ENNReal.ofReal
          (rexp (t * α s a * (r - m s a) - t ^ 2 * (α s a) ^ 2 * (v s a : ℝ) / 2))) := by
  by_cases hvz : v s a = 0
  · have hone : (fun r : ℝ => ENNReal.ofReal
        (rexp (t * α s a * (r - m s a) - t ^ 2 * (α s a) ^ 2 * (v s a : ℝ) / 2))) (m s a) = 1 := by
      simp [hvz]
    rw [show (perturbModel M m v α β t).reward s a
        = gaussianReal (m s a + t * α s a * (v s a : ℝ)) (v s a) from rfl, hgauss s a, hvz]
    simp only [NNReal.coe_zero, mul_zero, add_zero, gaussianReal_zero_var]
    classical
    refine Measure.ext fun A hA => ?_
    rw [withDensity_apply _ hA, MeasureTheory.restrict_dirac' hA]
    by_cases hmem : m s a ∈ A
    · rw [if_pos hmem, lintegral_dirac' _ (by fun_prop)]
      simpa [hvz, Measure.dirac_apply' _ hA, Set.indicator_of_mem hmem] using hone
    · rw [if_neg hmem]
      simp [Measure.dirac_apply' _ hA, Set.indicator_of_notMem hmem]
  have hv0 : (0 : ℝ) < (v s a : ℝ) :=
    lt_of_le_of_ne (v s a).coe_nonneg (fun hc => hvz (NNReal.coe_eq_zero.mp hc.symm))
  have hshift := Statistics.gaussianReal_shift (m s a) hvz (t * α s a * (v s a : ℝ))
  rw [show (perturbModel M m v α β t).reward s a
      = gaussianReal (m s a + t * α s a * (v s a : ℝ)) (v s a) from rfl, hshift, hgauss s a]
  congr 1
  funext r
  congr 2
  field_simp

/-- **The one-step tilt.**  The perturbed experiment step law is the true one tilted by the
one-observation likelihood ratio. -/
theorem stepLaw_perturbModel (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (s : S) :
    stepLaw (perturbModel M m v α β t) s
      = (stepLaw M s).withDensity
          (fun q : Bool × S × ℝ => ENNReal.ofReal (pertDens M m v α β t (s, q))) := by
  have hg : Measurable (fun q : Bool × S × ℝ =>
      ENNReal.ofReal (pertDens M m v α β t (s, q))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    simp only [pertDens, Step.state, Step.arm, Step.next, Step.rwd]
    fun_prop
  have key : ∀ γ : Bool,
      (Measure.dirac γ).prod
          (((perturbTrans M β t s (M.act γ s)).toMeasure).prod
            ((perturbModel M m v α β t).reward s (M.act γ s)))
        = ((Measure.dirac γ).prod
            (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))).withDensity
          (fun q : Bool × S × ℝ => ENNReal.ofReal (pertDens M m v α β t (s, q))) := by
    intro γ
    have hf1 : Measurable (fun j : S => ENNReal.ofReal (1 + t * β s (M.act γ s) j)) :=
      measurable_of_countable _
    have hf2 : Measurable (fun r : ℝ => ENNReal.ofReal
        (rexp (t * α s (M.act γ s) * (r - m s (M.act γ s))
          - t ^ 2 * (α s (M.act γ s)) ^ 2 * (v s (M.act γ s) : ℝ) / 2))) := by fun_prop
    haveI h1 : IsProbabilityMeasure (((M.trans s (M.act γ s)).toMeasure).withDensity
        (fun j => ENNReal.ofReal (1 + t * β s (M.act γ s) j))) := by
      rw [← perturbTrans_toMeasure M β t hcent ht s γ]; infer_instance
    haveI h2 : IsProbabilityMeasure ((M.reward s (M.act γ s)).withDensity
        (fun r => ENNReal.ofReal (rexp (t * α s (M.act γ s) * (r - m s (M.act γ s))
          - t ^ 2 * (α s (M.act γ s)) ^ 2 * (v s (M.act γ s) : ℝ) / 2)))) := by
      rw [← perturbModel_reward_withDensity M m v hgauss α β t s (M.act γ s)]
      exact (perturbModel M m v α β t).reward_prob _ _
    rw [Measure.dirac_prod, Measure.dirac_prod, Statistics.withDensity_map_prodMk _ _ hg]
    congr 1
    rw [perturbTrans_toMeasure M β t hcent ht s γ,
      perturbModel_reward_withDensity M m v hgauss α β t s (M.act γ s),
      ← Statistics.prod_withDensity _ _ hf1 hf2]
    congr 1
    funext y
    rw [← ENNReal.ofReal_mul (ht s (M.act γ s) y.1)]
    rfl
  rw [show stepLaw (perturbModel M m v α β t) s
      = (2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true).prod
          (((perturbTrans M β t s (M.act true s)).toMeasure).prod
            ((perturbModel M m v α β t).reward s (M.act true s)))
        + (Measure.dirac false).prod
          (((perturbTrans M β t s (M.act false s)).toMeasure).prod
            ((perturbModel M m v α β t).reward s (M.act false s)))) from rfl,
    key true, key false, stepLaw, withDensity_smul_measure, withDensity_add_measure]

variable (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
  (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ)

lemma measurable_pertDens :
    Measurable (fun z : Step S => ENNReal.ofReal (pertDens M m v α β t z)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  show Measurable fun z : Step S => pertDens M m v α β t z
  simp only [pertDens, Step.state, Step.arm, Step.next, Step.rwd]
  fun_prop

/-- **The observation-kernel tilt.** -/
theorem obsKernel_perturbModel (hgauss : M.GaussianRewards m v)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (s : S) :
    obsKernel (perturbModel M m v α β t) s
      = (obsKernel M s).withDensity (fun z => ENNReal.ofReal (pertDens M m v α β t z)) := by
  rw [obsKernel_apply, obsKernel_apply, Measure.dirac_prod, Measure.dirac_prod,
    Statistics.withDensity_map_prodMk _ _ (measurable_pertDens M m v α β t),
    stepLaw_perturbModel M m v hgauss α β t hcent ht s]

/-- **The observation-law tilt.**  Under any initial state distribution the perturbed
one-observation law is the true one tilted by the explicit likelihood ratio. -/
theorem obsLaw_perturbModel (hgauss : M.GaussianRewards m v)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (μ : Measure S) [IsProbabilityMeasure μ] :
    obsLaw (perturbModel M m v α β t) μ
      = (obsLaw M μ).withDensity (fun z => ENNReal.ofReal (pertDens M m v α β t z)) := by
  have hg := measurable_pertDens M m v α β t
  ext A hA
  rw [obsLaw, obsLaw, Measure.bind_apply hA (Kernel.aemeasurable _),
    withDensity_apply _ hA, ← lintegral_indicator hA, Measure.lintegral_bind
      (Kernel.aemeasurable _) ((hg.indicator hA).aemeasurable)]
  refine lintegral_congr fun s => ?_
  rw [obsKernel_perturbModel M m v α β t hgauss hcent ht s, withDensity_apply _ hA,
    ← lintegral_indicator hA]

end TreatmentLocality

end

-- === tl_mom.lean ===
section



open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma measurable_rwd : Measurable (fun z : Step S => Step.rwd z) :=
  measurable_snd.comp (measurable_snd.comp measurable_snd)

/-- The reward coordinate under the one-step experiment law is dominated, uniformly in
the state, by the total moment over the finitely many state-action pairs. -/
lemma lintegral_stepLaw_rwd_le (M : Model S) {F : ℝ → ℝ≥0∞} (hF : Measurable F) (s : S) :
    ∫⁻ p : Bool × S × ℝ, F p.2.2 ∂(stepLaw M s)
      ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun p : Bool × S × ℝ => F p.2.2) :=
    hF.comp (measurable_snd.comp measurable_snd)
  have harm : ∀ γ : Bool,
      ∫⁻ p : Bool × S × ℝ, F p.2.2 ∂((Measure.dirac γ).prod
          (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))))
        = ∫⁻ r, F r ∂(M.reward s (M.act γ s)) := by
    intro γ
    rw [Measure.dirac_prod, lintegral_map hFm measurable_prodMk_left]
    have h1 : Measure.map Prod.snd
        (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
        = M.reward s (M.act γ s) := by
      rw [Measure.map_snd_prod]; simp
    calc ∫⁻ q : S × ℝ, F (γ, q).2.2
            ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
        = ∫⁻ q : S × ℝ, F q.2
            ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := rfl
      _ = ∫⁻ r, F r ∂(Measure.map Prod.snd
            (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) :=
            (lintegral_map hF measurable_snd).symm
      _ = ∫⁻ r, F r ∂(M.reward s (M.act γ s)) := by rw [h1]
  have hle : ∀ γ : Bool, ∫⁻ r, F r ∂(M.reward s (M.act γ s))
      ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
    intro γ
    calc ∫⁻ r, F r ∂(M.reward s (M.act γ s))
        ≤ ∑ a : Bool, ∫⁻ r, F r ∂(M.reward s a) :=
          Finset.single_le_sum (f := fun a : Bool => ∫⁻ r, F r ∂(M.reward s a))
            (fun a _ => bot_le) (Finset.mem_univ (M.act γ s))
      _ ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) :=
          Finset.single_le_sum (f := fun t : S => ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a))
            (fun t _ => bot_le) (Finset.mem_univ s)
  rw [stepLaw, lintegral_smul_measure, lintegral_add_measure, harm true, harm false]
  set B := ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) with hB
  calc (2 : ℝ≥0∞)⁻¹ * ((∫⁻ r, F r ∂(M.reward s (M.act true s)))
          + ∫⁻ r, F r ∂(M.reward s (M.act false s)))
      ≤ (2 : ℝ≥0∞)⁻¹ * (B + B) := by
        gcongr <;> [exact hle true; exact hle false]
    _ = B := by
        rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The same bound along the experiment kernel. -/
lemma lintegral_expKernel_rwd_le (M : Model S) {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (z : Step S) :
    ∫⁻ w : Step S, F (Step.rwd w) ∂(expKernel M z)
      ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun w : Step S => F (Step.rwd w)) := hF.comp measurable_rwd
  rw [expKernel_apply, Measure.dirac_prod, lintegral_map hFm measurable_prodMk_left]
  exact lintegral_stepLaw_rwd_le M hF (Step.next z)

/-- The reward moment under an invariant law is bounded by the total moment over the
finitely many state-action pairs. -/
lemma lintegral_rwd_le_of_invariant (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (Step.rwd z) ∂ν ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun w : Step S => F (Step.rwd w)) := hF.comp measurable_rwd
  conv_lhs => rw [← hinv]
  have h1 : ν.bind (expKernel M) = ((expKernel M) ∘ₖ (Kernel.const Unit ν)) () := rfl
  rw [h1, Kernel.lintegral_comp _ _ _ hFm, Kernel.const_apply]
  calc ∫⁻ z, (∫⁻ w, F (Step.rwd w) ∂(expKernel M z)) ∂ν
      ≤ ∫⁻ _z : Step S, (∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a)) ∂ν :=
        lintegral_mono fun z => lintegral_expKernel_rwd_le M hF z
    _ = ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
        rw [lintegral_const, measure_univ, mul_one]

/-- The same bound along any positive number of steps of the chain. -/
lemma lintegral_iterKernel_rwd_le (M : Model S) {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (k : ℕ) (x : Step S) :
    ∫⁻ w : Step S, F (Step.rwd w) ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) x)
      ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun w : Step S => F (Step.rwd w)) := hF.comp measurable_rwd
  rw [MarkovChainCLT.iterKernel_succ, Kernel.lintegral_comp _ _ _ hFm]
  calc ∫⁻ y, (∫⁻ w, F (Step.rwd w) ∂(expKernel M y))
          ∂(MarkovChainCLT.iterKernel (expKernel M) k x)
      ≤ ∫⁻ _y : Step S, (∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a))
          ∂(MarkovChainCLT.iterKernel (expKernel M) k x) :=
        lintegral_mono fun y => lintegral_expKernel_rwd_le M hF y
    _ = ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
        rw [lintegral_const, measure_univ, mul_one]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- Gaussian rewards have a first moment. -/
lemma integrable_reward_of_gaussian (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (t : S) (a : Bool) :
    Integrable (fun r : ℝ => r) (M.reward t a) := by
  rw [hgauss t a]
  exact (memLp_id_gaussianReal (μ := m t a) (v := v t a) 1).integrable le_rfl

/-- Gaussian rewards have a second moment. -/
lemma memLp_reward_of_gaussian (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (t : S) (a : Bool) :
    MemLp (fun r : ℝ => r) 2 (M.reward t a) := by
  rw [hgauss t a]
  exact memLp_id_gaussianReal (μ := m t a) (v := v t a) 2

/-- Under an invariant law the reward coordinate is integrable. -/
theorem integrable_rwd_of_invariant (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) :
    Integrable (fun z : Step S => Step.rwd z) ν := by
  refine ⟨measurable_rwd.aestronglyMeasurable, lt_of_le_of_lt
    (lintegral_rwd_le_of_invariant M ν hinv (F := fun r : ℝ => ‖r‖ₑ) measurable_id.enorm) ?_⟩
  exact ENNReal.sum_lt_top.2 fun t _ => ENNReal.sum_lt_top.2 fun a _ => (hR t a).2

/-- Under an invariant law the reward coordinate is square-integrable. -/
theorem memLp_rwd_of_invariant (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR2 : ∀ t a, MemLp (fun r : ℝ => r) 2 (M.reward t a)) :
    MemLp (fun z : Step S => Step.rwd z) 2 ν := by
  rw [memLp_two_iff_integrable_sq measurable_rwd.aestronglyMeasurable]
  refine ⟨(measurable_rwd.pow_const 2).aestronglyMeasurable, lt_of_le_of_lt
    (lintegral_rwd_le_of_invariant M ν hinv (F := fun r : ℝ => ‖r ^ 2‖ₑ)
      (measurable_id.pow_const 2).enorm) ?_⟩
  refine ENNReal.sum_lt_top.2 fun t _ => ENNReal.sum_lt_top.2 fun a _ => ?_
  exact ((memLp_two_iff_integrable_sq
    (measurable_id : Measurable fun r : ℝ => r).aestronglyMeasurable).1 (hR2 t a)).2

/-- The reward coordinate is integrable along every step of the chain. -/
theorem integrable_rwd_iterKernel (M : Model S)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) (k : ℕ) (x : Step S) :
    Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x) := by
  cases k with
  | zero =>
      rw [MarkovChainCLT.iterKernel_zero, Kernel.id_apply]
      refine ⟨measurable_rwd.aestronglyMeasurable, ?_⟩
      have : ∫⁻ z : Step S, ‖Step.rwd z‖ₑ ∂(Measure.dirac x) = ‖Step.rwd x‖ₑ :=
        lintegral_dirac' _ measurable_rwd.enorm
      show ∫⁻ z : Step S, ‖Step.rwd z‖ₑ ∂(Measure.dirac x) < ⊤
      rw [this]
      exact enorm_lt_top
  | succ j =>
      refine ⟨measurable_rwd.aestronglyMeasurable, lt_of_le_of_lt
        (lintegral_iterKernel_rwd_le M (F := fun r : ℝ => ‖r‖ₑ) measurable_id.enorm j x) ?_⟩
      exact ENNReal.sum_lt_top.2 fun t _ => ENNReal.sum_lt_top.2 fun a _ => (hR t a).2

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma measurableSet_state_eq (i : S) : MeasurableSet {z : Step S | Step.state z = i} :=
  measurable_fst (measurableSet_singleton i)

lemma measurableSet_next_eq (i : S) : MeasurableSet {z : Step S | Step.next z = i} :=
  (measurable_fst.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton i)

lemma expKernel_state_eq (M : Model S) (i : S) (z : Step S) :
    (expKernel M z) {w : Step S | Step.state w = i}
      = if Step.next z = i then (1 : ℝ≥0∞) else 0 := by
  have hset : {w : Step S | Step.state w = i}
      = ({i} : Set S) ×ˢ (Set.univ : Set (Bool × S × ℝ)) := by
    ext w; simp [Step.state, Set.mem_prod]
  rw [expKernel_apply, hset, Measure.prod_prod, measure_univ, mul_one,
    MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton i)]
  by_cases h : Step.next z = i <;> simp [Set.indicator, h]

lemma expKernel_next_eq (M : Model S) (i : S) (z : Step S) :
    (expKernel M z) {w : Step S | Step.next w = i}
      = (stepLaw M (Step.next z)) {p : Bool × S × ℝ | p.2.1 = i} := by
  have hset : {w : Step S | Step.next w = i}
      = (Set.univ : Set S) ×ˢ {p : Bool × S × ℝ | p.2.1 = i} := by
    ext w; simp [Step.next, Set.mem_prod]
  rw [expKernel_apply, hset, Measure.prod_prod, measure_univ, one_mul]

lemma stepLaw_next_eq_ge (M : Model S) (i s : S) :
    (2 : ℝ≥0∞)⁻¹ * M.trans s (M.act true s) i
      ≤ (stepLaw M s) {p : Bool × S × ℝ | p.2.1 = i} := by
  have hset : {p : Bool × S × ℝ | p.2.1 = i}
      = (Set.univ : Set Bool) ×ˢ (({i} : Set S) ×ˢ (Set.univ : Set ℝ)) := by
    ext p; simp [Set.mem_prod]
  have harm : ∀ γ : Bool, ((Measure.dirac γ).prod
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))))
      {p : Bool × S × ℝ | p.2.1 = i} = M.trans s (M.act γ s) i := by
    intro γ
    rw [hset, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, one_mul,
      mul_one, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  rw [stepLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul, harm true, harm false]
  exact mul_le_mul' le_rfl (le_self_add)

/-- With strictly positive transitions every state has positive stationary visit
probability. -/
theorem visit_ne_zero_of_trans_pos (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j) (i : S) :
    ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0 := by
  classical
  have hbind : ∀ A : Set (Step S), MeasurableSet A →
      ν A = ∫⁻ z, (expKernel M z) A ∂ν := by
    intro A hA
    conv_lhs => rw [← hinv]
    exact Measure.bind_apply hA (Kernel.aemeasurable _)
  have hne : (Finset.univ : Finset S).Nonempty := ⟨i, Finset.mem_univ i⟩
  set ε : ℝ≥0∞ :=
    (2 : ℝ≥0∞)⁻¹ * Finset.univ.inf' hne (fun s => M.trans s (M.act true s) i) with hεdef
  have hε0 : 0 < ε := by
    refine ENNReal.mul_pos (by norm_num) (ne_of_gt ?_)
    exact (Finset.lt_inf'_iff hne).2 fun s _ => hpos s true i
  -- the next state hits `i` with probability at least ε
  have hnext : ε ≤ ν {z : Step S | Step.next z = i} := by
    rw [hbind _ (measurableSet_next_eq i)]
    calc ε = ∫⁻ _z : Step S, ε ∂ν := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ z, (expKernel M z) {w : Step S | Step.next w = i} ∂ν := by
          refine lintegral_mono fun z => ?_
          rw [expKernel_next_eq]
          refine le_trans ?_ (stepLaw_next_eq_ge M i (Step.next z))
          exact mul_le_mul' le_rfl ((Finset.inf'_le _ (Finset.mem_univ (Step.next z))))
  -- the current state has the same law as the next state
  have hstate : ν {z : Step S | Step.state z = i} = ν {z : Step S | Step.next z = i} := by
    rw [hbind _ (measurableSet_state_eq i)]
    have : ∀ z : Step S, (expKernel M z) {w : Step S | Step.state w = i}
        = Set.indicator {z : Step S | Step.next z = i} (fun _ => (1 : ℝ≥0∞)) z := by
      intro z
      rw [expKernel_state_eq]
      by_cases h : Step.next z = i <;> simp [Set.indicator, h]
    rw [lintegral_congr this, lintegral_indicator (measurableSet_next_eq i)]
    simp
  have hpos' : ν {z : Step S | Step.state z = i} ≠ 0 := by
    rw [hstate]
    exact ne_of_gt (lt_of_lt_of_le hε0 hnext)
  have hfun : (fun z : Step S => if Step.state z = i then (1 : ℝ) else 0)
      = Set.indicator {z : Step S | Step.state z = i} (fun _ => (1 : ℝ)) := by
    funext z
    by_cases h : Step.state z = i <;> simp [Set.indicator, h]
  rw [hfun, integral_indicator_const (1 : ℝ) (measurableSet_state_eq i)]
  simp only [smul_eq_mul, mul_one, Measure.real]
  exact ENNReal.toReal_ne_zero.2 ⟨hpos', measure_ne_top _ _⟩

end TreatmentLocality

end

-- === tl_env.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

section Coef

variable (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
  (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)

/-- The transition coefficient carried by one observation. -/
noncomputable def dcoefB (z : Step S) : ℝ :=
  β (Step.state z) (M.act (Step.arm z) (Step.state z)) (Step.next z)

/-- The centred reward direction carried by one observation. -/
noncomputable def dcoefA (z : Step S) : ℝ :=
  α (Step.state z) (M.act (Step.arm z) (Step.state z))
    * (Step.rwd z - m (Step.state z) (M.act (Step.arm z) (Step.state z)))

/-- Half the reward-direction variance carried by one observation. -/
noncomputable def dcoefC (z : Step S) : ℝ :=
  (α (Step.state z) (M.act (Step.arm z) (Step.state z))) ^ 2
    * (v (Step.state z) (M.act (Step.arm z) (Step.state z)) : ℝ) / 2

lemma pertDens_eq (t : ℝ) (z : Step S) :
    pertDens M m v α β t z
      = (1 + t * dcoefB M β z)
        * rexp (t * dcoefA M m α z - t ^ 2 * dcoefC M v α z) := by
  simp only [pertDens, dcoefA, dcoefB, dcoefC]
  congr 2
  ring

/-- The `t`-derivative of the one-observation likelihood ratio. -/
noncomputable def pertDeriv (t : ℝ) (z : Step S) : ℝ :=
  dcoefB M β z * rexp (t * dcoefA M m α z - t ^ 2 * dcoefC M v α z)
    + (1 + t * dcoefB M β z) * rexp (t * dcoefA M m α z - t ^ 2 * dcoefC M v α z)
      * (dcoefA M m α z - 2 * t * dcoefC M v α z)

lemma hasDerivAt_pertDens (t : ℝ) (z : Step S) :
    HasDerivAt (fun u : ℝ => pertDens M m v α β u z) (pertDeriv M m v α β t z) t := by
  have hfun : (fun u : ℝ => pertDens M m v α β u z)
      = fun u : ℝ => (1 + u * dcoefB M β z)
        * rexp (u * dcoefA M m α z - u ^ 2 * dcoefC M v α z) := by
    funext u; exact pertDens_eq M m v α β u z
  rw [hfun, pertDeriv]
  exact Statistics.hasDerivAt_pertScalar _ _ _ t

@[simp] lemma pertDens_zero (z : Step S) : pertDens M m v α β 0 z = 1 := by
  rw [pertDens_eq]; simp

lemma pertDeriv_zero (z : Step S) :
    pertDeriv M m v α β 0 z = dcoefB M β z + dcoefA M m α z := by
  simp [pertDeriv]

end Coef

section Env

variable (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
  (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)

private lemma le_sum2 {f : S → Bool → ℝ} (hf : ∀ s a, 0 ≤ f s a) (s : S) (a : Bool) :
    f s a ≤ ∑ x : S, ∑ b : Bool, f x b := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun x : S => ∑ b : Bool, f x b)
    (fun x _ => Finset.sum_nonneg fun b _ => hf x b) (Finset.mem_univ s))
  exact Finset.single_le_sum (f := fun b : Bool => f s b) (fun b _ => hf s b)
    (Finset.mem_univ a)

private lemma le_sum3 {f : S → Bool → S → ℝ} (hf : ∀ s a j, 0 ≤ f s a j)
    (s : S) (a : Bool) (j : S) :
    f s a j ≤ ∑ x : S, ∑ b : Bool, ∑ y : S, f x b y := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun x : S => ∑ b : Bool, ∑ y : S, f x b y)
    (fun x _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun y _ => hf x b y)
    (Finset.mem_univ s))
  refine le_trans ?_ (Finset.single_le_sum (f := fun b : Bool => ∑ y : S, f s b y)
    (fun b _ => Finset.sum_nonneg fun y _ => hf s b y) (Finset.mem_univ a))
  exact Finset.single_le_sum (f := fun y : S => f s a y) (fun y _ => hf s a y)
    (Finset.mem_univ j)

/-- A uniform bound on the reward direction. -/
noncomputable def cA : ℝ := ∑ s : S, ∑ a : Bool, |α s a|
/-- A uniform bound on the transition direction. -/
noncomputable def cB : ℝ := ∑ s : S, ∑ a : Bool, ∑ j : S, |β s a j|
/-- A uniform bound on the mean rewards. -/
noncomputable def cM : ℝ := ∑ s : S, ∑ a : Bool, |m s a|
/-- A uniform bound on the reward variances. -/
noncomputable def cV : ℝ := ∑ s : S, ∑ a : Bool, (v s a : ℝ)

lemma cA_nonneg : 0 ≤ cA α :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
lemma cB_nonneg : 0 ≤ cB β :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
lemma cM_nonneg : 0 ≤ cM m :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
lemma cV_nonneg : 0 ≤ cV v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => (v _ _).coe_nonneg

lemma abs_alpha_le (s : S) (a : Bool) : |α s a| ≤ cA α :=
  le_sum2 (fun _ _ => abs_nonneg _) s a
lemma abs_beta_le (s : S) (a : Bool) (j : S) : |β s a j| ≤ cB β :=
  le_sum3 (fun _ _ _ => abs_nonneg _) s a j
lemma abs_mean_le (s : S) (a : Bool) : |m s a| ≤ cM m :=
  le_sum2 (fun _ _ => abs_nonneg _) s a
lemma var_le (s : S) (a : Bool) : (v s a : ℝ) ≤ cV v :=
  le_sum2 (fun x b => (v x b).coe_nonneg) s a

lemma abs_dcoefB_le (z : Step S) : |dcoefB M β z| ≤ cB β := abs_beta_le β _ _ _

lemma abs_dcoefA_le (z : Step S) :
    |dcoefA M m α z| ≤ cA α * (|Step.rwd z| + cM m) := by
  rw [dcoefA, abs_mul]
  refine mul_le_mul (abs_alpha_le α _ _) ?_ (abs_nonneg _) (cA_nonneg α)
  refine le_trans (abs_sub _ _) ?_
  have := abs_mean_le m (Step.state z) (M.act (Step.arm z) (Step.state z))
  linarith

lemma dcoefC_nonneg (z : Step S) : 0 ≤ dcoefC M v α z := by
  rw [dcoefC]; positivity

lemma two_dcoefC_le (z : Step S) : 2 * dcoefC M v α z ≤ (cA α) ^ 2 * cV v := by
  rw [dcoefC]
  have h1 : (α (Step.state z) (M.act (Step.arm z) (Step.state z))) ^ 2 ≤ (cA α) ^ 2 := by
    have hab := abs_alpha_le α (Step.state z) (M.act (Step.arm z) (Step.state z))
    nlinarith [sq_abs (α (Step.state z) (M.act (Step.arm z) (Step.state z))),
      abs_nonneg (α (Step.state z) (M.act (Step.arm z) (Step.state z)))]
  have h2 : ((v (Step.state z) (M.act (Step.arm z) (Step.state z)) : ℝ)) ≤ cV v :=
    var_le v _ _
  have h3 : (0:ℝ) ≤ (v (Step.state z) (M.act (Step.arm z) (Step.state z)) : ℝ) :=
    (v _ _).coe_nonneg
  nlinarith [sq_nonneg (cA α), cV_nonneg v]

/-- The exponential rate of the envelope. -/
noncomputable def envRate : ℝ := cA α + 1

/-- The constant of the envelope. -/
noncomputable def envConst : ℝ :=
  1 + 3 / 2 * rexp (cA α * cM m)
    + rexp (cA α * cM m)
      * (cB β + 3 / 2 * cA α + 3 / 2 * (cA α * cM m) + 3 / 2 * ((cA α) ^ 2 * cV v))

/-- The `L²` envelope dominating the likelihood ratio and its `t`-derivative. -/
noncomputable def envelope (z : Step S) : ℝ :=
  envConst m v α β * rexp (envRate α * |Step.rwd z|)

lemma envConst_ge_one : 1 ≤ envConst m v α β := by
  have h1 : (0:ℝ) ≤ 3 / 2 * rexp (cA α * cM m) := by positivity
  have h2 : (0:ℝ) ≤ cB β + 3 / 2 * cA α + 3 / 2 * (cA α * cM m) + 3 / 2 * ((cA α) ^ 2 * cV v) := by
    have := cA_nonneg α; have := cB_nonneg β; have := cM_nonneg m; have := cV_nonneg v
    positivity
  have h3 : (0:ℝ) ≤ rexp (cA α * cM m)
      * (cB β + 3 / 2 * cA α + 3 / 2 * (cA α * cM m) + 3 / 2 * ((cA α) ^ 2 * cV v)) :=
    mul_nonneg (Real.exp_pos _).le h2
  rw [envConst]; linarith

lemma one_le_envelope (z : Step S) : 1 ≤ envelope m v α β z := by
  have h1 := envConst_ge_one m v α β
  have h2 : (1:ℝ) ≤ rexp (envRate α * |Step.rwd z|) := by
    refine Real.one_le_exp ?_
    have := cA_nonneg α
    have : (0:ℝ) ≤ envRate α := by rw [envRate]; linarith
    positivity
  rw [envelope]
  nlinarith

/-- The radius within which the perturbation is dominated. -/
noncomputable def envEps : ℝ := min 1 (1 / (2 * (cB β + 1)))

lemma envEps_pos : 0 < envEps β := by
  have := cB_nonneg β
  rw [envEps]
  refine lt_min one_pos ?_
  positivity

lemma envEps_le_one : envEps β ≤ 1 := min_le_left _ _

lemma abs_t_mul_beta_le {t : ℝ} (ht : |t| < envEps β) (s : S) (a : Bool) (j : S) :
    |t * β s a j| ≤ 1 / 2 := by
  have hB := cB_nonneg β
  have h1 : |t| ≤ 1 / (2 * (cB β + 1)) := le_of_lt (lt_of_lt_of_le ht (min_le_right _ _))
  have h2 : |β s a j| ≤ cB β := abs_beta_le β s a j
  rw [abs_mul]
  have hpos : (0:ℝ) < 2 * (cB β + 1) := by linarith
  calc |t| * |β s a j| ≤ (1 / (2 * (cB β + 1))) * cB β :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        linarith

lemma one_add_t_beta_nonneg {t : ℝ} (ht : |t| < envEps β) (s : S) (a : Bool) (j : S) :
    0 ≤ 1 + t * β s a j := by
  have h := abs_le.1 (abs_t_mul_beta_le β ht s a j)
  linarith [h.1]

lemma abs_t_mul_dcoefB_le {t : ℝ} (ht : |t| < envEps β) (z : Step S) :
    |t * dcoefB M β z| ≤ 1 / 2 := by
  have hB := cB_nonneg β
  have h1 : |t| ≤ 1 / (2 * (cB β + 1)) := le_of_lt (lt_of_lt_of_le ht (min_le_right _ _))
  have h2 : |dcoefB M β z| ≤ cB β := abs_dcoefB_le M β z
  rw [abs_mul]
  have hpos : (0:ℝ) < 2 * (cB β + 1) := by linarith
  calc |t| * |dcoefB M β z| ≤ (1 / (2 * (cB β + 1))) * cB β :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        linarith

lemma pertDens_nonneg {t : ℝ} (ht : |t| < envEps β) (z : Step S) :
    0 ≤ pertDens M m v α β t z := by
  rw [pertDens_eq]
  have h := one_add_t_beta_nonneg β ht (Step.state z)
    (M.act (Step.arm z) (Step.state z)) (Step.next z)
  have h2 : (0:ℝ) < rexp (t * dcoefA M m α z - t ^ 2 * dcoefC M v α z) := Real.exp_pos _
  have h3 : 0 ≤ 1 + t * dcoefB M β z := by rw [dcoefB]; exact h
  positivity

lemma abs_t_le_one {t : ℝ} (ht : |t| < envEps β) : |t| ≤ 1 :=
  le_of_lt (lt_of_lt_of_le ht (envEps_le_one β))

private lemma exp_abs_dcoefA_le (z : Step S) :
    rexp |dcoefA M m α z| ≤ rexp (cA α * cM m) * rexp (cA α * |Step.rwd z|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 (le_trans (abs_dcoefA_le M m α z) ?_)
  nlinarith

private lemma envConst_ge_dens : 3 / 2 * rexp (cA α * cM m) ≤ envConst m v α β := by
  have h2 : (0:ℝ) ≤ cB β + 3 / 2 * cA α + 3 / 2 * (cA α * cM m)
      + 3 / 2 * ((cA α) ^ 2 * cV v) := by
    have := cA_nonneg α; have := cB_nonneg β; have := cM_nonneg m; have := cV_nonneg v
    positivity
  have h3 : (0:ℝ) ≤ rexp (cA α * cM m)
      * (cB β + 3 / 2 * cA α + 3 / 2 * (cA α * cM m) + 3 / 2 * ((cA α) ^ 2 * cV v)) :=
    mul_nonneg (Real.exp_pos _).le h2
  rw [envConst]; linarith

lemma abs_pertDens_le_envelope {t : ℝ} (ht : |t| < envEps β) (z : Step S) :
    |pertDens M m v α β t z| ≤ envelope m v α β z := by
  have hb := abs_t_mul_dcoefB_le M β ht z
  have ht1 := abs_t_le_one β ht
  have hC := dcoefC_nonneg M v α z
  have hs := Statistics.abs_pertScalar_le (dcoefB M β z) (dcoefA M m α z)
    (dcoefC M v α z) t hC hb ht1
  rw [pertDens_eq]
  refine le_trans hs ?_
  have hexp := exp_abs_dcoefA_le M m α z
  have hcst := envConst_ge_dens m v α β
  have hslack : rexp (cA α * |Step.rwd z|) ≤ rexp (envRate α * |Step.rwd z|) := by
    refine Real.exp_le_exp.2 ?_
    have hr : (0:ℝ) ≤ |Step.rwd z| := abs_nonneg _
    rw [envRate]; nlinarith
  rw [envelope]
  calc 3 / 2 * rexp |dcoefA M m α z|
      ≤ 3 / 2 * (rexp (cA α * cM m) * rexp (cA α * |Step.rwd z|)) := by linarith
    _ ≤ 3 / 2 * (rexp (cA α * cM m) * rexp (envRate α * |Step.rwd z|)) := by
        have := Real.exp_pos (cA α * cM m); nlinarith
    _ = (3 / 2 * rexp (cA α * cM m)) * rexp (envRate α * |Step.rwd z|) := by ring
    _ ≤ envConst m v α β * rexp (envRate α * |Step.rwd z|) :=
        mul_le_mul_of_nonneg_right hcst (Real.exp_pos _).le

lemma abs_pertDeriv_le_envelope {t : ℝ} (ht : |t| < envEps β) (z : Step S) :
    |pertDeriv M m v α β t z| ≤ envelope m v α β z := by
  have hb := abs_t_mul_dcoefB_le M β ht z
  have ht1 := abs_t_le_one β ht
  have hC := dcoefC_nonneg M v α z
  have hs := Statistics.abs_pertScalarDeriv_le (dcoefB M β z) (dcoefA M m α z)
    (dcoefC M v α z) t hC hb ht1
  rw [pertDeriv]
  refine le_trans hs ?_
  have hA := cA_nonneg α
  have hB := cB_nonneg β
  have hM := cM_nonneg m
  have hV := cV_nonneg v
  have hr : (0:ℝ) ≤ |Step.rwd z| := abs_nonneg _
  set K : ℝ := cB β + 3 / 2 * cA α + 3 / 2 * (cA α * cM m) + 3 / 2 * ((cA α) ^ 2 * cV v) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hfac : |dcoefB M β z| + 3 / 2 * (|dcoefA M m α z| + 2 * dcoefC M v α z)
      ≤ K * (1 + |Step.rwd z|) := by
    have h1 := abs_dcoefB_le M β z
    have h2 := abs_dcoefA_le M m α z
    have h3 := two_dcoefC_le M v α z
    have h4 : 3 / 2 * cA α * |Step.rwd z| ≤ K * |Step.rwd z| := by
      refine mul_le_mul_of_nonneg_right ?_ hr
      rw [hK]; nlinarith
    rw [hK] at h4 ⊢
    nlinarith
  have hexp := exp_abs_dcoefA_le M m α z
  have hone : 1 + |Step.rwd z| ≤ rexp |Step.rwd z| := by
    have := Real.add_one_le_exp (|Step.rwd z|)
    linarith
  have hcst : K * rexp (cA α * cM m) ≤ envConst m v α β := by
    have h3 : (0:ℝ) ≤ 3 / 2 * rexp (cA α * cM m) := by positivity
    rw [envConst, hK]; nlinarith [Real.exp_pos (cA α * cM m)]
  have hposE : (0:ℝ) < rexp |dcoefA M m α z| := Real.exp_pos _
  have hcomb : rexp |Step.rwd z| * rexp (cA α * |Step.rwd z|)
      = rexp (envRate α * |Step.rwd z|) := by
    rw [← Real.exp_add, envRate]; congr 1; ring
  rw [envelope]
  calc (|dcoefB M β z| + 3 / 2 * (|dcoefA M m α z| + 2 * dcoefC M v α z))
        * rexp |dcoefA M m α z|
      ≤ (K * (1 + |Step.rwd z|)) * rexp |dcoefA M m α z| :=
        mul_le_mul_of_nonneg_right hfac hposE.le
    _ ≤ (K * rexp |Step.rwd z|)
        * (rexp (cA α * cM m) * rexp (cA α * |Step.rwd z|)) := by
        have hl : K * (1 + |Step.rwd z|) ≤ K * rexp |Step.rwd z| :=
          mul_le_mul_of_nonneg_left hone hK0
        exact mul_le_mul hl hexp hposE.le (by positivity)
    _ = (K * rexp (cA α * cM m)) * (rexp |Step.rwd z| * rexp (cA α * |Step.rwd z|)) := by
        ring
    _ = (K * rexp (cA α * cM m)) * rexp (envRate α * |Step.rwd z|) := by rw [hcomb]
    _ ≤ envConst m v α β * rexp (envRate α * |Step.rwd z|) :=
        mul_le_mul_of_nonneg_right hcst (Real.exp_pos _).le

lemma measurable_envelope : Measurable (fun z : Step S => envelope m v α β z) := by
  simp only [envelope, Step.rwd]
  fun_prop

/-- The envelope is square-integrable under any invariant law of the experiment chain with
Gaussian rewards. -/
theorem memLp_envelope (M : Model S) (hgauss : M.GaussianRewards m v)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) :
    MemLp (fun z : Step S => envelope m v α β z) 2 ν := by
  have hmeas : Measurable (fun z : Step S => envelope m v α β z) := measurable_envelope m v α β
  have hF : Measurable (fun r : ℝ => ENNReal.ofReal (rexp (2 * envRate α * |r|))) := by fun_prop
  have hfin : ∀ x : S, ∀ a : Bool,
      ∫⁻ r, ENNReal.ofReal (rexp (2 * envRate α * |r|)) ∂(M.reward x a) < ⊤ := by
    intro x a
    rw [hgauss x a]
    exact Statistics.lintegral_exp_abs_gaussian_lt_top (2 * envRate α) (m x a) (v x a)
  have hint : Integrable (fun z : Step S => rexp (2 * envRate α * |Step.rwd z|)) ν := by
    have hmr : Measurable (fun z : Step S => rexp (2 * envRate α * |Step.rwd z|)) := by
      simp only [Step.rwd]; fun_prop
    refine ⟨hmr.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)]
    refine lt_of_le_of_lt (lintegral_rwd_le_of_invariant M ν hinv hF) ?_
    exact ENNReal.sum_lt_top.2 fun x _ => ENNReal.sum_lt_top.2 fun a _ => hfin x a
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 ?_
  refine (hint.const_mul ((envConst m v α β) ^ 2)).congr ?_
  filter_upwards with z
  rw [envelope, mul_pow, ← Real.exp_nat_mul]
  ring_nf

end Env

end TreatmentLocality

end

-- === tl_fisher.lean ===
section



open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The Bochner integral against a measure pushed through a Markov kernel between
different spaces. -/
lemma integral_bind_kernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    {f : β → ℝ} (hf : Integrable f (μ.bind κ)) :
    ∫ y, f y ∂(μ.bind κ) = ∫ x, (∫ y, f y ∂(κ x)) ∂μ := by
  have h1 : μ.bind κ = (κ ∘ₖ (Kernel.const Unit μ)) () := rfl
  rw [h1] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-- **The one-observation law, integrated.**  Integrating against the observation law of a
model started from `μ` averages the step law over the initial state. -/
theorem integral_obsLaw (M : Model S) (μ : Measure S) [IsProbabilityMeasure μ]
    {f : Step S → ℝ} (hf : Measurable f) (hint : Integrable f (obsLaw M μ)) :
    ∫ z, f z ∂(obsLaw M μ) = ∑ x : S, μ.real {x} * ∫ q, f (x, q) ∂(stepLaw M x) := by
  have hker : ∀ x : S, ∫ z, f z ∂(obsKernel M x) = ∫ q, f (x, q) ∂(stepLaw M x) := by
    intro x
    rw [obsKernel_apply, Measure.dirac_prod,
      integral_map (measurable_prodMk_left).aemeasurable hf.aestronglyMeasurable]
  rw [obsLaw, integral_bind_kernel μ (obsKernel M) hint]
  have hg : Integrable (fun x : S => ∫ z, f z ∂(obsKernel M x)) μ := .of_finite
  rw [integral_fintype hg]
  exact Finset.sum_congr rfl fun x _ => by rw [smul_eq_mul, hker x]

/-- **The population transition statistic of the information-sharing scheme** under the
one-observation law of a model started from `μ`. -/
theorem meanObs_obsLaw_trans (M : Model S) (μ : Measure S) [IsProbabilityMeasure μ]
    (a : Bool) (i j : S) :
    (meanObs M .IS (obsLaw M μ) a).1 i j = μ.real {i} * M.polTrans a i j := by
  classical
  set f : Step S → ℝ := fun z => (estObs M .IS z a).1 i j with hf
  have hfEq : ∀ z : Step S, f z
      = (if Step.state z = i then (1 : ℝ) else 0)
        * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
          * (if Step.next z = j then (1 : ℝ) else 0)) := by
    intro z
    rw [hf]
    simp only [estObs, schemeWeight]
    by_cases h : Step.state z = i
    · by_cases h2 : Step.next z = j <;> simp [h, h2]
    · simp [h]
  have hmeasR : Measurable (fun z : Step S =>
      (if Step.state z = i then (1 : ℝ) else 0)
        * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
          * (if Step.next z = j then (1 : ℝ) else 0))) := by
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact Measurable.ite (measurable_fst (measurableSet_singleton i))
        measurable_const measurable_const
    · exact Measurable.ite (measurable_fst (measurableSet_singleton M.crucial))
        (((Measurable.ite ((measurable_fst.comp measurable_snd)
          (measurableSet_singleton a)) measurable_const measurable_const)).const_mul 2)
        measurable_const
    · exact Measurable.ite (((measurable_fst.comp measurable_snd).comp measurable_snd)
        (measurableSet_singleton j)) measurable_const measurable_const
  have hmeas : Measurable f := by
    have hfe : f = (fun z : Step S =>
        (if Step.state z = i then (1 : ℝ) else 0)
          * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
            * (if Step.next z = j then (1 : ℝ) else 0))) := funext hfEq
    rw [hfe]; exact hmeasR
  have hbd : ∀ z : Step S, |f z| ≤ 2 := by
    intro z
    rw [hfEq z]
    simp only [abs_mul]
    have h0 : |if Step.state z = i then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    have h1 : |if Step.state z = M.crucial then
        2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1| ≤ 2 := by
      split_ifs <;> norm_num
    have h2 : |if Step.next z = j then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    calc |if Step.state z = i then (1 : ℝ) else 0|
          * (|if Step.state z = M.crucial then
              2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1|
            * |if Step.next z = j then (1 : ℝ) else 0|)
        ≤ 1 * (2 * 1) :=
          mul_le_mul h0 (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num))
            (by positivity) (by norm_num)
      _ = 2 := by norm_num
  have hint : Integrable f (obsLaw M μ) := by
    refine (integrable_const (2 : ℝ)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using hbd z
  rw [meanObs]
  show ∫ z, f z ∂(obsLaw M μ) = μ.real {i} * M.polTrans a i j
  rw [integral_obsLaw M μ hmeas hint]
  refine Finset.sum_eq_single i (fun x _ hx => ?_) (fun h => absurd (Finset.mem_univ i) h) |>.trans ?_
  · have : ∀ q : Bool × S × ℝ, f (x, q) = 0 := by
      intro q
      rw [hfEq (x, q)]
      simp [Step.state, hx]
    simp [this]
  · congr 1
    have hq : ∀ q : Bool × S × ℝ, f (i, q)
        = (if i = M.crucial then 2 * (if q.1 = a then (1 : ℝ) else 0) else 1)
          * (if q.2.1 = j then (1 : ℝ) else 0) := by
      intro q
      rw [hfEq (i, q)]
      simp only [Step.state, Step.arm, Step.next, ite_true, one_mul]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall hq)]
    exact integral_stepLaw_indicator M i j a

/-- The reward moment under a one-observation law is controlled by the reward laws. -/
lemma lintegral_obsLaw_rwd_le (M : Model S) (μ : Measure S) [IsProbabilityMeasure μ]
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (Step.rwd z) ∂(obsLaw M μ) ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun z : Step S => F (Step.rwd z)) := hF.comp measurable_rwd
  rw [obsLaw, Measure.lintegral_bind (Kernel.aemeasurable _) hFm.aemeasurable]
  calc ∫⁻ x, (∫⁻ z, F (Step.rwd z) ∂(obsKernel M x)) ∂μ
      ≤ ∫⁻ _x : S, (∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [obsKernel_apply, Measure.dirac_prod, lintegral_map hFm measurable_prodMk_left]
        exact lintegral_stepLaw_rwd_le M hF x
    _ = ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
        rw [lintegral_const, measure_univ, mul_one]

/-- The reward is integrable under a one-observation law of a model with integrable
rewards. -/
lemma integrable_rwd_obsLaw (M : Model S) (μ : Measure S) [IsProbabilityMeasure μ]
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) :
    Integrable (fun z : Step S => Step.rwd z) (obsLaw M μ) := by
  refine ⟨measurable_rwd.aestronglyMeasurable, ?_⟩
  have hF : Measurable (fun r : ℝ => ENNReal.ofReal |r|) := by fun_prop
  have hfin : ∀ x : S, ∀ a : Bool, ∫⁻ r, ENNReal.ofReal |r| ∂(M.reward x a) < ⊤ := by
    intro x a
    have h := (hR x a).hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    refine lt_of_le_of_lt (le_of_eq ?_) h
    refine lintegral_congr fun r => ?_
    rw [Real.enorm_eq_ofReal_abs]
  rw [hasFiniteIntegral_iff_enorm]
  have hEq : ∫⁻ z : Step S, ‖Step.rwd z‖ₑ ∂(obsLaw M μ)
      = ∫⁻ z : Step S, ENNReal.ofReal |Step.rwd z| ∂(obsLaw M μ) := by
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal_abs]
  rw [hEq]
  refine lt_of_le_of_lt (lintegral_obsLaw_rwd_le M μ hF) ?_
  exact ENNReal.sum_lt_top.2 fun x _ => ENNReal.sum_lt_top.2 fun a _ => hfin x a

/-- **The population reward statistic of the information-sharing scheme** under the
one-observation law of a model started from `μ`. -/
theorem meanObs_obsLaw_rwd (M : Model S) (μ : Measure S) [IsProbabilityMeasure μ]
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) (a : Bool) (i : S) :
    (meanObs M .IS (obsLaw M μ) a).2 i = μ.real {i} * M.polReward a i := by
  classical
  set f : Step S → ℝ := fun z => (estObs M .IS z a).2 i with hf
  have hfEq : ∀ z : Step S, f z
      = (if Step.state z = i then (1 : ℝ) else 0)
        * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
          * Step.rwd z) := by
    intro z
    rw [hf]
    simp only [estObs, schemeWeight]
    by_cases h : Step.state z = i <;> simp [h] <;> ring
  have hmeasR : Measurable (fun z : Step S =>
      (if Step.state z = i then (1 : ℝ) else 0)
        * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
          * Step.rwd z)) := by
    refine Measurable.mul ?_ (Measurable.mul ?_ measurable_rwd)
    · exact Measurable.ite (measurable_fst (measurableSet_singleton i))
        measurable_const measurable_const
    · exact Measurable.ite (measurable_fst (measurableSet_singleton M.crucial))
        (((Measurable.ite ((measurable_fst.comp measurable_snd)
          (measurableSet_singleton a)) measurable_const measurable_const)).const_mul 2)
        measurable_const
  have hmeas : Measurable f := by
    have hfe : f = (fun z : Step S =>
        (if Step.state z = i then (1 : ℝ) else 0)
          * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
            * Step.rwd z)) := funext hfEq
    rw [hfe]; exact hmeasR
  have hbd : ∀ z : Step S, |f z| ≤ 2 * |Step.rwd z| := by
    intro z
    rw [hfEq z]
    simp only [abs_mul]
    have h0 : |if Step.state z = i then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    have h1 : |if Step.state z = M.crucial then
        2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1| ≤ 2 := by
      split_ifs <;> norm_num
    have hr : (0:ℝ) ≤ |Step.rwd z| := abs_nonneg _
    calc |if Step.state z = i then (1 : ℝ) else 0|
          * (|if Step.state z = M.crucial then
              2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1| * |Step.rwd z|)
        ≤ 1 * (2 * |Step.rwd z|) :=
          mul_le_mul h0 (mul_le_mul_of_nonneg_right h1 hr) (by positivity) (by norm_num)
      _ = 2 * |Step.rwd z| := by ring
  have hint : Integrable f (obsLaw M μ) := by
    refine ((integrable_rwd_obsLaw M μ hR).abs.const_mul (2:ℝ)).mono'
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using hbd z
  rw [meanObs]
  show ∫ z, f z ∂(obsLaw M μ) = μ.real {i} * M.polReward a i
  rw [integral_obsLaw M μ hmeas hint]
  refine Finset.sum_eq_single i (fun x _ hx => ?_) (fun h => absurd (Finset.mem_univ i) h)
    |>.trans ?_
  · have : ∀ q : Bool × S × ℝ, f (x, q) = 0 := by
      intro q
      rw [hfEq (x, q)]
      simp [Step.state, hx]
    simp [this]
  · congr 1
    have hq : ∀ q : Bool × S × ℝ, f (i, q)
        = (if i = M.crucial then 2 * (if q.1 = a then (1 : ℝ) else 0) else 1) * q.2.2 := by
      intro q
      rw [hfEq (i, q)]
      simp only [Step.state, Step.arm, Step.rwd, ite_true, one_mul]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall hq)]
    exact integral_stepLaw_rwd M i a hR

/-- The information-sharing statistics depend on the model only through the crucial
state. -/
lemma meanObs_congr_crucial (M M' : Model S) (hc : M'.crucial = M.crucial)
    (ν : Measure (Step S)) : meanObs M .IS ν = meanObs M' .IS ν := by
  have hw : ∀ (a : Bool) (z : Step S), schemeWeight M .IS a z = schemeWeight M' .IS a z := by
    intro a z; rw [schemeWeight, schemeWeight, hc]
  have he : ∀ (z : Step S), estObs M .IS z = estObs M' .IS z := by
    intro z; funext a; rw [estObs, estObs, hw a z]
  funext a
  rw [meanObs, meanObs]
  simp only [he]

/-- **Fisher consistency at any one-observation law.**  The plug-in estimator evaluated at
the population statistics of the observation law of a model `M'` started from a
fully-supported initial distribution returns the true average treatment effect of `M'` —
no stationarity is needed. -/
theorem mbATE_meanObs_obsLaw (M M' : Model S) (hc : M'.crucial = M.crucial)
    (hγ : M'.γdisc = M.γdisc) (μ : Measure S) [IsProbabilityMeasure μ]
    (hμ : ∀ i, μ.real {i} ≠ 0)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M'.reward x y)) :
    mbATE M (meanObs M .IS (obsLaw M' μ)) = M'.ate := by
  have hmean := meanObs_congr_crucial M M' hc (obsLaw M' μ)
  have hvisit : ∀ (a : Bool) (i : S),
      ∑ k, (meanObs M .IS (obsLaw M' μ) a).1 i k = μ.real {i} := by
    intro a i
    have h : ∀ k : S, (meanObs M .IS (obsLaw M' μ) a).1 i k = μ.real {i} * M'.polTrans a i k := by
      intro k; rw [hmean]; exact meanObs_obsLaw_trans M' μ a i k
    have hsum : ∑ k, M'.polTrans a i k = 1 := pmf_sum_toReal (M'.trans i (M'.act a i))
    rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.mul_sum, hsum, mul_one]
  have htrans : ∀ a : Bool, mbTrans (meanObs M .IS (obsLaw M' μ)) a = M'.polTrans a := by
    intro a
    ext i j
    rw [mbTrans, Matrix.of_apply, hvisit a i, hmean, meanObs_obsLaw_trans M' μ a i j]
    exact mul_div_cancel_left₀ _ (hμ i)
  have hrwd : ∀ a : Bool, mbReward (meanObs M .IS (obsLaw M' μ)) a = M'.polReward a := by
    intro a
    funext i
    rw [mbReward, hvisit a i, hmean, meanObs_obsLaw_rwd M' μ hR a i]
    exact mul_div_cancel_left₀ _ (hμ i)
  have hval : ∀ a : Bool, mbValue M (meanObs M .IS (obsLaw M' μ)) a = M'.value a := by
    intro a
    rw [mbValue, htrans a, hrwd a, Model.value, hγ]
  rw [mbATE_eq_mbValue, hval true, hval false]
  rfl

end TreatmentLocality

end

-- === tl_score1.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- Every exponential moment of the reward is finite under an invariant law with Gaussian
rewards. -/
theorem integrable_exp_abs_rwd (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (k : ℝ) :
    Integrable (fun z : Step S => rexp (k * |Step.rwd z|)) ν := by
  have hmr : Measurable (fun z : Step S => rexp (k * |Step.rwd z|)) := by
    simp only [Step.rwd]; fun_prop
  have hF : Measurable (fun r : ℝ => ENNReal.ofReal (rexp (k * |r|))) := by fun_prop
  refine ⟨hmr.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)]
  refine lt_of_le_of_lt (lintegral_rwd_le_of_invariant M ν hinv hF) ?_
  refine ENNReal.sum_lt_top.2 fun x _ => ENNReal.sum_lt_top.2 fun a _ => ?_
  rw [hgauss x a]
  exact Statistics.lintegral_exp_abs_gaussian_lt_top k (m x a) (v x a)

/-- The linear-times-envelope bound is integrable. -/
theorem integrable_lin_envelope (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (K : ℝ) (hK0 : 0 ≤ K) :
    Integrable (fun z : Step S => K * (1 + |Step.rwd z|) * envelope m v α β z) ν := by
  have hexp2 := integrable_exp_abs_rwd M m v hgauss ν hinv (envRate α + 1)
  refine ((hexp2.const_mul (K * envConst m v α β))).mono' ?_
    (Filter.Eventually.of_forall fun z => ?_)
  · have hm : Measurable (fun z : Step S => K * (1 + |Step.rwd z|) * envelope m v α β z) := by
      simp only [envelope, Step.rwd]; fun_prop
    exact hm.aestronglyMeasurable
  · have hEnv : (0:ℝ) ≤ envelope m v α β z :=
      le_trans zero_le_one (one_le_envelope m v α β z)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : 1 + |Step.rwd z| ≤ rexp |Step.rwd z| := by
      linarith [Real.add_one_le_exp (|Step.rwd z|)]
    have h2 : rexp |Step.rwd z| * rexp (envRate α * |Step.rwd z|)
        = rexp ((envRate α + 1) * |Step.rwd z|) := by
      rw [← Real.exp_add]; congr 1; ring
    calc K * (1 + |Step.rwd z|) * envelope m v α β z
        = K * (1 + |Step.rwd z|) * (envConst m v α β * rexp (envRate α * |Step.rwd z|)) := rfl
      _ ≤ K * rexp |Step.rwd z| * (envConst m v α β * rexp (envRate α * |Step.rwd z|)) := by
          have hC : (0:ℝ) ≤ envConst m v α β :=
            le_trans zero_le_one (envConst_ge_one m v α β)
          have hE : (0:ℝ) < rexp (envRate α * |Step.rwd z|) := Real.exp_pos _
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK0) ?_
          positivity
      _ = K * envConst m v α β * (rexp |Step.rwd z| * rexp (envRate α * |Step.rwd z|)) := by ring
      _ = K * envConst m v α β * rexp ((envRate α + 1) * |Step.rwd z|) := by rw [h2]

/-- Any linearly-bounded observable times the score is integrable. -/
theorem integrable_mul_pertDeriv (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (c : Step S → ℝ) (hc : Measurable c) (K : ℝ) (hK0 : 0 ≤ K)
    (hcbd : ∀ z, |c z| ≤ K * (1 + |Step.rwd z|)) :
    Integrable (fun z : Step S => c z * pertDeriv M m v α β 0 z) ν := by
  have hmd' : Measurable (fun z : Step S => pertDeriv M m v α β 0 z) := by
    simp only [pertDeriv, dcoefA, dcoefB, dcoefC, Step.state, Step.arm, Step.next, Step.rwd]
    fun_prop
  refine (integrable_lin_envelope M m v hgauss α β ν hinv K hK0).mono'
    (hc.mul hmd').aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have hz : |(0:ℝ)| < envEps β := by simpa using envEps_pos β
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hcbd z) (abs_pertDeriv_le_envelope M m v α β hz z) (abs_nonneg _)
    (by positivity)

/-- **Differentiating a single observation statistic along the perturbation.** -/
theorem hasDerivAt_integral_pertDens (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (c : Step S → ℝ) (hc : Measurable c) (K : ℝ) (hK0 : 0 ≤ K)
    (hcbd : ∀ z, |c z| ≤ K * (1 + |Step.rwd z|)) :
    HasDerivAt (fun t => ∫ z, c z * pertDens M m v α β t z ∂ν)
      (∫ z, c z * pertDeriv M m v α β 0 z ∂ν) 0 := by
  classical
  have hεpos : 0 < envEps β := envEps_pos β
  have hmd : ∀ t : ℝ, Measurable (fun z : Step S => pertDens M m v α β t z) := by
    intro t
    simp only [pertDens, Step.state, Step.arm, Step.next, Step.rwd]
    fun_prop
  have hmd' : ∀ t : ℝ, Measurable (fun z : Step S => pertDeriv M m v α β t z) := by
    intro t
    simp only [pertDeriv, dcoefA, dcoefB, dcoefC, Step.state, Step.arm, Step.next, Step.rwd]
    fun_prop
  have hexp1 := integrable_exp_abs_rwd M m v hgauss ν hinv 1
  have hlin : Integrable (fun z : Step S => K * (1 + |Step.rwd z|)) ν := by
    refine (hexp1.const_mul K).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have : Measurable (fun z : Step S => K * (1 + |Step.rwd z|)) := by
        simp only [Step.rwd]; fun_prop
      exact this.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : 1 + |Step.rwd z| ≤ rexp (1 * |Step.rwd z|) := by
        rw [one_mul]; linarith [Real.add_one_le_exp (|Step.rwd z|)]
      nlinarith [Real.exp_pos (1 * |Step.rwd z|)]
  have hbint := integrable_lin_envelope M m v hgauss α β ν hinv K hK0
  have hcint : Integrable c ν := by
    refine hlin.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact hcbd z
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun t z => c z * pertDens M m v α β t z)
    (F' := fun t z => c z * pertDeriv M m v α β t z)
    (x₀ := (0:ℝ)) (bound := fun z => K * (1 + |Step.rwd z|) * envelope m v α β z)
    (s := Metric.ball (0:ℝ) (envEps β)) (Metric.ball_mem_nhds 0 hεpos)
    (Filter.Eventually.of_forall fun t => (hc.mul (hmd t)).aestronglyMeasurable)
    (by
      show Integrable (fun z => c z * pertDens M m v α β 0 z) ν
      have hz : (fun z => c z * pertDens M m v α β 0 z) = c := by
        funext z; rw [pertDens_zero]; ring
      rw [hz]; exact hcint)
    (hc.mul (hmd' 0)).aestronglyMeasurable
    ?hbnd hbint ?hdiff
  · exact hkey.2
  case hbnd =>
    filter_upwards with z
    intro t ht
    have habs : |t| < envEps β := by simpa [Real.dist_eq] using ht
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hcbd z) (abs_pertDeriv_le_envelope M m v α β habs z)
      (abs_nonneg _) (by positivity)
  case hdiff =>
    filter_upwards with z
    intro t _
    exact (hasDerivAt_pertDens M m v α β t z).const_mul (c z)

end TreatmentLocality

end

-- === tl_grad.lean ===
section

open scoped NNReal ENNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The plug-in system matrix factors as `Diag(N^a) · (I - γ P̂^a)`. -/
lemma mbSystem_eq_diagonal_mul (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) :
    mbSystem M v a
      = (Matrix.diagonal fun i => ∑ k, (v a).1 i k)
          * ((1 : Matrix S S ℝ) - M.γdisc • mbTrans v a) := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Matrix.diagonal_apply_eq]
  have hentry : ((1 : Matrix S S ℝ) - M.γdisc • mbTrans v a) i j
      = (if i = j then (1 : ℝ) else 0) - M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k) := by
    simp [Matrix.sub_apply, Matrix.one_apply, mbTrans, smul_eq_mul]
  have hNi : (∑ k, (v a).1 i k) ≠ 0 := hN i
  have hc : (v a).1 i j / (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k) = (v a).1 i j := by
    field_simp
  have h2 : (∑ k, (v a).1 i k) * (M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k))
      = M.γdisc * (v a).1 i j := by
    calc (∑ k, (v a).1 i k) * (M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k))
        = M.γdisc * ((v a).1 i j / (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k)) := by ring
      _ = M.γdisc * (v a).1 i j := by rw [hc]
  rw [mbSystem_apply, hentry, mul_sub, h2]
  congr 1
  split_ifs <;> ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- With positive visit counts the plug-in value function solves the plug-in Bellman
system: `V̂^a = (Diag(N^a) - γ K^a)⁻¹ R^a`. -/
lemma mbValue_eq_mbSystem_inv_mulVec (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) :
    mbValue M v a = (mbSystem M v a)⁻¹.mulVec (fun i => (v a).2 i) := by
  have hDinv : (Matrix.diagonal fun i => ∑ k, (v a).1 i k)⁻¹
      = Matrix.diagonal (fun i => (∑ k, (v a).1 i k)⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k)⁻¹) = (fun _ : S => (1 : ℝ)) from
      funext fun i => mul_inv_cancel₀ (hN i)]
    exact Matrix.diagonal_one
  simp only [mbValue]
  rw [mbSystem_eq_diagonal_mul M v a hN, Matrix.mul_inv_rev, hDinv, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal]
  simp [mbReward, div_eq_inv_mul]

/-- Applying the plug-in system matrix to a vector. -/
lemma mbSystem_mulVec_apply (M : Model S) (u : EstInput S) (a : Bool) (x : S → ℝ) (i : S) :
    (mbSystem M u a).mulVec x i = ∑ j, (u a).1 i j * (x i - M.γdisc * x j) := by
  simp only [Matrix.mulVec, dotProduct, mbSystem_apply, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  · have hstep : ∀ j : S, (if i = j then (∑ k, (u a).1 i k) else 0) * x j
        = (if i = j then (∑ k, (u a).1 i k) * x i else 0) := by
      intro j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_eq]
    simp [Finset.sum_mul]
  · exact Finset.sum_congr rfl fun j _ => by ring

/-- The plug-in system matrix as a continuous linear map of the statistics. -/
noncomputable def mbSystemL (M : Model S) (a : Bool) : EstInput S →L[ℝ] Matrix S S ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => mbSystem M u a
      map_add' := by
        intro u₁ u₂
        ext i j
        simp only [mbSystem_apply, Matrix.add_apply, Pi.add_apply, Prod.fst_add,
          Finset.sum_add_distrib]
        split_ifs <;> ring
      map_smul' := by
        intro r u
        ext i j
        simp only [mbSystem_apply, Matrix.smul_apply, Pi.smul_apply, Prod.smul_fst,
          smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
        split_ifs <;> ring }

lemma mbSystemL_apply (M : Model S) (a : Bool) (u : EstInput S) :
    mbSystemL M a u = mbSystem M u a := rfl

/-- The visit count as a continuous linear functional. -/
noncomputable def visitL (a : Bool) (i : S) : EstInput S →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => ∑ k, (u a).1 i k
      map_add' := by intro u₁ u₂; simp [Finset.sum_add_distrib]
      map_smul' := by intro r u; simp [Finset.mul_sum] }

lemma visitL_apply (a : Bool) (i : S) (u : EstInput S) : visitL a i u = ∑ k, (u a).1 i k := rfl

/-- The reward statistic as a continuous linear functional. -/
noncomputable def rewardL (a : Bool) (i : S) : EstInput S →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => (u a).2 i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

lemma rewardL_apply (a : Bool) (i : S) (u : EstInput S) : rewardL a i u = (u a).2 i := rfl

/-- Reading off a matrix entry, as a continuous linear functional. -/
noncomputable def entryL (i j : S) : Matrix S S ℝ →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

lemma entryL_apply (i j : S) (A : Matrix S S ℝ) : entryL i j A = A i j := rfl

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The derivative of the inverse plug-in system matrix, as a continuous linear map. -/
noncomputable def invDL (M : Model S) (v : EstInput S) (a : Bool) :
    EstInput S →L[ℝ] Matrix S S ℝ :=
  (-ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ)
    (Ring.inverse (mbSystem M v a)) (Ring.inverse (mbSystem M v a))).comp (mbSystemL M a)

lemma invDL_apply (M : Model S) (v : EstInput S) (a : Bool) (h : EstInput S) :
    invDL M v a h = -(Ring.inverse (mbSystem M v a) * mbSystem M h a
      * Ring.inverse (mbSystem M v a)) := by
  show (-ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ)
    (Ring.inverse (mbSystem M v a)) (Ring.inverse (mbSystem M v a))) (mbSystemL M a h) = _
  rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, mbSystemL_apply]

/-- One summand of the gradient of the plug-in value function. -/
noncomputable def gradPiece (M : Model S) (v : EstInput S) (a : Bool) (s i : S) :
    EstInput S →L[ℝ] ℝ :=
  (Ring.inverse (mbSystem M v a) s i) • (rewardL a i)
    + ((v a).2 i) • ((entryL s i).comp (invDL M v a))

lemma gradPiece_apply (M : Model S) (v : EstInput S) (a : Bool) (s i : S) (h : EstInput S) :
    gradPiece M v a s i h
      = Ring.inverse (mbSystem M v a) s i * (h a).2 i
        - (v a).2 i * ((Ring.inverse (mbSystem M v a) * mbSystem M h a
            * Ring.inverse (mbSystem M v a)) s i) := by
  show (Ring.inverse (mbSystem M v a) s i) • (rewardL a i h)
    + ((v a).2 i) • ((entryL s i) (invDL M v a h)) = _
  rw [rewardL_apply, invDL_apply, entryL_apply, Matrix.neg_apply]
  simp only [smul_eq_mul]
  ring

/-- The plug-in value function is Fréchet differentiable in the statistics, with the
derivative obtained by differentiating the plug-in Bellman system. -/
theorem hasFDerivAt_mbValue (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) (hB : IsUnit (mbSystem M v a)) (s : S) :
    HasFDerivAt (fun u : EstInput S => mbValue M u a s)
      (∑ i : S, gradPiece M v a s i) v := by
  have hsys : HasFDerivAt (fun u : EstInput S => mbSystem M u a) (mbSystemL M a) v :=
    (mbSystemL M a).hasFDerivAt
  have hDinvM : HasFDerivAt (fun u : EstInput S => Ring.inverse (mbSystem M u a))
      (invDL M v a) v := by
    have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) hB.unit
    rw [hB.unit_spec] at h1
    have h2 : ((hB.unit⁻¹ : (Matrix S S ℝ)ˣ) : Matrix S S ℝ)
        = Ring.inverse (mbSystem M v a) := by
      rw [← Ring.inverse_unit hB.unit, hB.unit_spec]
    rw [h2] at h1
    exact h1.comp v hsys
  have hEach : ∀ i : S, HasFDerivAt
      (fun u : EstInput S => Ring.inverse (mbSystem M u a) s i * (u a).2 i)
      (gradPiece M v a s i) v := by
    intro i
    have hc : HasFDerivAt (fun u : EstInput S => Ring.inverse (mbSystem M u a) s i)
        ((entryL s i).comp (invDL M v a)) v := (entryL s i).hasFDerivAt.comp v hDinvM
    have hd : HasFDerivAt (fun u : EstInput S => (u a).2 i) (rewardL a i) v :=
      (rewardL a i).hasFDerivAt
    exact hc.mul hd
  have hsum : HasFDerivAt
      (fun u : EstInput S => ∑ i : S, Ring.inverse (mbSystem M u a) s i * (u a).2 i)
      (∑ i : S, gradPiece M v a s i) v :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hEach i)
  have hopen : ∀ᶠ u in nhds v, ∀ i : S, ∑ k, (u a).1 i k ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    have hne : visitL a i v ≠ 0 := by rw [visitL_apply]; exact hN i
    exact (visitL a i).continuous.continuousAt.eventually (eventually_ne_nhds hne)
  have heq : (fun u : EstInput S => mbValue M u a s)
      =ᶠ[nhds v] (fun u : EstInput S => ∑ i : S, Ring.inverse (mbSystem M u a) s i * (u a).2 i) := by
    filter_upwards [hopen] with u hu
    rw [mbValue_eq_mbSystem_inv_mulVec M u a hu, Matrix.nonsing_inv_eq_ringInverse]
    simp [Matrix.mulVec, dotProduct]
  exact hsum.congr_of_eventuallyEq heq

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

lemma sub_mbSystem_mulVec_mbValue (M : Model S) (v h : EstInput S) (a : Bool) :
    (fun i => (h a).2 i) - (mbSystem M h a).mulVec (mbValue M v a)
      = fun i => (h a).2 i + ∑ j, (h a).1 i j *
          (M.γdisc * mbValue M v a j - mbValue M v a i) := by
  funext i
  simp only [Pi.sub_apply, mbSystem_mulVec_apply]
  have hneg : ∀ j : S, (h a).1 i j * (M.γdisc * mbValue M v a j - mbValue M v a i)
      = -((h a).1 i j * (mbValue M v a i - M.γdisc * mbValue M v a j)) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hneg j), sub_eq_add_neg]
  congr 1
  simp

/-- **The gradient of the model-based plug-in estimator**, in closed form. -/
theorem fderiv_mbValue_apply (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) (hB : IsUnit (mbSystem M v a)) (s : S) (h : EstInput S) :
    fderiv ℝ (fun u : EstInput S => mbValue M u a s) v h
      = ((mbSystem M v a)⁻¹.mulVec (fun i =>
          (h a).2 i + ∑ j, (h a).1 i j *
            (M.γdisc * mbValue M v a j - mbValue M v a i))) s := by
  have key := hasFDerivAt_mbValue M v a hN hB s
  rw [key.fderiv, ContinuousLinearMap.sum_apply]
  have hri : Ring.inverse (mbSystem M v a) = (mbSystem M v a)⁻¹ :=
    (Matrix.nonsing_inv_eq_ringInverse _).symm
  simp only [gradPiece_apply, hri]
  set B := (mbSystem M v a)⁻¹ with hBdef
  set X := mbSystem M h a with hXdef
  rw [Finset.sum_sub_distrib]
  have e1 : ∑ i, B s i * (h a).2 i = (B.mulVec (fun i => (h a).2 i)) s := rfl
  have e2 : ∑ i, (v a).2 i * ((B * X * B) s i)
      = ((B * X * B).mulVec (fun i => (v a).2 i)) s := by
    show _ = ∑ i, (B * X * B) s i * (v a).2 i
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  have e3 : (B * X * B).mulVec (fun i => (v a).2 i)
      = B.mulVec (X.mulVec (mbValue M v a)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← mbValue_eq_mbSystem_inv_mulVec M v a hN]
  rw [e3, ← Pi.sub_apply, ← Matrix.mulVec_sub, sub_mbSystem_mulVec_mbValue M v h a]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- **The gradient of the model-based ATE estimator**: the difference of the two arm
gradients. -/
theorem fderiv_mbATE_apply (M : Model S) (v : EstInput S)
    (hN : ∀ a i, ∑ k, (v a).1 i k ≠ 0) (hB : ∀ a, IsUnit (mbSystem M v a))
    (s : S) (h : EstInput S) :
    fderiv ℝ (fun u : EstInput S => mbATE M u s) v h
      = ((mbSystem M v true)⁻¹.mulVec (fun i =>
          (h true).2 i + ∑ j, (h true).1 i j *
            (M.γdisc * mbValue M v true j - mbValue M v true i))) s
        - ((mbSystem M v false)⁻¹.mulVec (fun i =>
          (h false).2 i + ∑ j, (h false).1 i j *
            (M.γdisc * mbValue M v false j - mbValue M v false i))) s := by
  have ht := hasFDerivAt_mbValue M v true (hN true) (hB true) s
  have hf := hasFDerivAt_mbValue M v false (hN false) (hB false) s
  have hsub : HasFDerivAt (fun u : EstInput S => mbATE M u s)
      ((∑ i : S, gradPiece M v true s i) - (∑ i : S, gradPiece M v false s i)) v := by
    have := ht.sub hf
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    exact congrFun (mbATE_eq_mbValue M u) s
  rw [hsub.fderiv, ContinuousLinearMap.sub_apply, ← ht.fderiv, ← hf.fderiv,
    fderiv_mbValue_apply M v true (hN true) (hB true) s h,
    fderiv_mbValue_apply M v false (hN false) (hB false) s h]

end TreatmentLocality

end

-- === tl_mds.lean ===
section



open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

section Aux

variable {α : Type*} [MeasurableSpace α]

lemma integrable_of_bdd (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

end Aux

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- Integrability against the one-step experiment law, arm by arm. -/
lemma integrable_stepLaw (M : Model S) (s : S) {F : Bool × S × ℝ → ℝ} (hF : Measurable F)
    (hint : ∀ γ : Bool, Integrable (fun q : S × ℝ => F (γ, q))
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) :
    Integrable F (stepLaw M s) := by
  have hintd : ∀ γ : Bool, Integrable F ((Measure.dirac γ).prod
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) := by
    intro γ
    rw [Measure.dirac_prod]
    exact (integrable_map_measure hF.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 (hint γ)
  rw [stepLaw]
  exact Integrable.smul_measure (integrable_add_measure.mpr ⟨hintd true, hintd false⟩)
    (by norm_num)

/-- The scheme weight is measurable. -/
lemma measurable_isWeight (M : Model S) (s : S) (a : Bool) :
    Measurable (fun p : Bool × S × ℝ =>
      (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)) := by
  by_cases hs : s = M.crucial
  · simp only [if_pos hs]
    exact (Measurable.ite (measurable_fst (measurableSet_singleton a))
      measurable_const measurable_const).const_mul 2
  · simp only [if_neg hs]; exact measurable_const

lemma isWeight_abs_le (M : Model S) (s : S) (a : Bool) (p : Bool × S × ℝ) :
    |(if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)| ≤ 2 := by
  split_ifs <;> norm_num

/-- The weighted next-state value, integrated against the step law, is `P^a` applied to
the value vector. -/
lemma integral_stepLaw_value (M : Model S) (s : S) (a : Bool) (V : S → ℝ) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * V p.2.1)
        ∂(stepLaw M s)
      = ∑ j, M.polTrans a s j * V j := by
  classical
  have hsplit : ∀ p : Bool × S × ℝ,
      ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * V p.2.1)
        = ∑ j, V j *
          ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
            * (if p.2.1 = j then (1 : ℝ) else 0)) := by
    intro p
    rw [Finset.sum_eq_single p.2.1 (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
    ring
  have hmeas : ∀ j : S, Measurable (fun p : Bool × S × ℝ => V j *
      ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (if p.2.1 = j then (1 : ℝ) else 0))) := by
    intro j
    exact ((measurable_isWeight M s a).mul (Measurable.ite
      ((measurable_fst.comp measurable_snd) (measurableSet_singleton j))
      measurable_const measurable_const)).const_mul _
  have hint : ∀ j : S, Integrable (fun p : Bool × S × ℝ => V j *
      ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (if p.2.1 = j then (1 : ℝ) else 0))) (stepLaw M s) := by
    intro j
    refine integrable_of_bdd _ (hmeas j) (C := |V j| * 2) (fun p => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_mul]
    have h2 : |if p.2.1 = j then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    calc |if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1|
          * |if p.2.1 = j then (1 : ℝ) else 0| ≤ 2 * 1 :=
          mul_le_mul (isWeight_abs_le M s a p) h2 (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  rw [integral_finsetSum (μ := stepLaw M s)
    (f := fun (j : S) (p : Bool × S × ℝ) => V j *
      ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (if p.2.1 = j then (1 : ℝ) else 0))) _ (fun j _ => hint j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_stepLaw_indicator M s j a]
  rw [Model.polTrans, Matrix.of_apply]
  ring

/-- The scheme weight integrates to `1`. -/
lemma integral_stepLaw_weight (M : Model S) (s : S) (a : Bool) :
    ∫ p : Bool × S × ℝ,
        (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) ∂(stepLaw M s)
      = 1 := by
  have h := integral_stepLaw_value M s a (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  exact polTrans_row_sum M a s

/-- Integrability of a function of the reward coordinate against a product law. -/
lemma integrable_prod_snd (μ : Measure S) (ρ : Measure ℝ) [IsProbabilityMeasure μ] [SFinite ρ]
    {g : ℝ → ℝ} (hg : Measurable g) (hint : Integrable g ρ) :
    Integrable (fun q : S × ℝ => g q.2) (μ.prod ρ) := by
  have h1 : (μ.prod ρ).map Prod.snd = ρ := by rw [Measure.map_snd_prod]; simp
  refine (integrable_map_measure (g := g) (f := Prod.snd) (μ := μ.prod ρ) ?_
    measurable_snd.aemeasurable).1 ?_
  · rw [h1]; exact hg.aestronglyMeasurable
  · rw [h1]; exact hint

/-- The weighted reward is integrable against the step law. -/
lemma integrable_stepLaw_rwd (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) :
    Integrable (fun p : Bool × S × ℝ =>
      (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * p.2.2)
      (stepLaw M s) := by
  refine integrable_stepLaw M s
    ((measurable_isWeight M s a).mul (measurable_snd.comp measurable_snd)) (fun γ => ?_)
  show Integrable (fun q : S × ℝ =>
    (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1) * q.2) _
  exact Integrable.const_mul
    (integrable_prod_snd ((M.trans s (M.act γ s)).toMeasure) (M.reward s (M.act γ s))
      (g := fun r : ℝ => r) measurable_id (hR s (M.act γ s))) _

/-- **The inverse-probability-weighted temporal difference, integrated against the one-step
experiment law.** -/
lemma integral_stepLaw_td (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) (V : S → ℝ) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
          * (p.2.2 + M.γdisc * V p.2.1 - V s)) ∂(stepLaw M s)
      = M.polReward a s + M.γdisc * (∑ j, M.polTrans a s j * V j) - V s := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, ∀ j, |V j| ≤ C :=
    ⟨∑ t, |V t|, fun j => Finset.single_le_sum (fun t _ => abs_nonneg (V t)) (Finset.mem_univ j)⟩
  set W : Bool × S × ℝ → ℝ :=
    fun p => (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) with hW
  have hWm : Measurable W := measurable_isWeight M s a
  have hWb : ∀ p, |W p| ≤ 2 := isWeight_abs_le M s a
  have h1 : Integrable (fun p : Bool × S × ℝ => W p * p.2.2) (stepLaw M s) :=
    integrable_stepLaw_rwd M s a hR
  have h2 : Integrable (fun p : Bool × S × ℝ => M.γdisc * (W p * V p.2.1)) (stepLaw M s) := by
    refine integrable_of_bdd _ ((hWm.mul
      ((measurable_of_countable V).comp (measurable_fst.comp measurable_snd))).const_mul _)
      (C := |M.γdisc| * (2 * C)) (fun p => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul (hWb p) (hC _) (abs_nonneg _) (by norm_num)
  have h3 : Integrable (fun p : Bool × S × ℝ => V s * W p) (stepLaw M s) := by
    refine integrable_of_bdd _ (hWm.const_mul _) (C := |V s| * 2) (fun p => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hWb p) (abs_nonneg _)
  have hexp : ∀ p : Bool × S × ℝ,
      W p * (p.2.2 + M.γdisc * V p.2.1 - V s)
        = (W p * p.2.2 + M.γdisc * (W p * V p.2.1)) - V s * W p := fun p => by ring
  have e1 : ∫ p : Bool × S × ℝ,
        (W p * p.2.2 + M.γdisc * (W p * V p.2.1) - V s * W p) ∂(stepLaw M s)
      = (∫ p, W p * p.2.2 ∂(stepLaw M s))
        + (∫ p, M.γdisc * (W p * V p.2.1) ∂(stepLaw M s))
        - (∫ p, V s * W p ∂(stepLaw M s)) := by
    have h12 : Integrable (fun p : Bool × S × ℝ => W p * p.2.2 + M.γdisc * (W p * V p.2.1))
        (stepLaw M s) := h1.add h2
    rw [← integral_add h1 h2, ← integral_sub h12 h3]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), e1]
  simp only [hW]
  rw [integral_const_mul, integral_const_mul, integral_stepLaw_rwd M s a hR,
    integral_stepLaw_value M s a V, integral_stepLaw_weight M s a, mul_one]

/-- Integrability of the weighted temporal-difference error against the step law. -/
lemma integrable_stepLaw_td (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) (V : S → ℝ) :
    Integrable (fun p : Bool × S × ℝ =>
      (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (p.2.2 + M.γdisc * V p.2.1 - V s)) (stepLaw M s) := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, ∀ j, |V j| ≤ C :=
    ⟨∑ t, |V t|, fun j => Finset.single_le_sum (fun t _ => abs_nonneg (V t)) (Finset.mem_univ j)⟩
  set W : Bool × S × ℝ → ℝ :=
    fun p => (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) with hW
  have hWm : Measurable W := measurable_isWeight M s a
  have hWb : ∀ p, |W p| ≤ 2 := isWeight_abs_le M s a
  have h1 : Integrable (fun p : Bool × S × ℝ => W p * p.2.2) (stepLaw M s) :=
    integrable_stepLaw_rwd M s a hR
  have h2 : Integrable (fun p : Bool × S × ℝ => M.γdisc * (W p * V p.2.1)) (stepLaw M s) := by
    refine integrable_of_bdd _ ((hWm.mul
      ((measurable_of_countable V).comp (measurable_fst.comp measurable_snd))).const_mul _)
      (C := |M.γdisc| * (2 * C)) (fun p => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul (hWb p) (hC _) (abs_nonneg _) (by norm_num)
  have h3 : Integrable (fun p : Bool × S × ℝ => V s * W p) (stepLaw M s) := by
    refine integrable_of_bdd _ (hWm.const_mul _) (C := |V s| * 2) (fun p => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hWb p) (abs_nonneg _)
  have h12 : Integrable (fun p : Bool × S × ℝ => W p * p.2.2 + M.γdisc * (W p * V p.2.1))
      (stepLaw M s) := h1.add h2
  refine ((h12.sub h3).congr (Filter.Eventually.of_forall fun p => ?_))
  simp only [Pi.sub_apply, hW]
  ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The per-step statistic contracted against the plug-in gradient vector: an
inverse-probability-weighted temporal-difference error supported at the current state. -/
lemma estObs_grad_vec (M : Model S) (v : EstInput S) (a : Bool) (z : Step S) (i : S) :
    (estObs M .IS z a).2 i + ∑ j, (estObs M .IS z a).1 i j *
        (M.γdisc * mbValue M v a j - mbValue M v a i)
      = (if Step.state z = i then (1 : ℝ) else 0) *
        (schemeWeight M .IS a z *
          (Step.rwd z + M.γdisc * mbValue M v a (Step.next z) - mbValue M v a i)) := by
  classical
  by_cases h : Step.state z = i
  · rw [if_pos h]
    have h2 : ∀ j : S, (estObs M .IS z a).1 i j
        = schemeWeight M .IS a z * (if Step.next z = j then (1 : ℝ) else 0) := by
      intro j; simp [estObs, h]
    have h1 : (estObs M .IS z a).2 i = schemeWeight M .IS a z * Step.rwd z := by
      simp [estObs, h]
    rw [h1, Finset.sum_congr rfl (fun j _ => by rw [h2 j]),
      Finset.sum_eq_single (Step.next z) (fun b _ hb => by simp [Ne.symm hb])
        (fun hc => absurd (Finset.mem_univ _) hc)]
    simp
    ring
  · rw [if_neg h]
    have h1 : (estObs M .IS z a).2 i = 0 := by simp [estObs, h]
    have h2 : ∀ j : S, (estObs M .IS z a).1 i j = 0 := by intro j; simp [estObs, h]
    rw [h1, Finset.sum_congr rfl (fun j _ => by rw [h2 j])]
    simp

/-- The arm-`a` half of the influence function of the model-based estimator. -/
lemma mulVec_estObs_grad (M : Model S) (v : EstInput S) (a : Bool) (s : S) (z : Step S) :
    ((mbSystem M v a)⁻¹.mulVec (fun i =>
        (estObs M .IS z a).2 i + ∑ j, (estObs M .IS z a).1 i j *
          (M.γdisc * mbValue M v a j - mbValue M v a i))) s
      = (mbSystem M v a)⁻¹ s (Step.state z) *
        (schemeWeight M .IS a z *
          (Step.rwd z + M.γdisc * mbValue M v a (Step.next z)
            - mbValue M v a (Step.state z))) := by
  classical
  rw [Matrix.mulVec, dotProduct,
    Finset.sum_congr rfl (fun i _ => by rw [estObs_grad_vec M v a z i]),
    Finset.sum_eq_single (Step.state z) (fun b _ hb => by simp [Ne.symm hb])
      (fun hc => absurd (Finset.mem_univ _) hc)]
  simp

/-- **The influence function of the model-based estimator**, in closed form: a difference
of inverse-probability-weighted temporal-difference errors. -/
theorem fderiv_mbATE_estObs (M : Model S) (v : EstInput S)
    (hN : ∀ a i, ∑ k, (v a).1 i k ≠ 0) (hB : ∀ a, IsUnit (mbSystem M v a))
    (s : S) (z : Step S) :
    fderiv ℝ (fun u : EstInput S => mbATE M u s) v (estObs M .IS z)
      = (mbSystem M v true)⁻¹ s (Step.state z) *
          (schemeWeight M .IS true z *
            (Step.rwd z + M.γdisc * mbValue M v true (Step.next z)
              - mbValue M v true (Step.state z)))
        - (mbSystem M v false)⁻¹ s (Step.state z) *
          (schemeWeight M .IS false z *
            (Step.rwd z + M.γdisc * mbValue M v false (Step.next z)
              - mbValue M v false (Step.state z))) := by
  rw [fderiv_mbATE_apply M v hN hB s (estObs M .IS z),
    mulVec_estObs_grad M v true s z, mulVec_estObs_grad M v false s z]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The influence weight of the true value function is centred at every state**: the
inverse-probability-weighted temporal-difference error has zero mean under the one-step
experiment law. -/
theorem integral_stepLaw_td_value (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
          * (p.2.2 + M.γdisc * M.value a p.2.1 - M.value a s)) ∂(stepLaw M s)
      = 0 := by
  rw [integral_stepLaw_td M s a hR (M.value a)]
  have h := value_bellman_apply M a s
  linarith

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma measurable_schemeWeight (M : Model S) (a : Bool) :
    Measurable (fun z : Step S => schemeWeight M .IS a z) := by
  have hcr : MeasurableSet {z : Step S | Step.state z = M.crucial} :=
    measurable_fst (measurableSet_singleton M.crucial)
  have harm : MeasurableSet {z : Step S | Step.arm z = a} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton a)
  exact Measurable.ite hcr
    ((Measurable.ite harm measurable_const measurable_const).const_mul 2) measurable_const

lemma meanObs_IS_visit_ne_zero (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) (i : S) :
    ∑ k, ((meanObs M .IS ν) a).1 i k ≠ 0 := by
  rw [meanObs_IS_visit M ν hinv a i]; exact hμ i

/-- At the population statistics the plug-in Bellman system is invertible. -/
theorem isUnit_mbSystem_meanObs_IS (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    IsUnit (mbSystem M (meanObs M .IS ν) a) := by
  have hN : ∀ i, ∑ k, ((meanObs M .IS ν) a).1 i k ≠ 0 :=
    fun i => meanObs_IS_visit_ne_zero M ν hinv hμ a i
  rw [mbSystem_eq_diagonal_mul M _ a hN, mbTrans_meanObs_IS M ν hinv hμ a]
  refine IsUnit.mul ?_ (isUnit_one_sub_smul_polTrans M a)
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hN i)

/-- **The influence function of the information-sharing estimator at the population
statistics**: a difference of inverse-probability-weighted temporal-difference errors of
the *true* value functions. -/
theorem influence_eq (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (s : S) (y : Step S) :
    fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)
      = (mbSystem M (meanObs M .IS ν) true)⁻¹ s (Step.state y) *
          (schemeWeight M .IS true y * (Step.rwd y + M.γdisc * M.value true (Step.next y)
            - M.value true (Step.state y)))
        - (mbSystem M (meanObs M .IS ν) false)⁻¹ s (Step.state y) *
          (schemeWeight M .IS false y * (Step.rwd y + M.γdisc * M.value false (Step.next y)
            - M.value false (Step.state y))) := by
  rw [fderiv_mbATE_estObs M (meanObs M .IS ν)
    (fun a i => meanObs_IS_visit_ne_zero M ν hinv hμ a i)
    (fun a => isUnit_mbSystem_meanObs_IS M ν hinv hμ a) s y,
    mbValue_meanObs_IS M ν hinv hR hrint hμ true,
    mbValue_meanObs_IS M ν hinv hR hrint hμ false]

lemma measurable_influence (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S) :
    Measurable (fun y : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)) := by
  have hst : Measurable (fun y : Step S => Step.state y) := measurable_fst
  have hnx : Measurable (fun y : Step S => Step.next y) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hrw : Measurable (fun y : Step S => Step.rwd y) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have key : ∀ a : Bool, Measurable (fun y : Step S =>
      (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
        (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
          - M.value a (Step.state y)))) := by
    intro a
    refine Measurable.mul ((measurable_of_countable _).comp hst) ?_
    exact (measurable_schemeWeight M a).mul
      ((hrw.add (((measurable_of_countable (M.value a)).comp hnx).const_mul _)).sub
        ((measurable_of_countable (M.value a)).comp hst))
  simp only [influence_eq M ν hinv hR hrint hμ s]
  exact (key true).sub (key false)

/-- **The influence function is centred under the one-step experiment law.** -/
theorem integral_stepLaw_influence_eq_zero (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (s : S) (s₀ : S) :
    ∫ p : Bool × S × ℝ,
        fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS (s₀, p))
        ∂(stepLaw M s₀) = 0 := by
  simp only [influence_eq M ν hinv hR hrint hμ s]
  show ∫ p : Bool × S × ℝ,
      ((mbSystem M (meanObs M .IS ν) true)⁻¹ s s₀ *
          ((if s₀ = M.crucial then 2 * (if p.1 = true then (1 : ℝ) else 0) else 1)
            * (p.2.2 + M.γdisc * M.value true p.2.1 - M.value true s₀))
        - (mbSystem M (meanObs M .IS ν) false)⁻¹ s s₀ *
          ((if s₀ = M.crucial then 2 * (if p.1 = false then (1 : ℝ) else 0) else 1)
            * (p.2.2 + M.γdisc * M.value false p.2.1 - M.value false s₀)))
      ∂(stepLaw M s₀) = 0
  have hint : ∀ a : Bool, Integrable (fun p : Bool × S × ℝ =>
      (if s₀ = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (p.2.2 + M.γdisc * M.value a p.2.1 - M.value a s₀)) (stepLaw M s₀) :=
    fun a => integrable_stepLaw_td M s₀ a hR (M.value a)
  have hA := (hint true).const_mul ((mbSystem M (meanObs M .IS ν) true)⁻¹ s s₀)
  have hB := (hint false).const_mul ((mbSystem M (meanObs M .IS ν) false)⁻¹ s s₀)
  rw [integral_sub hA hB, integral_const_mul, integral_const_mul,
    integral_stepLaw_td_value M s₀ true hR, integral_stepLaw_td_value M s₀ false hR]
  ring

/-- **The influence function has zero conditional mean given the past**: it is a
martingale difference along the experiment chain. -/
theorem integral_influence_expKernel_eq_zero (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (s : S) (z : Step S) :
    ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)
        ∂(expKernel M z) = 0 := by
  rw [integral_expKernel M z (measurable_influence M ν hinv hR hrint hμ s)]
  exact integral_stepLaw_influence_eq_zero M ν hinv hR hrint hμ s (Step.next z)

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma schemeWeight_IS_abs_le (M : Model S) (a : Bool) (y : Step S) :
    |schemeWeight M .IS a y| ≤ 2 := by
  show |if Step.state y = M.crucial then 2 * (if Step.arm y = a then (1 : ℝ) else 0) else 1| ≤ 2
  split_ifs <;> norm_num

private lemma abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  calc |x - y| = |x + -y| := by ring_nf
    _ ≤ |x| + |-y| := abs_add_le _ _
    _ = |x| + |y| := by rw [abs_neg]

/-- The influence function is integrable against any finite measure with integrable
reward coordinate. -/
theorem integrable_influence (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hr : Integrable (fun z : Step S => Step.rwd z) μ) :
    Integrable (fun y : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)) μ := by
  have hst : Measurable (fun y : Step S => Step.state y) := measurable_fst
  have hnx : Measurable (fun y : Step S => Step.next y) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hrw : Measurable (fun y : Step S => Step.rwd y) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have key : ∀ a : Bool, Integrable (fun y : Step S =>
      (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
        (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
          - M.value a (Step.state y)))) μ := by
    intro a
    obtain ⟨C, hC0, hC⟩ : ∃ C, 0 ≤ C ∧ ∀ i, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s i| ≤ C :=
      ⟨∑ t, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s t|,
        Finset.sum_nonneg fun t _ => abs_nonneg _,
        fun i => Finset.single_le_sum
          (f := fun t => |(mbSystem M (meanObs M .IS ν) a)⁻¹ s t|)
          (fun t _ => abs_nonneg _) (Finset.mem_univ i)⟩
    obtain ⟨D, hD0, hD⟩ : ∃ D, 0 ≤ D ∧ ∀ i, |M.value a i| ≤ D :=
      ⟨∑ t, |M.value a t|, Finset.sum_nonneg fun t _ => abs_nonneg _,
        fun i => Finset.single_le_sum (f := fun t => |M.value a t|)
          (fun t _ => abs_nonneg _) (Finset.mem_univ i)⟩
    have hgm : Measurable (fun y : Step S =>
        (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y) :=
      ((measurable_of_countable _).comp hst).mul (measurable_schemeWeight M a)
    have hgb : ∀ y : Step S, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y)
        * schemeWeight M .IS a y| ≤ C * 2 := by
      intro y
      rw [abs_mul]
      exact mul_le_mul (hC _) (schemeWeight_IS_abs_le M a y) (abs_nonneg _) hC0
    have hhm : Measurable (fun y : Step S =>
        ((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y)
          * (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y))) :=
      hgm.mul ((((measurable_of_countable (M.value a)).comp hnx).const_mul _).sub
        ((measurable_of_countable (M.value a)).comp hst))
    have hhb : ∀ y : Step S,
        |((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y)
          * (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y))|
          ≤ (C * 2) * (|M.γdisc| * D + D) := by
      intro y
      rw [abs_mul]
      refine mul_le_mul (hgb y) ?_ (abs_nonneg _) (by positivity)
      refine (abs_sub_le_add _ _).trans ?_
      have h1 : |M.γdisc * M.value a (Step.next y)| ≤ |M.γdisc| * D := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
      exact add_le_add h1 (hD _)
    have e : ∀ y : Step S,
        (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
          (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
            - M.value a (Step.state y)))
        = ((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y)
            * Step.rwd y
          + ((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y)
            * (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y)) :=
      fun y => by ring
    refine Integrable.congr ?_ (Filter.Eventually.of_forall fun y => (e y).symm)
    exact (hr.bdd_mul hgm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hgb y)).add
      (integrable_of_bdd _ hhm hhb)
  simp only [influence_eq M ν hinv hR hrint hμ s]
  exact (key true).sub (key false)

/-- The influence function has mean zero under the stationary law. -/
theorem integral_influence_eq_zero (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S) :
    ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y) ∂ν
      = 0 := by
  rw [integral_eq_integral_stepLaw M ν hinv (measurable_influence M ν hinv hR hrint hμ s)
    (integrable_influence M ν hinv hR hrint hμ s ν hrint)]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
    integral_stepLaw_influence_eq_zero M ν hinv hR hrint hμ s (Step.state z))]
  simp

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The conditional expectation of the influence function at any positive lag vanishes. -/
theorem integral_iterKernel_influence (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x))
    (s : S) (k : ℕ) (x : Step S) :
    ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)
        ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) x) = 0 := by
  have hI : Integrable (fun y : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y))
      (MarkovChainCLT.iterKernel (expKernel M) (k + 1) x) :=
    integrable_influence M ν hinv hR hrint hμ s _ (hiter (k + 1) x)
  rw [MarkovChainCLT.iterKernel_succ] at hI ⊢
  rw [Kernel.integral_comp hI]
  simp only [integral_influence_expKernel_eq_zero M ν hinv hR hrint hμ s]
  simp

/-- **All lagged autocovariances of the influence function vanish.** -/
theorem lagCovariance_influence_succ (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x))
    (s s' : S) (k : ℕ) :
    MarkovChainCLT.lagCovariance (expKernel M) ν
      (fun z => fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
        (estObs M .IS z))
      (fun z => fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
        (estObs M .IS z)) (k + 1) = 0 := by
  rw [MarkovChainCLT.lagCovariance]
  have hz : ∀ x : Step S,
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS x)
          - ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
              (estObs M .IS y) ∂ν)
        * ((∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS y) ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) x))
          - ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS y) ∂ν) = 0 := by
    intro x
    rw [integral_iterKernel_influence M ν hinv hR hrint hμ hiter s' k x,
      integral_influence_eq_zero M ν hinv hR hrint hμ s']
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hz)]
  simp

/-- **The asymptotic covariance of the information-sharing estimator is instantaneous.**
Because the influence function is a martingale difference along the experiment chain, the
lagged terms of `Σ_IS` all vanish and only the one-step covariance survives. -/
theorem mbISCov_eq_integral (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x))
    (s s' : S) :
    mbISCov M ν s s'
      = ∫ z, (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
                (estObs M .IS z))
            * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
                (estObs M .IS z)) ∂ν := by
  rw [mbISCov, Matrix.of_apply, MarkovChainCLT.asymptoticCovariance,
    tsum_congr (fun k => lagCovariance_influence_succ M ν hinv hR hrint hμ hiter s s' k),
    tsum_congr (fun k => lagCovariance_influence_succ M ν hinv hR hrint hμ hiter s' s k),
    tsum_zero, add_zero, add_zero, MarkovChainCLT.lagCovariance]
  have hdir : ∀ x : Step S,
      ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν) (estObs M .IS y)
          ∂(MarkovChainCLT.iterKernel (expKernel M) 0 x)
        = fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν) (estObs M .IS x) := by
    intro x
    rw [MarkovChainCLT.iterKernel_zero, Kernel.id_apply]
    exact integral_dirac' _ x (measurable_influence M ν hinv hR hrint hμ s').stronglyMeasurable
  have e : ∀ x : Step S,
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS x)
          - ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
              (estObs M .IS y) ∂ν)
        * ((∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS y) ∂(MarkovChainCLT.iterKernel (expKernel M) 0 x))
          - ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS y) ∂ν)
        = (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS x))
          * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS x)) := by
    intro x
    rw [hdir x, integral_influence_eq_zero M ν hinv hR hrint hμ s,
      integral_influence_eq_zero M ν hinv hR hrint hμ s']
    ring
  exact integral_congr_ae (Filter.Eventually.of_forall e)

end TreatmentLocality

end

-- === mc_l1.lean ===
section



open Filter Finset Function MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

/-- The σ-algebra generated by the coordinates `≤ k`. -/
def pathSigma (X : Type*) [MeasurableSpace X] (k : ℕ) : MeasurableSpace (ℕ → X) :=
  MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => X) k) inferInstance

lemma pathSigma_le (k : ℕ) :
    pathSigma X k ≤ (inferInstance : MeasurableSpace (ℕ → X)) :=
  Measurable.comap_le (Preorder.measurable_frestrictLe (X := fun _ : ℕ => X) k)

lemma measurable_coord_pathSigma {i k : ℕ} (hik : i ≤ k) :
    Measurable[pathSigma X k] (fun ω : ℕ → X => ω i) := by
  have hfr : Measurable[pathSigma X k] (Preorder.frestrictLe (π := fun _ : ℕ => X) k) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (⟨i, Finset.mem_Iic.2 hik⟩ : ↑(Finset.Iic k))).comp hfr

/-- The truncation of a real function at level `n`. -/
noncomputable def trunc (h : X → ℝ) (n : ℕ) : X → ℝ :=
  fun x => if |h x| ≤ (n : ℝ) then h x else 0

lemma measurable_trunc {h : X → ℝ} (hh : Measurable h) (n : ℕ) : Measurable (trunc h n) := by
  refine Measurable.ite ?_ hh measurable_const
  exact (hh.abs) measurableSet_Iic

lemma abs_trunc_le (h : X → ℝ) (n : ℕ) (x : X) : |trunc h n x| ≤ (n : ℝ) := by
  rw [trunc]
  split_ifs with hx
  · exact hx
  · simpa using Nat.cast_nonneg n

lemma abs_trunc_le_abs (h : X → ℝ) (n : ℕ) (x : X) : |trunc h n x| ≤ |h x| := by
  rw [trunc]
  split_ifs
  · exact le_rfl
  · simpa using abs_nonneg (h x)

lemma tendsto_trunc (h : X → ℝ) (x : X) :
    Tendsto (fun n : ℕ => trunc h n x) atTop (𝓝 (h x)) := by
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈|h x|⌉₊) (fun n hn => ?_)
  have : |h x| ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.2 hn)
  simp [trunc, this]

end MarkovChainCLT

namespace MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

lemma measurable_kernel_integral (P : Kernel X X) [IsMarkovKernel P] {g : X → ℝ}
    (hg : Measurable g) : Measurable (fun x => ∫ y, g y ∂(P x)) :=
  (StronglyMeasurable.integral_kernel (κ := P) hg.stronglyMeasurable).measurable

set_option maxHeartbeats 1000000 in
/-- **The Markov property of the path measure, for integrable observables.** -/
theorem condExp_next_coord_of_integrable (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (h : X → ℝ) (hh : Measurable h) (hint : Integrable h π) (k : ℕ) :
    (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k)))
      =ᵐ[chainMeasure P π] (chainMeasure P π)[fun ω : ℕ → X => h (ω (k + 1)) |
        pathSigma X k] := by
  set μ := chainMeasure P π with hμdef
  have hm : pathSigma X k ≤ (inferInstance : MeasurableSpace (ℕ → X)) := pathSigma_le k
  have hmap : ∀ n : ℕ, Measure.map (fun ω : ℕ → X => ω n) μ = π :=
    fun n => map_coord_chainMeasure P π hinv n
  have hqmp : ∀ n : ℕ, Measure.QuasiMeasurePreserving (fun ω : ℕ → X => ω n) μ π :=
    fun n => ⟨measurable_pi_apply n, by rw [hmap n]⟩
  -- the observed coordinate is integrable
  have hf : Integrable (fun ω : ℕ → X => h (ω (k + 1))) μ := by
    have hiff := integrable_map_measure (g := h) (f := fun ω : ℕ → X => ω (k + 1)) (μ := μ)
      (by rw [hmap (k + 1)]; exact hh.aestronglyMeasurable)
      (measurable_pi_apply (k + 1)).aemeasurable
    rw [hmap (k + 1)] at hiff
    exact hiff.1 hint
  -- integrability along the kernel
  have hcomp : Integrable h (P ∘ₘ π) := by
    show Integrable h (π.bind P)
    rw [hinv]; exact hint
  obtain ⟨hae, hnorm⟩ := (Measure.integrable_comp_iff (κ := P) (μ := π) (f := h)
    (by show AEStronglyMeasurable h (π.bind P); rw [hinv]; exact hh.aestronglyMeasurable)).1 hcomp
  have haeμ : ∀ᵐ ω ∂μ, Integrable h (P (ω k)) := (hqmp k).ae hae
  have hnormm : Measurable (fun x : X => ∫ y, ‖h y‖ ∂(P x)) :=
    measurable_kernel_integral P hh.norm
  have hnormμ : Integrable (fun ω : ℕ → X => ∫ y, ‖h y‖ ∂(P (ω k))) μ := by
    have hiff := integrable_map_measure (g := fun x : X => ∫ y, ‖h y‖ ∂(P x))
      (f := fun ω : ℕ → X => ω k) (μ := μ)
      (by rw [hmap k]; exact hnormm.aestronglyMeasurable)
      (measurable_pi_apply k).aemeasurable
    rw [hmap k] at hiff
    exact hiff.1 hnorm
  have hgm : Measurable (fun x : X => ∫ y, h y ∂(P x)) := measurable_kernel_integral P hh
  have hgint : Integrable (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k))) μ := by
    refine hnormμ.mono' ((hgm.comp (measurable_pi_apply k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    exact norm_integral_le_integral_norm _
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => hgint.integrableOn) ?_ ?_
  · rintro s ⟨A₀, hA₀, rfl⟩ -
    set T := (Preorder.frestrictLe (π := fun _ : ℕ => X) k) ⁻¹' A₀ with hT
    have key : ∀ n : ℕ,
        ∫ ω in T, trunc h n (ω (k + 1)) ∂μ
          = ∫ ω in T, (∫ y, trunc h n y ∂(P (ω k))) ∂μ :=
      fun n => setIntegral_next_coord_eq P π (trunc h n) (measurable_trunc hh n) (n : ℝ)
        (abs_trunc_le h n) k A₀ hA₀
    have L1 : Filter.Tendsto (fun n : ℕ => ∫ ω in T, trunc h n (ω (k + 1)) ∂μ) Filter.atTop
        (𝓝 (∫ ω in T, h (ω (k + 1)) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω : ℕ → X => |h (ω (k + 1))|)
        (fun n => (((measurable_trunc hh n).comp
          (measurable_pi_apply (k + 1))).aestronglyMeasurable))
        (hf.abs.integrableOn) (fun n => Filter.Eventually.of_forall fun ω => ?_)
        (Filter.Eventually.of_forall fun ω => tendsto_trunc h (ω (k + 1)))
      simpa [Real.norm_eq_abs] using abs_trunc_le_abs h n (ω (k + 1))
    have L2 : Filter.Tendsto (fun n : ℕ => ∫ ω in T, (∫ y, trunc h n y ∂(P (ω k))) ∂μ)
        Filter.atTop (𝓝 (∫ ω in T, (∫ y, h y ∂(P (ω k))) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun ω : ℕ → X => ∫ y, ‖h y‖ ∂(P (ω k)))
        (fun n => (((measurable_kernel_integral P (measurable_trunc hh n)).comp
          (measurable_pi_apply k)).aestronglyMeasurable))
        (hnormμ.integrableOn) (fun n => ?_) ?_
      · filter_upwards [ae_restrict_of_ae haeμ] with ω hω
        calc ‖∫ y, trunc h n y ∂(P (ω k))‖ ≤ ∫ y, ‖trunc h n y‖ ∂(P (ω k)) :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ y, ‖h y‖ ∂(P (ω k)) := by
              refine integral_mono ?_ hω.norm (fun y => ?_)
              · exact (hω.norm.mono' (measurable_trunc hh n).norm.aestronglyMeasurable
                  (Filter.Eventually.of_forall fun y => by
                    simpa [Real.norm_eq_abs] using abs_trunc_le_abs h n y))
              · simpa [Real.norm_eq_abs] using abs_trunc_le_abs h n y
      · filter_upwards [ae_restrict_of_ae haeμ] with ω hω
        refine tendsto_integral_of_dominated_convergence (fun y => |h y|)
          (fun n => (measurable_trunc hh n).aestronglyMeasurable) hω.abs
          (fun n => Filter.Eventually.of_forall fun y => by
            simpa [Real.norm_eq_abs] using abs_trunc_le_abs h n y)
          (Filter.Eventually.of_forall fun y => tendsto_trunc h y)
    exact tendsto_nhds_unique L2 (L1.congr key)
  · exact ((hgm.comp (measurable_coord_pathSigma (le_refl k))) :
      Measurable[pathSigma X k] _).stronglyMeasurable.aestronglyMeasurable

end MarkovChainCLT

end

-- === tl_score.lean ===
section



open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The influence function is square-integrable wherever the reward is. -/
theorem memLp_influence (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 μ) :
    MemLp (fun y : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
        (estObs M .IS y)) 2 μ := by
  have hst : Measurable (fun y : Step S => Step.state y) := measurable_fst
  have hnx : Measurable (fun y : Step S => Step.next y) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have key : ∀ a : Bool, MemLp (fun y : Step S =>
      (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
        (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
          - M.value a (Step.state y)))) 2 μ := by
    intro a
    obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s i| ≤ C :=
      ⟨∑ t, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s t|,
        Finset.sum_nonneg fun t _ => abs_nonneg _,
        fun i => Finset.single_le_sum
          (f := fun t => |(mbSystem M (meanObs M .IS ν) a)⁻¹ s t|)
          (fun t _ => abs_nonneg _) (Finset.mem_univ i)⟩
    obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ i, |M.value a i| ≤ D :=
      ⟨∑ t, |M.value a t|, Finset.sum_nonneg fun t _ => abs_nonneg _,
        fun i => Finset.single_le_sum (f := fun t => |M.value a t|)
          (fun t _ => abs_nonneg _) (Finset.mem_univ i)⟩
    obtain ⟨cw, hcwdef⟩ : ∃ f : Step S → ℝ, f = fun y : Step S =>
        (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y :=
      ⟨_, rfl⟩
    have hcwm : Measurable cw := by
      rw [hcwdef]
      exact ((measurable_of_countable _).comp hst).mul (measurable_schemeWeight M a)
    have hcwb : ∀ y : Step S, |cw y| ≤ C * 2 := by
      intro y
      simp only [hcwdef]
      rw [abs_mul]
      exact mul_le_mul (hC _) (schemeWeight_IS_abs_le M a y) (abs_nonneg _) hC0
    have hvm : Measurable (fun y : Step S =>
        M.γdisc * M.value a (Step.next y) - M.value a (Step.state y)) :=
      (((measurable_of_countable (M.value a)).comp hnx).const_mul _).sub
        ((measurable_of_countable (M.value a)).comp hst)
    have hvb : ∀ y : Step S,
        |M.γdisc * M.value a (Step.next y) - M.value a (Step.state y)|
          ≤ |M.γdisc| * D + D := by
      intro y
      have hsub : ∀ x z : ℝ, |x - z| ≤ |x| + |z| := fun x z => by
        calc |x - z| = |x + -z| := by ring_nf
          _ ≤ |x| + |-z| := abs_add_le _ _
          _ = |x| + |z| := by rw [abs_neg]
      refine (hsub _ _).trans (add_le_add ?_ (hD _))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
    have h1 : MemLp (fun y : Step S => cw y * Step.rwd y) 2 μ := by
      refine MemLp.of_le (hr2.const_mul (C * 2))
        (hcwm.mul measurable_rwd).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * 2)]
      exact mul_le_mul_of_nonneg_right (hcwb y) (abs_nonneg _)
    have h2 : MemLp (fun y : Step S => cw y *
        (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y))) 2 μ := by
      refine MemLp.of_bound (hcwm.mul hvm).aestronglyMeasurable
        ((C * 2) * (|M.γdisc| * D + D)) (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hcwb y) (hvb y) (abs_nonneg _) (by positivity)
    have hfun : (fun y : Step S =>
        (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
          (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
            - M.value a (Step.state y))))
        = fun y : Step S => cw y * Step.rwd y
          + cw y * (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y)) := by
      funext y
      simp only [hcwdef]
      ring
    rw [hfun]
    exact h1.add h2
  simp only [influence_eq M ν hinv hR hrint hμ s]
  exact (key true).sub (key false)

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The influence function of the information-sharing estimator contracted against a
direction `w`. -/
noncomputable def infl (M : Model S) (ν : Measure (Step S)) (w : S → ℝ) (z : Step S) : ℝ :=
  ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z)

lemma integrable_rwd_expKernel (M : Model S)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) (z : Step S) :
    Integrable (fun w : Step S => Step.rwd w) (expKernel M z) :=
  ⟨measurable_rwd.aestronglyMeasurable, lt_of_le_of_lt
    (lintegral_expKernel_rwd_le M (F := fun r : ℝ => ‖r‖ₑ) measurable_id.enorm z)
    (ENNReal.sum_lt_top.2 fun t _ => ENNReal.sum_lt_top.2 fun a _ => (hR t a).2)⟩

variable (M : Model S) (ν : Measure (Step S))

lemma measurable_infl [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ) :
    Measurable (infl M ν w) :=
  Finset.measurable_sum _ fun s _ =>
    (measurable_influence M ν hinv hR hrint hμ s).const_mul _

lemma memLp_infl [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 μ) :
    MemLp (infl M ν w) 2 μ :=
  memLp_finsetSum (μ := μ) (f := fun (s : S) (z : Step S) =>
      w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
    _ fun s _ => (memLp_influence M ν hinv hR hrint hμ s μ hr2).const_mul (w s)

lemma integrable_infl [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hr : Integrable (fun z : Step S => Step.rwd z) μ) :
    Integrable (infl M ν w) μ :=
  integrable_finsetSum (μ := μ) (f := fun (s : S) (z : Step S) =>
      w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
    _ fun s _ => (integrable_influence M ν hinv hR hrint hμ s μ hr).const_mul (w s)

/-- **The contracted influence function has zero conditional mean.** -/
theorem integral_infl_expKernel_eq_zero [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ)
    (z : Step S) :
    ∫ y, infl M ν w y ∂(expKernel M z) = 0 := by
  simp only [infl]
  rw [integral_finsetSum (μ := expKernel M z) (f := fun (s : S) (y : Step S) =>
      w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y))
    _ fun s _ => (integrable_influence M ν hinv hR hrint hμ s (expKernel M z)
      (integrable_rwd_expKernel M hR z)).const_mul (w s)]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [integral_const_mul, integral_influence_expKernel_eq_zero M ν hinv hR hrint hμ s z,
    mul_zero]

/-- The contracted influence function is centred under the stationary law. -/
theorem integral_infl_eq_zero [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ) :
    ∫ z, infl M ν w z ∂ν = 0 := by
  simp only [infl]
  rw [integral_finsetSum (μ := ν) (f := fun (s : S) (z : Step S) =>
      w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
    _ fun s _ => (integrable_influence M ν hinv hR hrint hμ s ν hrint).const_mul (w s)]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [integral_const_mul, integral_influence_eq_zero M ν hinv hR hrint hμ s, mul_zero]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The second moment of the contracted influence function is the information-sharing
asymptotic variance in that direction.** -/
theorem integral_infl_sq (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x)) (w : S → ℝ) :
    ∫ z, (infl M ν w z) ^ 2 ∂ν = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by
  have hL2 : ∀ s : S, MemLp (fun z : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z)) 2 ν :=
    fun s => memLp_influence M ν hinv hR hrint hμ s ν hr2
  have hprod : ∀ s s' : S, Integrable (fun z : Step S =>
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z))) ν := fun s s' => (hL2 s).integrable_mul (hL2 s')
  have hcprod : ∀ s s' : S, Integrable (fun z : Step S => (w s * w s') *
      ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z)))) ν := fun s s' => (hprod s s').const_mul _
  have hexp : ∀ z : Step S, (infl M ν w z) ^ 2
      = ∑ s, ∑ s', (w s * w s') *
        ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
          * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS z))) := by
    intro z
    simp only [infl, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [integral_finsetSum (μ := ν) (f := fun (s : S) (z : Step S) => ∑ s', (w s * w s') *
      ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z)))) _
    (fun s _ => integrable_finsetSum (μ := ν) (f := fun (s' : S) (z : Step S) =>
      (w s * w s') *
      ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z)))) _ (fun s' _ => hcprod s s'))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum (μ := ν) (f := fun (s' : S) (z : Step S) => (w s * w s') *
      ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z)))) _ (fun s' _ => hcprod s s')]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [integral_const_mul, ← mbISCov_eq_integral M ν hinv hR hrint hμ hiter s s']
  ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

section Chain

variable (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
  (hinv : Kernel.Invariant (expKernel M) ν)
  (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
  (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
  (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 ν)
  (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
  (w : S → ℝ)

include hinv hR hrint hμ in
lemma memLp_coord_infl (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 ν) (n : ℕ) :
    MemLp (fun ω : ℕ → Step S => infl M ν w (ω n)) 2
      (MarkovChainCLT.chainMeasure (expKernel M) ν) := by
  have hmap := MarkovChainCLT.map_coord_chainMeasure (expKernel M) ν hinv n
  have h : MemLp (infl M ν w) 2
      (Measure.map (fun ω : ℕ → Step S => ω n) (MarkovChainCLT.chainMeasure (expKernel M) ν)) := by
    rw [hmap]; exact memLp_infl M ν hinv hR hrint hμ w ν hr2
  exact (memLp_map_measure_iff h.1 (measurable_pi_apply n).aemeasurable).1 h

include hinv hR hrint hμ in
lemma integral_coord_infl (n : ℕ) :
    ∫ ω, infl M ν w (ω n) ∂(MarkovChainCLT.chainMeasure (expKernel M) ν) = 0 := by
  have hmap := MarkovChainCLT.map_coord_chainMeasure (expKernel M) ν hinv n
  have h := integral_map (μ := MarkovChainCLT.chainMeasure (expKernel M) ν)
    (φ := fun ω : ℕ → Step S => ω n) (f := infl M ν w)
    (measurable_pi_apply n).aemeasurable
    (by rw [hmap]; exact (measurable_infl M ν hinv hR hrint hμ w).aestronglyMeasurable)
  rw [hmap] at h
  rw [← h]
  exact integral_infl_eq_zero M ν hinv hR hrint hμ w

include hinv hR hrint hμ in
lemma integral_coord_infl_sq
    (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 ν)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x)) (n : ℕ) :
    ∫ ω, (infl M ν w (ω n)) ^ 2 ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
      = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by
  have hmap := MarkovChainCLT.map_coord_chainMeasure (expKernel M) ν hinv n
  have h := integral_map (μ := MarkovChainCLT.chainMeasure (expKernel M) ν)
    (φ := fun ω : ℕ → Step S => ω n) (f := fun z : Step S => (infl M ν w z) ^ 2)
    (measurable_pi_apply n).aemeasurable
    (by rw [hmap]
        exact ((measurable_infl M ν hinv hR hrint hμ w).pow_const 2).aestronglyMeasurable)
  rw [hmap] at h
  rw [← h]
  exact integral_infl_sq M ν hinv hR hrint hr2 hμ hiter w

include hinv hR hrint hμ in
lemma condExp_coord_infl (j : ℕ) :
    (MarkovChainCLT.chainMeasure (expKernel M) ν)[fun ω : ℕ → Step S => infl M ν w (ω (j + 1)) |
        MarkovChainCLT.pathSigma (Step S) j]
      =ᵐ[MarkovChainCLT.chainMeasure (expKernel M) ν] 0 := by
  have hker := (MarkovChainCLT.condExp_next_coord_of_integrable (expKernel M) ν hinv
    (infl M ν w) (measurable_infl M ν hinv hR hrint hμ w)
    (integrable_infl M ν hinv hR hrint hμ w ν hrint) j).symm
  filter_upwards [hker] with ω hω
  simp only [Pi.zero_apply]
  rw [hω]
  exact integral_infl_expKernel_eq_zero M ν hinv hR hrint hμ w (ω j)

include hinv hR hrint hμ in
lemma stronglyMeasurable_coord_infl {n j : ℕ} (hnj : n ≤ j) :
    StronglyMeasurable[MarkovChainCLT.pathSigma (Step S) j]
      (fun ω : ℕ → Step S => infl M ν w (ω n)) :=
  (((measurable_infl M ν hinv hR hrint hμ w).comp
    (MarkovChainCLT.measurable_coord_pathSigma hnj)) :
      Measurable[MarkovChainCLT.pathSigma (Step S) j] _).stronglyMeasurable

end Chain

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The martingale score system of the SST experiment**, given the covariance identity
between the estimator and the accumulated influence function. -/
theorem exists_martingale_score_of_score_covariance
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (δ : (T : ℕ) → (Fin T → Step S) → S → ℝ)
    (hscore : ∀ (w : S → ℝ) (T : ℕ), 1 ≤ T →
      ∫ ω, (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
            * (∑ i ∈ Finset.range (T + 1),
                ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
                  (estObs M .IS (ω i)))
          ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
        = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s') :
    ∀ w : S → ℝ, ∃ (V : ℕ → (ℕ → Step S) → ℝ) (c : (ℕ → Step S) → ℝ),
      (∀ j, MemLp (V j) 2 (MarkovChainCLT.chainMeasure (expKernel M) ν)) ∧
      (∀ j, StronglyMeasurable[MeasurableSpace.comap
          (Preorder.frestrictLe (π := fun _ : ℕ => Step S) (j + 1)) inferInstance] (V j)) ∧
      (∀ j, (MarkovChainCLT.chainMeasure (expKernel M) ν)[V j | MeasurableSpace.comap
            (Preorder.frestrictLe (π := fun _ : ℕ => Step S) j) inferInstance]
          =ᵐ[MarkovChainCLT.chainMeasure (expKernel M) ν] 0) ∧
      (∀ j, ∫ ω, (V j ω) ^ 2 ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
          = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s') ∧
      MemLp c 2 (MarkovChainCLT.chainMeasure (expKernel M) ν) ∧
      StronglyMeasurable[MeasurableSpace.comap
        (Preorder.frestrictLe (π := fun _ : ℕ => Step S) 0) inferInstance] c ∧
      ∫ ω, c ω ∂(MarkovChainCLT.chainMeasure (expKernel M) ν) = 0 ∧
      (∀ T : ℕ, 1 ≤ T →
        ∫ ω, (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
              * ((∑ j ∈ Finset.range T, V j ω) + c ω)
            ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
          = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s') := by
  have hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y) :=
    fun x y => integrable_reward_of_gaussian M m v hgauss x y
  have hR2 : ∀ t a, MemLp (fun r : ℝ => r) 2 (M.reward t a) :=
    fun t a => memLp_reward_of_gaussian M m v hgauss t a
  have hrint := integrable_rwd_of_invariant M ν hinv hR
  have hr2 := memLp_rwd_of_invariant M ν hinv hR2
  have hμ := visit_ne_zero_of_trans_pos M ν hinv hpos
  have hiter := integrable_rwd_iterKernel M hR
  intro w
  refine ⟨fun j ω => infl M ν w (ω (j + 1)), fun ω => infl M ν w (ω 0),
    fun j => memLp_coord_infl M ν hinv hR hrint hμ w hr2 (j + 1),
    fun j => stronglyMeasurable_coord_infl M ν hinv hR hrint hμ w (le_refl (j + 1)),
    fun j => condExp_coord_infl M ν hinv hR hrint hμ w j,
    fun j => integral_coord_infl_sq M ν hinv hR hrint hμ w hr2 hiter (j + 1),
    memLp_coord_infl M ν hinv hR hrint hμ w hr2 0,
    stronglyMeasurable_coord_infl M ν hinv hR hrint hμ w (le_refl 0),
    integral_coord_infl M ν hinv hR hrint hμ w 0, ?_⟩
  intro T hT
  have e : ∀ ω : ℕ → Step S,
      (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
          * ((∑ j ∈ Finset.range T, infl M ν w (ω (j + 1))) + infl M ν w (ω 0))
        = (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
          * (∑ i ∈ Finset.range (T + 1), infl M ν w (ω i)) := by
    intro ω
    rw [Finset.sum_range_succ']
  rw [integral_congr_ae (Filter.Eventually.of_forall e)]
  exact hscore w T hT

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The influence function lies in the tangent space of the SST family**: it is an
affine function of the reward, centred at the mean reward of the executed action, plus a
function of the realized transition that is centred under the true transition law. -/
theorem influence_tangent_decomposition (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ) :
    ∃ (α : S → Bool → ℝ) (β : S → Bool → S → ℝ),
      (∀ (s : S) (γ : Bool),
        ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0) ∧
      (∀ z : Step S, infl M ν w z
        = α (Step.state z) (M.act (Step.arm z) (Step.state z))
            * (Step.rwd z
              - ∫ x, x ∂(M.reward (Step.state z) (M.act (Step.arm z) (Step.state z))))
          + β (Step.state z) (M.act (Step.arm z) (Step.state z)) (Step.next z)) := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : Bool → S → ℝ, G = fun a i =>
      ∑ s, w s * (mbSystem M (meanObs M .IS ν) a)⁻¹ s i := ⟨_, rfl⟩
  obtain ⟨Ct, hCt⟩ : ∃ Ct : S → Bool → ℝ, Ct = fun s a =>
      if s = M.crucial then (if a then 2 * G true s else 0) else G true s := ⟨_, rfl⟩
  obtain ⟨Cf, hCf⟩ : ∃ Cf : S → Bool → ℝ, Cf = fun s a =>
      if s = M.crucial then (if a then 0 else 2 * G false s) else G false s := ⟨_, rfl⟩
  refine ⟨fun s a => Ct s a - Cf s a,
    fun s a j => (Ct s a - Cf s a) * (∫ x, x ∂(M.reward s a))
      + M.γdisc * (Ct s a * M.value true j - Cf s a * M.value false j)
      - (Ct s a * M.value true s - Cf s a * M.value false s), ?_, ?_⟩
  · intro s γ
    have hsum1 : ∑ j, (M.trans s (M.act γ s) j).toReal = 1 :=
      pmf_sum_toReal (M.trans s (M.act γ s))
    have hbel : ∀ b : Bool, M.act b s = M.act γ s →
        (∫ x, x ∂(M.reward s (M.act γ s)))
          + M.γdisc * (∑ j, (M.trans s (M.act γ s) j).toReal * M.value b j)
          - M.value b s = 0 := by
      intro b hb
      have h1 : ∀ j : S, (M.trans s (M.act γ s) j).toReal = M.polTrans b s j := by
        intro j; rw [Model.polTrans, Matrix.of_apply, hb]
      have h2 : (∫ x, x ∂(M.reward s (M.act γ s))) = M.polReward b s := by
        rw [Model.polReward, hb]
      rw [h2, Finset.sum_congr rfl (fun j _ => by rw [h1 j])]
      have hv := value_bellman_apply M b s
      linarith
    have hexpand : ∑ j, (M.trans s (M.act γ s) j).toReal *
          ((Ct s (M.act γ s) - Cf s (M.act γ s)) * (∫ x, x ∂(M.reward s (M.act γ s)))
            + M.γdisc * (Ct s (M.act γ s) * M.value true j
              - Cf s (M.act γ s) * M.value false j)
            - (Ct s (M.act γ s) * M.value true s - Cf s (M.act γ s) * M.value false s))
        = Ct s (M.act γ s) * ((∫ x, x ∂(M.reward s (M.act γ s)))
            + M.γdisc * (∑ j, (M.trans s (M.act γ s) j).toReal * M.value true j)
            - M.value true s)
          - Cf s (M.act γ s) * ((∫ x, x ∂(M.reward s (M.act γ s)))
            + M.γdisc * (∑ j, (M.trans s (M.act γ s) j).toReal * M.value false j)
            - M.value false s) := by
      have hterm : ∀ j : S, (M.trans s (M.act γ s) j).toReal *
          ((Ct s (M.act γ s) - Cf s (M.act γ s)) * (∫ x, x ∂(M.reward s (M.act γ s)))
            + M.γdisc * (Ct s (M.act γ s) * M.value true j
              - Cf s (M.act γ s) * M.value false j)
            - (Ct s (M.act γ s) * M.value true s - Cf s (M.act γ s) * M.value false s))
          = ((Ct s (M.act γ s) - Cf s (M.act γ s)) * (∫ x, x ∂(M.reward s (M.act γ s)))
              - (Ct s (M.act γ s) * M.value true s - Cf s (M.act γ s) * M.value false s))
            * (M.trans s (M.act γ s) j).toReal
            + (M.γdisc * Ct s (M.act γ s))
              * ((M.trans s (M.act γ s) j).toReal * M.value true j)
            - (M.γdisc * Cf s (M.act γ s))
              * ((M.trans s (M.act γ s) j).toReal * M.value false j) := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum1]
      ring
    rw [hexpand]
    by_cases hs : s = M.crucial
    · cases γ
      · have hact : M.act false s = false := by simp [Model.act]
        have hct : Ct s (M.act false s) = 0 := by
          simp only [hCt, hact, if_pos hs]; simp
        have hcf : Cf s (M.act false s) = 2 * G false s := by
          simp only [hCf, hact, if_pos hs]; simp
        rw [hct, hcf, hbel false rfl]
        ring
      · have hact : M.act true s = true := by simp [Model.act, hs]
        have hct : Ct s (M.act true s) = 2 * G true s := by
          simp only [hCt, hact, if_pos hs]; simp
        have hcf : Cf s (M.act true s) = 0 := by
          simp only [hCf, hact, if_pos hs]; simp
        rw [hct, hcf, hbel true rfl]
        ring
    · have hactf : M.act false s = M.act γ s := by simp [Model.act, hs]
      have hactt : M.act true s = M.act γ s := by simp [Model.act, hs]
      rw [hbel true hactt, hbel false hactf]
      ring
  · intro z
    simp only [infl, influence_eq M ν hinv hR hrint hμ]
    have hsub : ∀ (T1 T2 : S → ℝ), ∑ s, w s * (T1 s - T2 s)
        = (∑ s, w s * T1 s) - (∑ s, w s * T2 s) := by
      intro T1 T2
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hsub]
    have hfac : ∀ (a : Bool) (Y : ℝ),
        ∑ s, w s * ((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state z) * Y)
          = G a (Step.state z) * Y := by
      intro a Y
      rw [hG]
      simp only
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hfac true, hfac false]
    have hWt : G true (Step.state z) * schemeWeight M .IS true z
        = Ct (Step.state z) (M.act (Step.arm z) (Step.state z)) := by
      rw [hCt]
      simp only
      by_cases hs : Step.state z = M.crucial
      · rw [if_pos hs]
        have : M.act (Step.arm z) (Step.state z) = Step.arm z := by simp [Model.act, hs]
        rw [this]
        show G true (Step.state z) *
          (if Step.state z = M.crucial then
            2 * (if Step.arm z = true then (1 : ℝ) else 0) else 1) = _
        rw [if_pos hs]
        cases Step.arm z <;> simp <;> ring
      · rw [if_neg hs]
        show G true (Step.state z) *
          (if Step.state z = M.crucial then
            2 * (if Step.arm z = true then (1 : ℝ) else 0) else 1) = _
        rw [if_neg hs, mul_one]
    have hWf : G false (Step.state z) * schemeWeight M .IS false z
        = Cf (Step.state z) (M.act (Step.arm z) (Step.state z)) := by
      rw [hCf]
      simp only
      by_cases hs : Step.state z = M.crucial
      · rw [if_pos hs]
        have : M.act (Step.arm z) (Step.state z) = Step.arm z := by simp [Model.act, hs]
        rw [this]
        show G false (Step.state z) *
          (if Step.state z = M.crucial then
            2 * (if Step.arm z = false then (1 : ℝ) else 0) else 1) = _
        rw [if_pos hs]
        cases Step.arm z <;> simp <;> ring
      · rw [if_neg hs]
        show G false (Step.state z) *
          (if Step.state z = M.crucial then
            2 * (if Step.arm z = false then (1 : ℝ) else 0) else 1) = _
        rw [if_neg hs, mul_one]
    rw [← mul_assoc, ← mul_assoc, hWt, hWf]
    ring

end TreatmentLocality

end

-- === tl_ident.lean ===
section



open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The stationary visit probability of a state. -/
noncomputable def visit (ν : Measure (Step S)) (i : S) : ℝ :=
  ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν

/-- Integrating a function of the current state against the stationary law. -/
lemma integral_state_fun (ν : Measure (Step S)) [IsProbabilityMeasure ν] (g : S → ℝ) :
    ∫ z, g (Step.state z) ∂ν = ∑ i, visit ν i * g i := by
  classical
  have hsplit : ∀ z : Step S, g (Step.state z)
      = ∑ i, (if Step.state z = i then (1 : ℝ) else 0) * g i := by
    intro z
    rw [Finset.sum_eq_single (Step.state z) (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have hmeas : ∀ i : S, Measurable (fun z : Step S =>
      (if Step.state z = i then (1 : ℝ) else 0) * g i) :=
    fun i => (Measurable.ite (measurable_fst (measurableSet_singleton i))
      measurable_const measurable_const).mul_const _
  have hint : ∀ i : S, Integrable (fun z : Step S =>
      (if Step.state z = i then (1 : ℝ) else 0) * g i) ν := by
    intro i
    refine integrable_of_bdd ν (hmeas i) (C := |g i|) (fun z => ?_)
    rw [abs_mul]
    have : |if Step.state z = i then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    calc |if Step.state z = i then (1 : ℝ) else 0| * |g i| ≤ 1 * |g i| :=
          mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = |g i| := one_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_finsetSum (μ := ν) (f := fun (i : S) (z : Step S) =>
      (if Step.state z = i then (1 : ℝ) else 0) * g i) _ (fun i _ => hint i)]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const, visit]

/-- The inverse of the Bellman system, reweighted by the visit probabilities, is the
inverse of the plug-in system at the population point. -/
lemma inv_bellman_eq (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (hμ : ∀ i, visit ν i ≠ 0) (a : Bool) :
    ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹
      = (mbSystem M (meanObs M .IS ν) a)⁻¹ * Matrix.diagonal (visit ν) := by
  have hN : ∀ i, ∑ k, ((meanObs M .IS ν) a).1 i k ≠ 0 := by
    intro i
    rw [meanObs_IS_visit M ν hinv a i]
    exact hμ i
  have hvis : (fun i => ∑ k, ((meanObs M .IS ν) a).1 i k) = visit ν := by
    funext i; rw [meanObs_IS_visit M ν hinv a i, visit]
  have hfac : mbSystem M (meanObs M .IS ν) a
      = Matrix.diagonal (visit ν) * ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a) := by
    rw [mbSystem_eq_diagonal_mul M _ a hN, mbTrans_meanObs_IS M ν hinv hμ a, hvis]
  have hDunit : IsUnit (Matrix.diagonal (visit ν)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hμ i)
  have hDinv : (Matrix.diagonal (visit ν))⁻¹ = Matrix.diagonal (fun i => (visit ν i)⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal,
      show (fun i => visit ν i * (visit ν i)⁻¹) = (fun _ : S => (1 : ℝ)) from
        funext fun i => mul_inv_cancel₀ (hμ i)]
    exact Matrix.diagonal_one
  rw [hfac, Matrix.mul_inv_rev, hDinv, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
    show (fun i => (visit ν i)⁻¹ * visit ν i) = (fun _ : S => (1 : ℝ)) from
      funext fun i => inv_mul_cancel₀ (hμ i), Matrix.diagonal_one, Matrix.mul_one]

/-- The `w`-weighted solution of the Bellman system, in terms of the plug-in system. -/
lemma weighted_inv_mulVec (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (hμ : ∀ i, visit ν i ≠ 0) (a : Bool)
    (w : S → ℝ) (x : S → ℝ) :
    ∑ s, w s * ((((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹).mulVec x s)
      = ∑ i, visit ν i * (∑ s, w s * (mbSystem M (meanObs M .IS ν) a)⁻¹ s i) * x i := by
  have hentry : ∀ s i : S, (((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹) s i
      = (mbSystem M (meanObs M .IS ν) a)⁻¹ s i * visit ν i := by
    intro s i
    rw [inv_bellman_eq M ν hinv hμ a, Matrix.mul_apply,
      Finset.sum_eq_single i (fun b _ hb => by
        simp [Matrix.diagonal_apply_ne _ hb]) (fun h => absurd (Finset.mem_univ i) h),
      Matrix.diagonal_apply_eq]
  simp only [Matrix.mulVec, dotProduct]
  have hL : ∀ s : S,
      w s * (∑ j, (((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹) s j * x j)
        = ∑ j, (w s * (mbSystem M (meanObs M .IS ν) a)⁻¹ s j) * (visit ν j * x j) := by
    intro s
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hentry s j]; ring
  rw [Finset.sum_congr rfl (fun s _ => hL s), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  ring

end TreatmentLocality

end

-- === tl_affine.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma visit_eq_map_real (ν : Measure (Step S)) [IsProbabilityMeasure ν] (i : S) :
    visit ν i = (Measure.map Step.state ν).real {i} := by
  have hset : MeasurableSet {z : Step S | Step.state z = i} :=
    measurable_fst (measurableSet_singleton i)
  have h1 : (fun z : Step S => (if Step.state z = i then (1 : ℝ) else 0))
      = Set.indicator {z : Step S | Step.state z = i} 1 := by
    funext z
    by_cases h : Step.state z = i <;> simp [Set.indicator, h]
  rw [visit, h1, integral_indicator_one hset]
  rw [Measure.real, Measure.real,
    Measure.map_apply (f := Step.state) measurable_fst (measurableSet_singleton i)]
  rfl

/-- The velocity of the population statistics along the perturbation. -/
noncomputable def scoreStat (M : Model S) (v : S → Bool → ℝ≥0) (α : S → Bool → ℝ)
    (β : S → Bool → S → ℝ) (ν : Measure (Step S)) : EstInput S :=
  fun a => (fun i j => visit ν i * dTrans M β a i j,
    fun i => visit ν i * dReward M v α a i)

/-- **The population statistics move affinely along the perturbation.** -/
theorem meanObs_perturbModel (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    {t : ℝ} (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) :
    meanObs M .IS (obsLaw (perturbModel M m v α β t) (Measure.map Step.state ν))
      = meanObs M .IS ν + t • scoreStat M v α β ν := by
  have hobs : obsLaw M (Measure.map Step.state ν) = ν := obsLaw_map_state M ν hinv
  haveI : IsProbabilityMeasure (Measure.map Step.state ν) :=
    Measure.isProbabilityMeasure_map (f := Step.state) measurable_fst.aemeasurable
  set μ : Measure S := Measure.map Step.state ν with hμdef
  funext a
  have hc : (perturbModel M m v α β t).crucial = M.crucial := rfl
  refine Prod.ext ?_ ?_
  · funext i j
    have hL : (meanObs M .IS (obsLaw (perturbModel M m v α β t) μ) a).1 i j
        = μ.real {i} * (perturbModel M m v α β t).polTrans a i j := by
      rw [meanObs_congr_crucial M (perturbModel M m v α β t) hc]
      exact meanObs_obsLaw_trans (perturbModel M m v α β t) μ a i j
    have hR : (meanObs M .IS ν a).1 i j = μ.real {i} * M.polTrans a i j := by
      rw [← hobs]
      exact meanObs_obsLaw_trans M μ a i j
    rw [hL, perturbModel_polTrans M m v α β hcent ht a]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    show μ.real {i} * (M.polTrans a i j + t * dTrans M β a i j)
      = (meanObs M .IS ν a).1 i j + t * (visit ν i * dTrans M β a i j)
    rw [hR, visit_eq_map_real ν i]
    ring
  · funext i
    have hL : (meanObs M .IS (obsLaw (perturbModel M m v α β t) μ) a).2 i
        = μ.real {i} * (perturbModel M m v α β t).polReward a i := by
      rw [meanObs_congr_crucial M (perturbModel M m v α β t) hc]
      refine meanObs_obsLaw_rwd (perturbModel M m v α β t) μ ?_ a i
      intro x y
      rw [show (perturbModel M m v α β t).reward x y
        = gaussianReal (m x y + t * α x y * (v x y : ℝ)) (v x y) from rfl]
      exact (memLp_id_gaussianReal 1).integrable le_rfl
    have hR : (meanObs M .IS ν a).2 i = μ.real {i} * M.polReward a i := by
      rw [← hobs]
      refine meanObs_obsLaw_rwd M μ ?_ a i
      intro x y
      rw [hgauss x y]
      exact (memLp_id_gaussianReal 1).integrable le_rfl
    rw [hL, perturbModel_polReward M m v α β t a i]
    show μ.real {i} * (m i (M.act a i) + t * dReward M v α a i)
      = (meanObs M .IS ν a).2 i + t * (visit ν i * dReward M v α a i)
    rw [hR, polReward_zero M m v hgauss a i, visit_eq_map_real ν i]
    ring

end TreatmentLocality

end

-- === tl_scorecoord.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The expectation of an observable under the perturbed observation law is its
likelihood-ratio-weighted expectation under the true one. -/
theorem integral_obsLaw_perturbModel (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    {t : ℝ} (ht : |t| < envEps β) (c : Step S → ℝ) :
    ∫ z, c z ∂(obsLaw (perturbModel M m v α β t) (Measure.map Step.state ν))
      = ∫ z, c z * pertDens M m v α β t z ∂ν := by
  haveI : IsProbabilityMeasure (Measure.map Step.state ν) :=
    Measure.isProbabilityMeasure_map (f := Step.state) measurable_fst.aemeasurable
  rw [obsLaw_perturbModel M m v α β t hgauss hcent
    (fun s a j => one_add_t_beta_nonneg β ht s a j) (Measure.map Step.state ν),
    obsLaw_map_state M ν hinv,
    integral_withDensity_eq_integral_toReal_smul (measurable_pertDens M m v α β t)
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (ENNReal.ofReal (pertDens M m v α β t z)).toReal • c z
      = c z * pertDens M m v α β t z
  rw [smul_eq_mul, ENNReal.toReal_ofReal (pertDens_nonneg M m v α β ht z)]
  ring

/-- Identifying a score covariance from the affine motion of a statistic. -/
theorem integral_pertDeriv_of_affine (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (c : Step S → ℝ) (hc : Measurable c) (K : ℝ) (hK0 : 0 ≤ K)
    (hcbd : ∀ z, |c z| ≤ K * (1 + |Step.rwd z|)) (c₀ H : ℝ)
    (haff : ∀ t : ℝ, |t| < envEps β →
      ∫ z, c z * pertDens M m v α β t z ∂ν = c₀ + t * H) :
    ∫ z, c z * pertDeriv M m v α β 0 z ∂ν = H := by
  have h1 := hasDerivAt_integral_pertDens M m v hgauss α β ν hinv c hc K hK0 hcbd
  have h2 : HasDerivAt (fun t : ℝ => c₀ + t * H) H 0 := by
    have h := ((hasDerivAt_id' (x := (0:ℝ))).mul_const H).const_add c₀
    rw [one_mul] at h
    exact h
  have heq : (fun t : ℝ => c₀ + t * H)
      =ᶠ[nhds 0] fun t : ℝ => ∫ z, c z * pertDens M m v α β t z ∂ν := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (envEps_pos β)] with t ht
    exact (haff t (by simpa [Real.dist_eq] using ht)).symm
  exact (h1.congr_of_eventuallyEq heq).unique h2

section Coords

variable (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
  (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
  (hcent : ∀ (s : S) (γ : Bool),
    ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
  (ν : Measure (Step S)) [IsProbabilityMeasure ν]
  (hinv : Kernel.Invariant (expKernel M) ν)

include hgauss hcent hinv

/-- **The score covariance of the transition statistic.** -/
theorem integral_estObs_pertDeriv_trans (a : Bool) (i j : S) :
    ∫ z, (estObs M .IS z a).1 i j * pertDeriv M m v α β 0 z ∂ν
      = (scoreStat M v α β ν a).1 i j := by
  classical
  have hcm : Measurable (fun z : Step S => (estObs M .IS z a).1 i j) := by
    have h1 : (fun z : Step S => (estObs M .IS z a).1 i j)
        = fun z : Step S => schemeWeight M .IS a z
          * (if Step.state z = i ∧ Step.next z = j then (1:ℝ) else 0) := rfl
    rw [h1]
    refine (measurable_schemeWeight M a).mul ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurable_fst (measurableSet_singleton i)).inter
      (((measurable_fst.comp measurable_snd).comp measurable_snd)
        (measurableSet_singleton j))
  have hcbd : ∀ z : Step S, |(estObs M .IS z a).1 i j| ≤ 2 * (1 + |Step.rwd z|) := by
    intro z
    have h1 : (estObs M .IS z a).1 i j = schemeWeight M .IS a z
        * (if Step.state z = i ∧ Step.next z = j then (1:ℝ) else 0) := rfl
    rw [h1, abs_mul]
    have hw := schemeWeight_IS_abs_le M a z
    have hi : |if Step.state z = i ∧ Step.next z = j then (1:ℝ) else 0| ≤ 1 := by
      split_ifs <;> norm_num
    have hr : (0:ℝ) ≤ |Step.rwd z| := abs_nonneg _
    nlinarith [abs_nonneg (schemeWeight M .IS a z)]
  refine integral_pertDeriv_of_affine M m v hgauss α β ν hinv _ hcm 2 (by norm_num) hcbd
    ((meanObs M .IS ν a).1 i j) _ ?_
  intro t ht
  rw [← integral_obsLaw_perturbModel M m v hgauss α β hcent ν hinv ht
    (fun z => (estObs M .IS z a).1 i j)]
  show (meanObs M .IS (obsLaw (perturbModel M m v α β t) (Measure.map Step.state ν)) a).1 i j
    = (meanObs M .IS ν a).1 i j + t * (scoreStat M v α β ν a).1 i j
  rw [meanObs_perturbModel M m v hgauss α β hcent ν hinv
    (fun s b k => one_add_t_beta_nonneg β ht s b k)]
  simp [Pi.add_apply, Pi.smul_apply]

/-- **The score covariance of the reward statistic.** -/
theorem integral_estObs_pertDeriv_rwd (a : Bool) (i : S) :
    ∫ z, (estObs M .IS z a).2 i * pertDeriv M m v α β 0 z ∂ν
      = (scoreStat M v α β ν a).2 i := by
  classical
  have hcm : Measurable (fun z : Step S => (estObs M .IS z a).2 i) := by
    have h1 : (fun z : Step S => (estObs M .IS z a).2 i)
        = fun z : Step S => schemeWeight M .IS a z
          * (if Step.state z = i then Step.rwd z else 0) := rfl
    rw [h1]
    refine (measurable_schemeWeight M a).mul ?_
    exact Measurable.ite (measurable_fst (measurableSet_singleton i))
      measurable_rwd measurable_const
  have hcbd : ∀ z : Step S, |(estObs M .IS z a).2 i| ≤ 2 * (1 + |Step.rwd z|) := by
    intro z
    have h1 : (estObs M .IS z a).2 i = schemeWeight M .IS a z
        * (if Step.state z = i then Step.rwd z else 0) := rfl
    rw [h1, abs_mul]
    have hw := schemeWeight_IS_abs_le M a z
    have hi : |if Step.state z = i then Step.rwd z else 0| ≤ |Step.rwd z| := by
      split_ifs with h
      · exact le_rfl
      · simp
    have hr : (0:ℝ) ≤ |Step.rwd z| := abs_nonneg _
    nlinarith [abs_nonneg (schemeWeight M .IS a z),
      abs_nonneg (if Step.state z = i then Step.rwd z else 0)]
  refine integral_pertDeriv_of_affine M m v hgauss α β ν hinv _ hcm 2 (by norm_num) hcbd
    ((meanObs M .IS ν a).2 i) _ ?_
  intro t ht
  rw [← integral_obsLaw_perturbModel M m v hgauss α β hcent ν hinv ht
    (fun z => (estObs M .IS z a).2 i)]
  show (meanObs M .IS (obsLaw (perturbModel M m v α β t) (Measure.map Step.state ν)) a).2 i
    = (meanObs M .IS ν a).2 i + t * (scoreStat M v α β ν a).2 i
  rw [meanObs_perturbModel M m v hgauss α β hcent ν hinv
    (fun s b k => one_add_t_beta_nonneg β ht s b k)]
  simp [Pi.add_apply, Pi.smul_apply]

end Coords

end TreatmentLocality

end

-- === tl_lin.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

section Lin

variable (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
  (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
  (hcent : ∀ (s : S) (γ : Bool),
    ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
  (ν : Measure (Step S)) [IsProbabilityMeasure ν]
  (hinv : Kernel.Invariant (expKernel M) ν)

include hgauss hcent hinv

/-- A flat listing of the coordinates of a statistics vector. -/
def flat (h : EstInput S) (a : Bool) : S ⊕ S × S → ℝ
  | .inl i => (h a).2 i
  | .inr (i, j) => (h a).1 i j

/-- The coordinates of the raw statistic, indexed by a flat index. -/
private noncomputable def rawCoord (a : Bool) : S ⊕ S × S → Step S → ℝ
  | .inl i => fun z => (estObs M .IS z a).2 i
  | .inr (i, j) => fun z => (estObs M .IS z a).1 i j

omit hgauss hcent hinv in
private lemma rawCoord_meas (a : Bool) (p : S ⊕ S × S) : Measurable (rawCoord M a p) := by
  classical
  cases p with
  | inl i =>
      have h1 : rawCoord M a (.inl i)
          = fun z : Step S => schemeWeight M .IS a z
            * (if Step.state z = i then Step.rwd z else 0) := rfl
      rw [h1]
      exact (measurable_schemeWeight M a).mul
        (Measurable.ite (measurable_fst (measurableSet_singleton i))
          measurable_rwd measurable_const)
  | inr q =>
      obtain ⟨i, j⟩ := q
      have h1 : rawCoord M a (.inr (i, j))
          = fun z : Step S => schemeWeight M .IS a z
            * (if Step.state z = i ∧ Step.next z = j then (1:ℝ) else 0) := rfl
      rw [h1]
      refine (measurable_schemeWeight M a).mul ?_
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (measurable_fst (measurableSet_singleton i)).inter
        (((measurable_fst.comp measurable_snd).comp measurable_snd)
          (measurableSet_singleton j))

omit hgauss hcent hinv in
private lemma rawCoord_bd (a : Bool) (p : S ⊕ S × S) (z : Step S) :
    |rawCoord M a p z| ≤ 2 * (1 + |Step.rwd z|) := by
  classical
  have hw := schemeWeight_IS_abs_le M a z
  have hw0 : (0:ℝ) ≤ |schemeWeight M .IS a z| := abs_nonneg _
  have hr : (0:ℝ) ≤ |Step.rwd z| := abs_nonneg _
  cases p with
  | inl i =>
      have h1 : rawCoord M a (.inl i) z = schemeWeight M .IS a z
          * (if Step.state z = i then Step.rwd z else 0) := rfl
      rw [h1, abs_mul]
      have hi : |if Step.state z = i then Step.rwd z else 0| ≤ |Step.rwd z| := by
        split_ifs with h
        · exact le_rfl
        · simp
      nlinarith [abs_nonneg (if Step.state z = i then Step.rwd z else 0)]
  | inr q =>
      obtain ⟨i, j⟩ := q
      have h1 : rawCoord M a (.inr (i, j)) z = schemeWeight M .IS a z
          * (if Step.state z = i ∧ Step.next z = j then (1:ℝ) else 0) := rfl
      rw [h1, abs_mul]
      have hi : |if Step.state z = i ∧ Step.next z = j then (1:ℝ) else 0| ≤ 1 := by
        split_ifs <;> norm_num
      nlinarith

/-- The score covariance of any flat coordinate. -/
private lemma integral_rawCoord (a : Bool) (p : S ⊕ S × S) :
    ∫ z, rawCoord M a p z * pertDeriv M m v α β 0 z ∂ν
      = flat (scoreStat M v α β ν) a p := by
  classical
  cases p with
  | inl i => exact integral_estObs_pertDeriv_rwd M m v hgauss α β hcent ν hinv a i
  | inr q =>
      obtain ⟨i, j⟩ := q
      exact integral_estObs_pertDeriv_trans M m v hgauss α β hcent ν hinv a i j

/-- Linearity of the integral in the flat coordinates. -/
private lemma integral_lincomb (a : Bool) (κ : S ⊕ S × S → ℝ) :
    ∫ z, (∑ p, κ p * rawCoord M a p z) * pertDeriv M m v α β 0 z ∂ν
      = ∑ p, κ p * flat (scoreStat M v α β ν) a p := by
  have hint : ∀ p : S ⊕ S × S,
      Integrable (fun z => rawCoord M a p z * pertDeriv M m v α β 0 z) ν := fun p =>
    integrable_mul_pertDeriv M m v hgauss α β ν hinv _ (rawCoord_meas M a p) 2
      (by norm_num) (rawCoord_bd M a p)
  have hexp : ∀ z : Step S, (∑ p, κ p * rawCoord M a p z) * pertDeriv M m v α β 0 z
      = ∑ p, κ p * (rawCoord M a p z * pertDeriv M m v α β 0 z) := by
    intro z
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_finsetSum _ (fun p _ => (hint p).const_mul _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul, integral_rawCoord M m v hgauss α β hcent ν hinv a p]

omit hgauss hcent hinv in
private lemma sum_flat_eq (a : Bool) (h : EstInput S) (B : Matrix S S ℝ) (w : S → S → ℝ)
    (s : S) :
    (B.mulVec (fun i => (h a).2 i + ∑ j, (h a).1 i j * w i j)) s
      = ∑ p : S ⊕ S × S, (Sum.elim (fun i => B s i)
          (fun q : S × S => B s q.1 * w q.1 q.2) p) * flat h a p := by
  classical
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : S, (Sum.elim (fun i => B s i)
      (fun q : S × S => B s q.1 * w q.1 q.2) (Sum.inl i)) * flat h a (Sum.inl i)
      = ∑ i : S, B s i * (h a).2 i := rfl
  have h2 : ∑ q : S × S, (Sum.elim (fun i => B s i)
      (fun q : S × S => B s q.1 * w q.1 q.2) (Sum.inr q)) * flat h a (Sum.inr q)
      = ∑ i : S, ∑ j : S, (B s i * w i j) * (h a).1 i j := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [h1, h2, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_add]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit hgauss hcent hinv in
private lemma rawCoord_eq_flat (a : Bool) (p : S ⊕ S × S) (z : Step S) :
    rawCoord M a p z = flat (estObs M .IS z) a p := by
  cases p with
  | inl i => rfl
  | inr q => obtain ⟨i, j⟩ := q; rfl

/-- **The influence function against the score.**  Linearity of the plug-in gradient turns
the score covariance of the raw statistics into the score covariance of the influence
function. -/
theorem integral_influence_pertDeriv
    (hN : ∀ a i, ∑ k, (meanObs M .IS ν a).1 i k ≠ 0)
    (hB : ∀ a, IsUnit (mbSystem M (meanObs M .IS ν) a)) (s : S) :
    ∫ z, (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * pertDeriv M m v α β 0 z ∂ν
      = fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
          (scoreStat M v α β ν) := by
  classical
  obtain ⟨κ, hκ⟩ : ∃ κ : Bool → (S ⊕ S × S) → ℝ, κ = fun a => Sum.elim
      (fun i => (mbSystem M (meanObs M .IS ν) a)⁻¹ s i)
      (fun q : S × S => (mbSystem M (meanObs M .IS ν) a)⁻¹ s q.1
        * (M.γdisc * mbValue M (meanObs M .IS ν) a q.2
          - mbValue M (meanObs M .IS ν) a q.1)) := ⟨_, rfl⟩
  have hterm : ∀ (a : Bool) (h : EstInput S),
      ((mbSystem M (meanObs M .IS ν) a)⁻¹.mulVec (fun i => (h a).2 i + ∑ j, (h a).1 i j *
          (M.γdisc * mbValue M (meanObs M .IS ν) a j
            - mbValue M (meanObs M .IS ν) a i))) s
        = ∑ p, κ a p * flat h a p := by
    intro a h
    rw [hκ]
    exact sum_flat_eq a h ((mbSystem M (meanObs M .IS ν) a)⁻¹)
      (fun i j => M.γdisc * mbValue M (meanObs M .IS ν) a j
        - mbValue M (meanObs M .IS ν) a i) s
  have hexp : ∀ z : Step S,
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
          * pertDeriv M m v α β 0 z
        = ((∑ p, κ true p * rawCoord M true p z) * pertDeriv M m v α β 0 z)
          - ((∑ p, κ false p * rawCoord M false p z) * pertDeriv M m v α β 0 z) := by
    intro z
    rw [fderiv_mbATE_apply M (meanObs M .IS ν) hN hB s (estObs M .IS z),
      hterm true (estObs M .IS z), hterm false (estObs M .IS z)]
    simp only [← rawCoord_eq_flat M]
    ring
  have hintp : ∀ (a : Bool) (p : S ⊕ S × S),
      Integrable (fun z => rawCoord M a p z * pertDeriv M m v α β 0 z) ν := fun a p =>
    integrable_mul_pertDeriv M m v hgauss α β ν hinv _ (rawCoord_meas M a p) 2
      (by norm_num) (rawCoord_bd M a p)
  have hint : ∀ a : Bool, Integrable
      (fun z => (∑ p, κ a p * rawCoord M a p z) * pertDeriv M m v α β 0 z) ν := by
    intro a
    have heq : (fun z => (∑ p, κ a p * rawCoord M a p z) * pertDeriv M m v α β 0 z)
        = fun z => ∑ p, κ a p * (rawCoord M a p z * pertDeriv M m v α β 0 z) := by
      funext z
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [heq]
    exact integrable_finset_sum _ (fun p _ => (hintp a p).const_mul _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_sub (hint true) (hint false),
    integral_lincomb M m v hgauss α β hcent ν hinv true (κ true),
    integral_lincomb M m v hgauss α β hcent ν hinv false (κ false),
    fderiv_mbATE_apply M (meanObs M .IS ν) hN hB s (scoreStat M v α β ν),
    hterm true (scoreStat M v α β ν), hterm false (scoreStat M v α β ν)]

end Lin

end TreatmentLocality

end

-- === tl_ate.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The plug-in estimator is differentiable at any statistics vector with invertible
Bellman systems. -/
theorem differentiableAt_mbATE (M : Model S) (v : EstInput S)
    (hN : ∀ a i, ∑ k, (v a).1 i k ≠ 0) (hB : ∀ a, IsUnit (mbSystem M v a)) (s : S) :
    DifferentiableAt ℝ (fun u : EstInput S => mbATE M u s) v := by
  have ht := hasFDerivAt_mbValue M v true (hN true) (hB true) s
  have hf := hasFDerivAt_mbValue M v false (hN false) (hB false) s
  have hsub : HasFDerivAt (fun u : EstInput S => mbATE M u s)
      ((∑ i : S, gradPiece M v true s i) - (∑ i : S, gradPiece M v false s i)) v := by
    refine (ht.sub hf).congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    exact congrFun (mbATE_eq_mbValue M u) s
  exact hsub.differentiableAt

/-- **The derivative of the true ATE along the perturbation.** -/
theorem hasDerivAt_ate_perturbModel (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S) :
    HasDerivAt (fun t => (perturbModel M m v α β t).ate s)
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
        (scoreStat M v α β ν)) 0 := by
  classical
  haveI : IsProbabilityMeasure (Measure.map Step.state ν) :=
    Measure.isProbabilityMeasure_map (f := Step.state) measurable_fst.aemeasurable
  have hN : ∀ (a : Bool) (i : S), ∑ k, ((meanObs M .IS ν) a).1 i k ≠ 0 :=
    fun a i => meanObs_IS_visit_ne_zero M ν hinv hμ a i
  have hB : ∀ a : Bool, IsUnit (mbSystem M (meanObs M .IS ν) a) :=
    fun a => isUnit_mbSystem_meanObs_IS M ν hinv hμ a
  have hμ' : ∀ i : S, (Measure.map Step.state ν).real {i} ≠ 0 := by
    intro i
    rw [← visit_eq_map_real ν i]
    exact hμ i
  -- the affine curve in statistics space
  have hline : HasDerivAt
      (fun t : ℝ => meanObs M .IS ν + t • scoreStat M v α β ν) (scoreStat M v α β ν) 0 := by
    have h := (hasDerivAt_id' (x := (0:ℝ))).smul_const (scoreStat M v α β ν)
    rw [one_smul] at h
    exact h.const_add (meanObs M .IS ν)
  have hchain : HasDerivAt
      (fun t : ℝ => mbATE M (meanObs M .IS ν + t • scoreStat M v α β ν) s)
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
        (scoreStat M v α β ν)) 0 := by
    have hd := (differentiableAt_mbATE M (meanObs M .IS ν) hN hB s).hasFDerivAt
    have hpt : meanObs M .IS ν + (0:ℝ) • scoreStat M v α β ν = meanObs M .IS ν := by
      rw [zero_smul, add_zero]
    have hd2 : HasFDerivAt (fun u : EstInput S => mbATE M u s)
        (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν))
        (meanObs M .IS ν + (0:ℝ) • scoreStat M v α β ν) := by
      rw [hpt]; exact hd
    exact hd2.comp_hasDerivAt 0 hline
  refine hchain.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (envEps_pos β)] with t ht
  have htabs : |t| < envEps β := by simpa [Real.dist_eq] using ht
  have hR' : ∀ (x : S) (y : Bool),
      Integrable (fun r : ℝ => r) ((perturbModel M m v α β t).reward x y) := by
    intro x y
    rw [show (perturbModel M m v α β t).reward x y
      = gaussianReal (m x y + t * α x y * (v x y : ℝ)) (v x y) from rfl]
    exact (memLp_id_gaussianReal 1).integrable le_rfl
  have hfisher := mbATE_meanObs_obsLaw M (perturbModel M m v α β t) rfl rfl
    (Measure.map Step.state ν) hμ' hR'
  rw [← meanObs_perturbModel M m v hgauss α β hcent ν hinv
    (fun x b k => one_add_t_beta_nonneg β htabs x b k)]
  exact (congrFun hfisher s).symm

end TreatmentLocality

end

-- === pi_dens.lean ===
section

open MeasureTheory Measure
open scoped ENNReal

namespace Statistics

/-- **Tonelli for finite products**: the `ℝ≥0∞`-integral of a product of coordinatewise
functions over a product measure is the product of the integrals. -/
theorem lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmp := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
      have hg : Measurable (fun q : E 0 × ((j : Fin n) → E ((0 : Fin (n+1)).succAbove j)) =>
          f 0 q.1 * ∏ j, f ((0 : Fin (n+1)).succAbove j) (q.2 j)) := by
        refine Measurable.mul ((hf 0).comp measurable_fst) ?_
        exact Finset.measurable_prod _ fun j _ =>
          (hf _).comp ((measurable_pi_apply j).comp measurable_snd)
      have hcomp := hmp.lintegral_comp hg
      have heq : ∀ a : (j : Fin (n + 1)) → E j,
          f 0 ((MeasurableEquiv.piFinSuccAbove E 0) a).1 *
            ∏ j, f ((0 : Fin (n+1)).succAbove j) (((MeasurableEquiv.piFinSuccAbove E 0) a).2 j)
          = ∏ i, f i (a i) := by
        intro a
        rw [Fin.prod_univ_succAbove (fun i => f i (a i)) 0]
        rfl
      simp only [heq] at hcomp
      rw [hcomp]
      rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun j => μ ((0 : Fin (n+1)).succAbove j))
          (f := fun x => f 0 x) (g := fun h => ∏ j, f ((0 : Fin (n+1)).succAbove j) (h j))
          (hf 0).aemeasurable
          (Finset.measurable_prod _ fun j _ =>
            (hf _).comp (measurable_pi_apply j)).aemeasurable]
      rw [ih (fun j => hf ((0 : Fin (n+1)).succAbove j)),
        Fin.prod_univ_succAbove (fun i => ∫⁻ y, f i y ∂(μ i)) 0]

/-- **A product of densities is the density of the product**: forming a product measure
commutes with tilting each factor by a density. -/
theorem pi_withDensity {n : ℕ} {E : Type*} [MeasurableSpace E] (μ : Fin n → Measure E)
    [∀ i, SigmaFinite (μ i)] (g : Fin n → E → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hfin : ∀ i, SigmaFinite ((μ i).withDensity (g i))) :
    Measure.pi (fun i => (μ i).withDensity (g i))
      = (Measure.pi μ).withDensity (fun p => ∏ i, g i (p i)) := by
  haveI := hfin
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (g i)) fun s hs => ?_
  have hms : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hms, ← lintegral_indicator hms]
  have hind : ∀ p : Fin n → E, (Set.univ.pi s).indicator (fun p => ∏ i, g i (p i)) p
      = ∏ i, (s i).indicator (g i) (p i) := by
    intro p
    by_cases hp : p ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hp]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact (Set.indicator_of_mem (hp i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hp]
      simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at hp
      obtain ⟨i, hi⟩ := hp
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      exact Set.indicator_of_notMem hi _
  simp only [hind]
  rw [lintegral_fin_nat_prod (E := fun _ => E) (μ := μ) (f := fun i => (s i).indicator (g i))
    (fun i => (hg i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

section Deriv

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The product of a coordinatewise family of `L²` functions is `L²` for the product measure. -/
lemma memLp_two_pi_prod (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (Ψ : Ω → ℝ)
    (hΨmeas : Measurable Ψ) (hΨ : MemLp Ψ 2 μ) :
    MemLp (fun p : Fin T → Ω => ∏ i, Ψ (p i)) 2 (Measure.pi fun _ : Fin T => μ) := by
  have hsq : Integrable (fun x => Ψ x * Ψ x) μ := hΨ.integrable_mul hΨ
  have hprod : Integrable (fun p : Fin T → Ω => ∏ i, (Ψ (p i) * Ψ (p i)))
      (Measure.pi fun _ : Fin T => μ) :=
    Integrable.fintype_prod (f := fun _ : Fin T => fun x => Ψ x * Ψ x) (fun _ => hsq)
  have hmeasP : Measurable (fun p : Fin T → Ω => ∏ i, Ψ (p i)) :=
    Finset.measurable_prod _ fun i _ => hΨmeas.comp (measurable_pi_apply i)
  refine (memLp_two_iff_integrable_sq hmeasP.aestronglyMeasurable).2 (hprod.congr ?_)
  filter_upwards with p
  rw [sq, ← Finset.prod_mul_distrib]

/-- **Differentiation under the integral sign for an i.i.d. tilted family.**  If each
coordinate density `L t` is differentiable in `t` with derivative and value dominated by a
single `L²` envelope `Ψ ≥ 1`, then the expectation of `D` against the tilted product measure
is differentiable at `t = 0`, with the derivative given by the sum of the coordinatewise
scores. -/
theorem hasDerivAt_integral_pi_mul (μ : Measure Ω) [IsProbabilityMeasure μ] {T : ℕ}
    (L L' : ℝ → Ω → ℝ) (D : (Fin T → Ω) → ℝ) {ε : ℝ} (hε : 0 < ε) (Ψ : Ω → ℝ)
    (hL0 : ∀ x, L 0 x = 1)
    (hLmeas : ∀ t, Measurable (L t)) (hL'meas : Measurable (L' 0))
    (hDmeas : Measurable D)
    (hD : MemLp D 2 (Measure.pi fun _ : Fin T => μ))
    (hderiv : ∀ (x : Ω) (t : ℝ), |t| < ε → HasDerivAt (fun t => L t x) (L' t x) t)
    (hΨ1 : ∀ x, 1 ≤ Ψ x)
    (hLbound : ∀ (x : Ω) (t : ℝ), |t| < ε → |L t x| ≤ Ψ x)
    (hL'bound : ∀ (x : Ω) (t : ℝ), |t| < ε → |L' t x| ≤ Ψ x)
    (hΨmeas : Measurable Ψ) (hΨL2 : MemLp Ψ 2 μ) :
    HasDerivAt (fun t => ∫ p, D p * ∏ i, L t (p i) ∂(Measure.pi fun _ : Fin T => μ))
      (∫ p, D p * ∑ i : Fin T, L' 0 (p i) ∂(Measure.pi fun _ : Fin T => μ)) 0 := by
  classical
  set P : Measure (Fin T → Ω) := Measure.pi fun _ : Fin T => μ with hP
  set F : ℝ → (Fin T → Ω) → ℝ := fun t p => D p * ∏ i, L t (p i) with hF
  set F' : ℝ → (Fin T → Ω) → ℝ := fun t p =>
    D p * ∑ i : Fin T, (∏ j ∈ Finset.univ.erase i, L t (p j)) * L' t (p i) with hF'
  set bound : (Fin T → Ω) → ℝ := fun p => |D p| * ((T : ℝ) * ∏ j, Ψ (p j)) with hbound
  have hLmeasP : ∀ t : ℝ, Measurable (fun p : Fin T → Ω => ∏ i, L t (p i)) := fun t =>
    Finset.measurable_prod _ fun i _ => (hLmeas t).comp (measurable_pi_apply i)
  have hFmeas : ∀ t : ℝ, Measurable (F t) := fun t => hDmeas.mul (hLmeasP t)
  have hF'meas : Measurable (F' 0) := by
    refine hDmeas.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact (Finset.measurable_prod _ fun j _ => (hLmeas 0).comp (measurable_pi_apply j)).mul
      (hL'meas.comp (measurable_pi_apply i))
  have hF0 : F 0 = D := by
    funext p; simp [hF, hL0]
  have hΨprod : MemLp (fun p : Fin T → Ω => ∏ i, Ψ (p i)) 2 P :=
    memLp_two_pi_prod μ T Ψ hΨmeas hΨL2
  have hboundint : Integrable bound P := by
    have h1 : MemLp (fun p : Fin T → Ω => |D p|) 2 P := hD.abs
    have h2 : MemLp (fun p : Fin T → Ω => (T : ℝ) * ∏ i, Ψ (p i)) 2 P := hΨprod.const_mul _
    exact h1.integrable_mul h2
  have hballabs : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) ε → |t| < ε := by
    intro t ht
    simpa [Real.dist_eq] using ht
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (bound := bound) (s := Metric.ball (0:ℝ) ε) (Metric.ball_mem_nhds 0 hε)
    (Filter.Eventually.of_forall fun t => (hFmeas t).aestronglyMeasurable)
    (by rw [hF0]; exact hD.integrable one_le_two) hF'meas.aestronglyMeasurable
    ?hbnd hboundint ?hdiff
  · refine hkey.2.congr_deriv ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp [hF', hL0]
  case hbnd =>
    filter_upwards with p
    intro t ht
    have habs := hballabs t ht
    rw [Real.norm_eq_abs, hF', hbound]
    simp only [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |∑ i : Fin T, (∏ j ∈ Finset.univ.erase i, L t (p j)) * L' t (p i)|
        ≤ ∑ i : Fin T, |(∏ j ∈ Finset.univ.erase i, L t (p j)) * L' t (p i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin T, ∏ j, Ψ (p j) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have h1 : |∏ j ∈ Finset.univ.erase i, L t (p j)| ≤ ∏ j ∈ Finset.univ.erase i, Ψ (p j) := by
            rw [Finset.abs_prod]
            exact Finset.prod_le_prod (fun j _ => abs_nonneg _)
              (fun j _ => hLbound (p j) t habs)
          have h2 : |L' t (p i)| ≤ Ψ (p i) := hL'bound (p i) t habs
          have hnn : (0 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, Ψ (p j) :=
            Finset.prod_nonneg fun j _ => le_trans zero_le_one (hΨ1 (p j))
          calc |∏ j ∈ Finset.univ.erase i, L t (p j)| * |L' t (p i)|
              ≤ (∏ j ∈ Finset.univ.erase i, Ψ (p j)) * Ψ (p i) := by
                exact mul_le_mul h1 h2 (abs_nonneg _) hnn
            _ = ∏ j, Ψ (p j) := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
      _ = (T : ℝ) * ∏ j, Ψ (p j) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  case hdiff =>
    filter_upwards with p
    intro t ht
    have habs := hballabs t ht
    have hprod : HasDerivAt (fun u : ℝ => ∏ i : Fin T, L u (p i))
        (∑ i : Fin T, (∏ j ∈ Finset.univ.erase i, L t (p j)) • L' t (p i)) t :=
      HasDerivAt.fun_finsetProd (f := fun i u => L u (p i)) (f' := fun i => L' t (p i))
        (fun i _ => hderiv (p i) t habs)
    have := hprod.const_mul (D p)
    refine this.congr_deriv ?_
    simp [hF', smul_eq_mul, Finset.mul_sum]

end Deriv

end Statistics

end

-- === tl_leaf.lean ===
section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

section Sample

variable (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
  (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
  (hcent : ∀ (s : S) (γ : Bool),
    ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
  (ν : Measure (Step S)) [IsProbabilityMeasure ν]
  (hinv : Kernel.Invariant (expKernel M) ν)

include hgauss hcent hinv

/-- **The perturbed sample law is the true one tilted by the product likelihood ratio.** -/
theorem sampleLaw_perturbModel {t : ℝ} (ht : |t| < envEps β) (T : ℕ) :
    sampleLaw (perturbModel M m v α β t) (Measure.map Step.state ν) T
      = (Measure.pi fun _ : Fin T => ν).withDensity
          (fun p => ∏ i, ENNReal.ofReal (pertDens M m v α β t (p i))) := by
  haveI : IsProbabilityMeasure (Measure.map Step.state ν) :=
    Measure.isProbabilityMeasure_map (f := Step.state) measurable_fst.aemeasurable
  have hobs : obsLaw (perturbModel M m v α β t) (Measure.map Step.state ν)
      = ν.withDensity (fun z => ENNReal.ofReal (pertDens M m v α β t z)) := by
    rw [obsLaw_perturbModel M m v α β t hgauss hcent
      (fun s a j => one_add_t_beta_nonneg β ht s a j) (Measure.map Step.state ν),
      obsLaw_map_state M ν hinv]
  have hfin : ∀ _i : Fin T, SigmaFinite
      (ν.withDensity (fun z => ENNReal.ofReal (pertDens M m v α β t z))) := by
    intro _i
    rw [← hobs]
    infer_instance
  rw [sampleLaw]
  simp only [hobs]
  exact Statistics.pi_withDensity (fun _ : Fin T => ν)
    (fun _ : Fin T => fun z => ENNReal.ofReal (pertDens M m v α β t z))
    (fun _ => measurable_pertDens M m v α β t) hfin

/-- Expectations under the perturbed sample law are likelihood-ratio-weighted expectations
under the true one. -/
theorem integral_sampleLaw_perturbModel {t : ℝ} (ht : |t| < envEps β) (T : ℕ)
    (f : (Fin T → Step S) → ℝ) :
    ∫ p, f p ∂(sampleLaw (perturbModel M m v α β t) (Measure.map Step.state ν) T)
      = ∫ p, f p * ∏ i, pertDens M m v α β t (p i) ∂(Measure.pi fun _ : Fin T => ν) := by
  have hmeasP : Measurable
      (fun p : Fin T → Step S => ∏ i, ENNReal.ofReal (pertDens M m v α β t (p i))) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_pertDens M m v α β t).comp (measurable_pi_apply i)
  rw [sampleLaw_perturbModel M m v hgauss α β hcent ν hinv ht T,
    integral_withDensity_eq_integral_toReal_smul hmeasP
      (Filter.Eventually.of_forall fun p => ?_)]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show (∏ i, ENNReal.ofReal (pertDens M m v α β t (p i))).toReal • f p
      = f p * ∏ i, pertDens M m v α β t (p i)
    rw [smul_eq_mul, ENNReal.toReal_prod]
    have : ∀ i : Fin T, (ENNReal.ofReal (pertDens M m v α β t (p i))).toReal
        = pertDens M m v α β t (p i) := fun i =>
      ENNReal.toReal_ofReal (pertDens_nonneg M m v α β ht (p i))
    rw [Finset.prod_congr rfl fun i _ => this i]
    ring
  · exact ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top

/-- The likelihood ratio is square-integrable. -/
theorem memLp_pertDens {t : ℝ} (ht : |t| < envEps β) :
    MemLp (fun z : Step S => pertDens M m v α β t z) 2 ν := by
  have hmeas : Measurable (fun z : Step S => pertDens M m v α β t z) := by
    simp only [pertDens, Step.state, Step.arm, Step.next, Step.rwd]; fun_prop
  refine MemLp.of_le (memLp_envelope m v α β M hgauss ν hinv) hmeas.aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (le_trans zero_le_one (one_le_envelope m v α β z))]
  exact abs_pertDens_le_envelope M m v α β ht z

/-- The score is square-integrable. -/
theorem memLp_pertDeriv :
    MemLp (fun z : Step S => pertDeriv M m v α β 0 z) 2 ν := by
  have hz : |(0:ℝ)| < envEps β := by simpa using envEps_pos β
  have hmeas : Measurable (fun z : Step S => pertDeriv M m v α β 0 z) := by
    simp only [pertDeriv, dcoefA, dcoefB, dcoefC, Step.state, Step.arm, Step.next, Step.rwd]
    fun_prop
  refine MemLp.of_le (memLp_envelope m v α β M hgauss ν hinv) hmeas.aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (le_trans zero_le_one (one_le_envelope m v α β z))]
  exact abs_pertDeriv_le_envelope M m v α β hz z

/-- The product likelihood ratio over a sample is square-integrable. -/
theorem memLp_prod_pertDens {t : ℝ} (ht : |t| < envEps β) (T : ℕ) :
    MemLp (fun p : Fin T → Step S => ∏ i, pertDens M m v α β t (p i)) 2
      (Measure.pi fun _ : Fin T => ν) := by
  have hΨ : MemLp (fun p : Fin T → Step S => ∏ i, envelope m v α β (p i)) 2
      (Measure.pi fun _ : Fin T => ν) :=
    Statistics.memLp_two_pi_prod ν T (fun z => envelope m v α β z)
      (measurable_envelope m v α β) (memLp_envelope m v α β M hgauss ν hinv)
  have hmeas : Measurable (fun p : Fin T → Step S => ∏ i, pertDens M m v α β t (p i)) := by
    refine Finset.measurable_prod _ fun i _ => ?_
    have h : Measurable (fun z : Step S => pertDens M m v α β t z) := by
      simp only [pertDens, Step.state, Step.arm, Step.next, Step.rwd]; fun_prop
    exact h.comp (measurable_pi_apply i)
  refine MemLp.of_le hΨ hmeas.aestronglyMeasurable ?_
  filter_upwards with p
  have hnn : (0:ℝ) ≤ ∏ i, envelope m v α β (p i) :=
    Finset.prod_nonneg fun i _ => le_trans zero_le_one (one_le_envelope m v α β (p i))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _)
    (fun i _ => abs_pertDens_le_envelope M m v α β ht (p i))

end Sample

/-- **The influence function is the score of the SST family on an i.i.d. sample.**  For any
regular unbiased estimator of the average treatment effect, its covariance with the sum of
the per-observation influence functions is exactly the information-sharing asymptotic
variance in the direction `w`. -/
theorem influence_score_covariance_iid_aux
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (δ : (T : ℕ) → (Fin T → Step S) → S → ℝ)
    (hmeas : ∀ T s, Measurable (fun path => δ T path s))
    (hL2 : ∀ T s, MemLp (fun path => δ T path s) 2
      (sampleLaw M (Measure.map Step.state ν) T))
    (hunbiased : ∀ (M' : Model S), M'.crucial = M.crucial → M'.γdisc = M.γdisc →
      (∃ m' : S → Bool → ℝ, M'.GaussianRewards m' v) →
      ∀ T : ℕ, 1 ≤ T → ∀ s,
        ∫ path, δ T path s ∂(sampleLaw M' (Measure.map Step.state ν) T) = M'.ate s)
    (w : S → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∫ path, (∑ s, w s * δ T path s)
        * (∑ i : Fin T, ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s)
            (meanObs M .IS ν) (estObs M .IS (path i)))
        ∂(sampleLaw M (Measure.map Step.state ν) T)
      = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by
  classical
  haveI : IsProbabilityMeasure (Measure.map Step.state ν) :=
    Measure.isProbabilityMeasure_map (f := Step.state) measurable_fst.aemeasurable
  have hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y) :=
    integrable_reward_of_gaussian M m v hgauss
  have hR2 : ∀ x y, MemLp (fun r : ℝ => r) 2 (M.reward x y) :=
    memLp_reward_of_gaussian M m v hgauss
  have hrint := integrable_rwd_of_invariant M ν hinv hR
  have hr2 := memLp_rwd_of_invariant M ν hinv hR2
  have hiter := integrable_rwd_iterKernel M hR
  have hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0 :=
    fun i => visit_ne_zero_of_trans_pos M ν hinv hpos i
  have hN : ∀ (a : Bool) (i : S), ∑ k, ((meanObs M .IS ν) a).1 i k ≠ 0 :=
    fun a i => meanObs_IS_visit_ne_zero M ν hinv hμ a i
  have hB : ∀ a : Bool, IsUnit (mbSystem M (meanObs M .IS ν) a) :=
    fun a => isUnit_mbSystem_meanObs_IS M ν hinv hμ a
  obtain ⟨α, β, hcent, hdecomp⟩ := influence_tangent_decomposition M ν hinv hR hrint hμ w
  -- the score of the perturbation is the influence function
  have hscore : ∀ z : Step S, pertDeriv M m v α β 0 z = infl M ν w z := by
    intro z
    rw [pertDeriv_zero, hdecomp z, dcoefA, dcoefB,
      hgauss (Step.state z) (M.act (Step.arm z) (Step.state z)), integral_id_gaussianReal]
    ring
  have hsample : sampleLaw M (Measure.map Step.state ν) T = Measure.pi fun _ : Fin T => ν := by
    rw [sampleLaw, obsLaw_map_state M ν hinv]
  obtain ⟨D, hD⟩ : ∃ D : (Fin T → Step S) → ℝ, D = fun path => ∑ s, w s * δ T path s :=
    ⟨_, rfl⟩
  have hDmeas : Measurable D := by
    rw [hD]
    exact Finset.measurable_sum _ fun s _ => (hmeas T s).const_mul _
  have hDL2 : MemLp D 2 (Measure.pi fun _ : Fin T => ν) := by
    rw [hD, ← hsample]
    exact memLp_finset_sum _ (fun s _ => (hL2 T s).const_mul _)
  have hderiv1 : HasDerivAt
      (fun t => ∫ p, D p * ∏ i, pertDens M m v α β t (p i) ∂(Measure.pi fun _ : Fin T => ν))
      (∫ p, D p * ∑ i : Fin T, pertDeriv M m v α β 0 (p i)
        ∂(Measure.pi fun _ : Fin T => ν)) 0 := by
    refine Statistics.hasDerivAt_integral_pi_mul ν
      (fun t z => pertDens M m v α β t z) (fun t z => pertDeriv M m v α β t z) D
      (envEps_pos β) (fun z => envelope m v α β z)
      (fun z => pertDens_zero M m v α β z)
      (fun t => ?_) ?_ hDmeas hDL2
      (fun z t _ => hasDerivAt_pertDens M m v α β t z)
      (fun z => one_le_envelope m v α β z)
      (fun z t ht => abs_pertDens_le_envelope M m v α β ht z)
      (fun z t ht => abs_pertDeriv_le_envelope M m v α β ht z)
      (measurable_envelope m v α β)
      (memLp_envelope m v α β M hgauss ν hinv)
    · simp only [pertDens, Step.state, Step.arm, Step.next, Step.rwd]; fun_prop
    · simp only [pertDeriv, dcoefA, dcoefB, dcoefC, Step.state, Step.arm, Step.next, Step.rwd]
      fun_prop
  have haff : ∀ t : ℝ, |t| < envEps β →
      ∫ p, D p * ∏ i, pertDens M m v α β t (p i) ∂(Measure.pi fun _ : Fin T => ν)
        = ∑ s, w s * (perturbModel M m v α β t).ate s := by
    intro t ht
    have hprodL2 := memLp_prod_pertDens M m v hgauss α β hcent ν hinv ht T
    have hints : ∀ s : S, Integrable
        (fun p : Fin T → Step S => δ T p s * ∏ i, pertDens M m v α β t (p i))
        (Measure.pi fun _ : Fin T => ν) := by
      intro s
      have h1 : MemLp (fun p : Fin T → Step S => δ T p s) 2
          (Measure.pi fun _ : Fin T => ν) := by
        rw [← hsample]; exact hL2 T s
      exact h1.integrable_mul hprodL2
    have hexp : ∀ p : Fin T → Step S, D p * ∏ i, pertDens M m v α β t (p i)
        = ∑ s, w s * (δ T p s * ∏ i, pertDens M m v α β t (p i)) := by
      intro p
      rw [hD, Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_finsetSum _ (fun s _ => (hints s).const_mul _)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_const_mul,
      ← integral_sampleLaw_perturbModel M m v hgauss α β hcent ν hinv ht T (fun p => δ T p s),
      hunbiased (perturbModel M m v α β t) rfl rfl
        ⟨_, perturbModel_gaussianRewards M m v α β t⟩ T hT s]
  have hderiv2 : HasDerivAt (fun t => ∑ s, w s * (perturbModel M m v α β t).ate s)
      (∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
        (scoreStat M v α β ν)) 0 :=
    HasDerivAt.fun_sum fun s _ =>
      (hasDerivAt_ate_perturbModel M m v hgauss α β hcent ν hinv hμ s).const_mul (w s)
  have hderiv1' : HasDerivAt (fun t => ∑ s, w s * (perturbModel M m v α β t).ate s)
      (∫ p, D p * ∑ i : Fin T, pertDeriv M m v α β 0 (p i)
        ∂(Measure.pi fun _ : Fin T => ν)) 0 := by
    refine hderiv1.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (envEps_pos β)] with t ht
    exact (haff t (by simpa [Real.dist_eq] using ht)).symm
  have hkey := hderiv1'.unique hderiv2
  have hintφ : ∀ s : S, Integrable (fun z : Step S =>
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * pertDeriv M m v α β 0 z) ν := fun s =>
    (memLp_influence M ν hinv hR hrint hμ s ν hr2).integrable_mul
      (memLp_pertDeriv M m v hgauss α β hcent ν hinv)
  have hrhs : ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
      (scoreStat M v α β ν) = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by
    have hstep : ∀ s : S, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s)
        (meanObs M .IS ν) (scoreStat M v α β ν)
        = ∫ z, w s * ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
            (estObs M .IS z)) * pertDeriv M m v α β 0 z) ∂ν := by
      intro s
      rw [integral_const_mul, integral_influence_pertDeriv M m v hgauss α β hcent ν hinv hN hB s]
    rw [Finset.sum_congr rfl fun s _ => hstep s,
      ← integral_finsetSum _ (fun s _ => (hintφ s).const_mul _),
      ← integral_infl_sq M ν hinv hR hrint hr2 hμ hiter w]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hsum : ∑ s : S, w s * ((fderiv ℝ (fun u : EstInput S => mbATE M u s)
        (meanObs M .IS ν) (estObs M .IS z)) * pertDeriv M m v α β 0 z)
        = (∑ s : S, w s * (fderiv ℝ (fun u : EstInput S => mbATE M u s)
            (meanObs M .IS ν) (estObs M .IS z))) * pertDeriv M m v α β 0 z := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    show (∑ s : S, w s * ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
        (estObs M .IS z)) * pertDeriv M m v α β 0 z)) = infl M ν w z ^ 2
    rw [hsum, hscore z]
    simp only [infl]
    ring
  rw [hsample]
  have hgoal : ∀ p : Fin T → Step S,
      (∑ s, w s * δ T p s)
        * (∑ i : Fin T, ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s)
            (meanObs M .IS ν) (estObs M .IS (p i)))
        = D p * ∑ i : Fin T, pertDeriv M m v α β 0 (p i) := by
    intro p
    rw [hD]
    refine congrArg _ ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hscore (p i)]
    simp only [infl]
  rw [integral_congr_ae (Filter.Eventually.of_forall hgoal), hkey, hrhs]

end TreatmentLocality


end



open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open TreatmentLocality in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (δ : (T : ℕ) → (Fin T → Step S) → S → ℝ)
    (hmeas : ∀ T s, Measurable (fun path => δ T path s))
    (hL2 : ∀ T s, MemLp (fun path => δ T path s) 2
      (sampleLaw M (Measure.map Step.state ν) T))
    (hunbiased : ∀ (M' : Model S), M'.crucial = M.crucial → M'.γdisc = M.γdisc →
      (∃ m' : S → Bool → ℝ, M'.GaussianRewards m' v) →
      ∀ T : ℕ, 1 ≤ T → ∀ s,
        ∫ path, δ T path s ∂(sampleLaw M' (Measure.map Step.state ν) T) = M'.ate s)
    (w : S → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∫ path, (∑ s, w s * δ T path s)
        * (∑ i : Fin T, ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s)
            (meanObs M .IS ν) (estObs M .IS (path i)))
        ∂(sampleLaw M (Measure.map Step.state ν) T)
      = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' :=
  TreatmentLocality.influence_score_covariance_iid_aux M m v hgauss hpos ν hinv δ hmeas hL2
    hunbiased w T hT
