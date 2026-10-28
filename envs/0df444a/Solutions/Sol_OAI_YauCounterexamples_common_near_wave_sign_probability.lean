-- Prove2me | solution 1 for OAI.YauCounterexamples.common_near_wave_sign_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:17:02.503761+00:00
-- url     : https://prove2.me/submissions/178d5b6e-56a8-43d1-85f9-589e0c016048

import Mathlib
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace YauCounterexamples
theorem lowerSemicontinuous_measure_neg {A X : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [MeasurableSpace X] (μ : Measure X)
    (F : A → X → ℝ) (hF : ∀ a, Measurable (F a))
    (hc : ∀ x, Continuous (fun a => F a x)) :
    LowerSemicontinuous (fun a => μ {x | F a x < 0}) := by
  let G : A → X → ℝ≥0∞ := fun a => {x | F a x < 0}.indicator (fun _ => 1)
  have hG (a : A) : Measurable (G a) :=
    measurable_const.indicator (measurableSet_lt (hF a) measurable_const)
  have hGl (x : X) : LowerSemicontinuous (fun a => G a x) := by
    have ho : IsOpen {a | F a x < 0} := isOpen_lt (hc x) continuous_const
    exact ho.lowerSemicontinuous_indicator (show (0 : ℝ≥0∞) ≤ 1 from zero_le)
  have hGi (a : A) : ∫⁻ x, G a x ∂μ = μ {x | F a x < 0} := by
    dsimp only [G]
    rw [lintegral_indicator (measurableSet_lt (hF a) measurable_const)]
    simp
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro a
  rw [← hGi a]
  calc
    ∫⁻ x, G a x ∂μ ≤ ∫⁻ x, liminf (fun a' => G a' x) (𝓝 a) ∂μ :=
      lintegral_mono (fun x => (hGl x).le_liminf a)
    _ ≤ liminf (fun a' => ∫⁻ x, G a' x ∂μ) (𝓝 a) := lintegral_liminf_le hG
    _ = liminf (fun a' => μ {x | F a' x < 0}) (𝓝 a) := by simp_rw [hGi]

theorem gaussian_pi_open_pos {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (s : Set (ι → ℝ)) (hs : IsOpen s) (hne : s.Nonempty) :
    0 < (Measure.pi (fun i => gaussianReal (m i) 1)) s := by
  have (i : ι) : Measure.IsOpenPosMeasure (gaussianReal (m i) 1) :=
    (gaussianReal_absolutelyContinuous' (m i) one_ne_zero).isOpenPosMeasure
  exact hs.measure_pos _ hne

theorem gaussianPairOppositeProbability_pos (p : ℝ × ℝ × ℝ)
    (hp : -1 < p.1 ∧ p.1 < 1) : 0 < gaussianPairOppositeProbability p := by
  have hpos : 0 < Real.sqrt (1 - p.1 ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  apply gaussian_pi_open_pos
  · apply isOpen_lt _ continuous_const
    unfold gaussianPairSignProduct
    fun_prop
  · refine ⟨![1 - p.2.1, (-1 - p.2.2 - p.1 * (1 - p.2.1)) /
        Real.sqrt (1 - p.1 ^ 2)], ?_⟩
    change (p.2.1 + (1 - p.2.1)) *
      (p.2.2 + p.1 * (1 - p.2.1) + Real.sqrt (1 - p.1 ^ 2) *
        ((-1 - p.2.2 - p.1 * (1 - p.2.1)) / Real.sqrt (1 - p.1 ^ 2))) < 0
    field_simp
    nlinarith

theorem lowerSemicontinuous_gaussianPairOppositeProbability :
    LowerSemicontinuous gaussianPairOppositeProbability := by
  apply lowerSemicontinuous_measure_neg
  · intro p
    unfold gaussianPairSignProduct
    fun_prop
  · intro x
    unfold gaussianPairSignProduct
    fun_prop

theorem gaussian_opposite_uniform (a b M : ℝ) (ha : -1 < a) (hab : a ≤ b)
    (hb : b < 1) (hM : 0 ≤ M) :
    ∃ q : ℝ, 0 < q ∧ ∀ p : ℝ × ℝ × ℝ,
      a ≤ p.1 → p.1 ≤ b → |p.2.1| ≤ M → |p.2.2| ≤ M →
      ENNReal.ofReal q ≤ gaussianPairOppositeProbability p := by
  let K : Set (ℝ × ℝ × ℝ) := Icc a b ×ˢ (Icc (-M) M ×ˢ Icc (-M) M)
  have hKn : K.Nonempty := ⟨(a, 0, 0), ⟨⟨le_rfl, hab⟩, ⟨by constructor <;> linarith,
    by constructor <;> linarith⟩⟩⟩
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨p, hpK, hpmin⟩ := LowerSemicontinuousOn.exists_isMinOn hKn hKc
    (lowerSemicontinuous_gaussianPairOppositeProbability.lowerSemicontinuousOn K)
  have hprob : 0 < gaussianPairOppositeProbability p :=
    gaussianPairOppositeProbability_pos p ⟨ha.trans_le hpK.1.1, hpK.1.2.trans_lt hb⟩
  have hfinite : gaussianPairOppositeProbability p ≠ ∞ := measure_ne_top _ _
  refine ⟨(gaussianPairOppositeProbability p).toReal, ENNReal.toReal_pos hprob.ne' hfinite, ?_⟩
  intro z hza hzb hz1 hz2
  rw [ENNReal.ofReal_toReal hfinite]
  exact hpmin ⟨⟨hza, hzb⟩, abs_le.mp hz1, abs_le.mp hz2⟩

end YauCounterexamples

end

open Set Function MeasureTheory
open scoped ENNReal
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_StdGaussianMapInnerUnit
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_map_inner_unit (a : E) (ha : ‖a‖ = 1) :
    (stdGaussian E).map (fun x => ⟪a, x⟫) = gaussianReal 0 1 := by
  change (stdGaussian E).map (innerSL ℝ a) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  simp [ha]

theorem stdGaussian_map_orthonormal_pair (a c : E) (ha : ‖a‖ = 1) (hc : ‖c‖ = 1)
    (hac : ⟪a, c⟫ = 0) :
    (stdGaussian E).map (fun x => (⟪a, x⟫, ⟪c, x⟫)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hlaw : HasGaussianLaw (fun x : E => (⟪a, x⟫, ⟪c, x⟫)) (stdGaussian E) := by
    exact (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
      ((innerSL ℝ a).prod (innerSL ℝ c))
  have hcov : cov[fun x : E => ⟪a, x⟫, fun x : E => ⟪c, x⟫; stdGaussian E] = 0 := by
    rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian]
    exact hac
  rw [(hlaw.indepFun_of_covariance_eq_zero hcov).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop), stdGaussian_map_inner_unit a ha,
    stdGaussian_map_inner_unit c hc]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem correlated_pair_orthogonal (a b : E) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hρ : |⟪a, b⟫| < 1) :
    let ρ := ⟪a, b⟫
    let s := Real.sqrt (1 - ρ ^ 2)
    let c := s⁻¹ • (b - ρ • a)
    ‖c‖ = 1 ∧ ⟪a, c⟫ = 0 ∧ b = ρ • a + s • c := by
  dsimp only
  let ρ := ⟪a, b⟫
  let s := Real.sqrt (1 - ρ ^ 2)
  have hr : 0 < 1 - ρ ^ 2 := by
    dsimp only [ρ]
    nlinarith [abs_lt.mp hρ]
  have hs : 0 < s := Real.sqrt_pos.mpr hr
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hr.le
  have haa : ⟪a, a⟫ = 1 := by simp [ha]
  have hbb : ⟪b, b⟫ = 1 := by simp [hb]
  have hnorm : ‖b - ρ • a‖ ^ 2 = s ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, haa, hbb]
    rw [real_inner_comm a b]
    change 1 - ρ * ρ - (ρ * ρ - ρ * (ρ * 1)) = s ^ 2
    nlinarith
  have hnorm' : ‖b - ρ • a‖ = s := by
    nlinarith [norm_nonneg (b - ρ • a)]
  refine ⟨?_, ?_, ?_⟩
  · change ‖s⁻¹ • (b - ρ • a)‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, hnorm', inv_mul_cancel₀ hs.ne']
  · change ⟪a, s⁻¹ • (b - ρ • a)⟫ = 0
    simp only [real_inner_smul_right, inner_sub_right, haa]
    change s⁻¹ * (ρ - ρ * 1) = 0
    ring
  · change b = ρ • a + s • (s⁻¹ • (b - ρ • a))
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CosUnitQuadraticGap
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace YauCounterexamples

lemma cos_unit_quadratic_gap {s : ℝ} (hs : |s| ≤ 1) : s^2/4 ≤ 1-Real.cos s := by
  let f : ℝ → ℝ := fun t => 1-Real.cos t-t^2/4
  let f' : ℝ → ℝ := fun t => Real.sin t-t/2
  let f'' : ℝ → ℝ := fun t => Real.cos t-1/2
  have hd (t : ℝ) : HasDerivAt f (f' t) t := by
    convert ((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).sub
      (((hasDerivAt_id t).pow 2).div_const 4) using 1 <;> first | rfl | (dsimp [f,f']; ring)
  have hdd (t : ℝ) : HasDerivAt f' (f'' t) t := by
    exact (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).div_const 2)
  have hc : ConvexOn ℝ (Icc (-1) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hdd t).hasDerivWithinAt)
    intro t ht
    dsimp [f'']
    have ht := interior_subset ht
    have hsq : t^2 ≤ 1 := by
      have hp := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ t+1 by linarith [ht.1])
      nlinarith
    have hcos := Real.one_sub_sq_div_two_le_cos (x := t)
    linarith
  have hmem : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
  have hneg : -s ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hmem.1,hmem.2]
  have hh := hc.2 hmem hneg (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ)+1/2=1 by norm_num)
  dsimp [f] at hh
  simp only [Real.cos_neg,neg_sq] at hh
  rw [show (1/2 : ℝ)*s+1/2*(-s)=0 by ring,Real.cos_zero] at hh
  nlinarith

lemma common_weight_cosine_gap {I : Type*} [Fintype I]
    (weights : I → ℝ) (hweights : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (θ : I → Fin 3 → ℝ) {κ : ℝ}
    (hθ : ∀ i j, |θ i j| ≤ 1) (he : ∀ i, κ ≤ ∑ j, (θ i j)^2) :
    (∀ j, 1/2 ≤ ∑ i, weights i*Real.cos (θ i j)) ∧
      κ/4 ≤ ∑ j, (1-∑ i, weights i*Real.cos (θ i j)) := by
  classical
  constructor
  · intro j
    calc
      1/2 = ∑ i, weights i*(1/2) := by rw [←Finset.sum_mul,hsum]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (by
        have hs : (θ i j)^2 ≤ 1 := by
          have hab := abs_le.mp (hθ i j)
          have hp := mul_nonneg (sub_nonneg.mpr hab.2) (show 0 ≤ θ i j+1 by linarith [hab.1])
          nlinarith
        linarith [Real.one_sub_sq_div_two_le_cos (x := θ i j)]) (hweights i))
  · calc
      κ/4 = ∑ i, weights i*(κ/4) := by rw [←Finset.sum_mul,hsum]; ring
      _ ≤ ∑ i, weights i*(∑ j, (1-Real.cos (θ i j))) := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_left _ (hweights i)
        apply (div_le_div_of_nonneg_right (he i) (by norm_num : (0 : ℝ) ≤ 4)).trans
        rw [Finset.sum_div]
        exact Finset.sum_le_sum (fun j _ => cos_unit_quadratic_gap (hθ i j))
      _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hsum]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GeneratedCutoffWaveEndpointRatio
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

section Normalize
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalize_vector_error (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • b‖ ≤ 2*‖a-b‖/‖a‖ := by
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  calc
    _ = ‖‖a‖⁻¹ • (a-b)+(‖a‖⁻¹-‖b‖⁻¹) • b‖ := by congr 1; module
    _ ≤ ‖‖a‖⁻¹ • (a-b)‖+‖(‖a‖⁻¹-‖b‖⁻¹) • b‖ := norm_add_le _ _
    _ = ‖a-b‖/‖a‖+|‖b‖-‖a‖|/‖a‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr han)]
      have he : ‖a‖⁻¹-‖b‖⁻¹ = (‖b‖-‖a‖)/(‖a‖*‖b‖) := by field_simp
      rw [he,abs_div,abs_mul,abs_of_pos han,abs_of_pos hbn]
      field_simp
    _ ≤ ‖a-b‖/‖a‖+‖a-b‖/‖a‖ := by
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le b a
    _ = _ := by ring

lemma norm_normalize_vector (a : E) (ha : a ≠ 0) : ‖‖a‖⁻¹ • a‖ = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]

end Normalize

variable {I : Type*} [Fintype I]

lemma complexValueVector_inner (z w : I → ℂ) :
    ⟪complexValueVector z,complexValueVector w⟫ = ∑ i, ((starRingEnd ℂ (z i))*w i).re := by
  simp only [PiLp.inner_apply,complexValueVector,Fintype.sum_sum_type,
    RCLike.inner_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    neg_mul,sub_neg_eq_add,Finset.sum_add_distrib, Sum.elim_inl, Sum.elim_inr]
  simp only [starRingEnd_apply, star_trivial]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma complexValueVector_norm_sq (z : I → ℂ) :
    ‖complexValueVector z‖^2 = ∑ i, ‖z i‖^2 := by
  rw [←real_inner_self_eq_norm_sq,complexValueVector_inner]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,neg_mul,sub_neg_eq_add,
    Complex.sq_norm]
  rw [Complex.normSq_apply]

omit [Fintype I] in
lemma complexValueVector_real_smul (a : ℝ) (z : I → ℂ) :
    complexValueVector (fun i => (a : ℂ)*z i) = a • complexValueVector z := by
  ext i
  cases i <;> simp [complexValueVector,Complex.mul_re,Complex.mul_im]

lemma complexValueVector_rotated_norm (z : I → ℂ) (θ : I → ℝ) :
    ‖complexValueVector (rotatedWaveValues z θ)‖ = ‖complexValueVector z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [complexValueVector_norm_sq,complexValueVector_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  simp [rotatedWaveValues,Complex.norm_exp]

lemma complexValueVector_rotated_inner (z : I → ℂ) (θ : I → ℝ) :
    ⟪complexValueVector z,complexValueVector (rotatedWaveValues z θ)⟫ =
      ∑ i, ‖z i‖^2*Real.cos (θ i) := by
  rw [complexValueVector_inner]
  apply Finset.sum_congr rfl
  intro i _
  have he : starRingEnd ℂ (z i)*(Complex.exp ((θ i : ℂ)*Complex.I)*z i) =
      (‖z i‖^2 : ℂ)*Complex.exp ((θ i : ℂ)*Complex.I) := by
    rw [show starRingEnd ℂ (z i)*(Complex.exp ((θ i : ℂ)*Complex.I)*z i) =
      (starRingEnd ℂ (z i)*z i)*Complex.exp ((θ i : ℂ)*Complex.I) by ring,
      Complex.conj_mul']
  change (starRingEnd ℂ (z i)*(Complex.exp ((θ i : ℂ)*Complex.I)*z i)).re = _
  rw [he]
  simp [←Complex.ofReal_pow,Complex.mul_re,Complex.exp_re]

end



open Set Filter
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_UnitCorrelation
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace YauCounterexamples

section Correlations
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma unitCorrelation_error (a b c : E) (ha : a ≠ 0) (hb : b ≠ 0)
    {δ : ℝ} (hδ : δ < 1) (hbc : ‖b-c‖ ≤ δ*‖b‖) :
    c ≠ 0 ∧ |unitCorrelation a b-unitCorrelation a c| ≤ 2*δ := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hc : c ≠ 0 := by
    intro hc
    simp only [hc,sub_zero] at hbc
    nlinarith
  refine ⟨hc,?_⟩
  calc
    _ = |⟪‖a‖⁻¹ • a, ‖b‖⁻¹ • b-‖c‖⁻¹ • c⟫| := by
      rw [inner_sub_right]; rfl
    _ ≤ ‖‖a‖⁻¹ • a‖*‖‖b‖⁻¹ • b-‖c‖⁻¹ • c‖ := abs_real_inner_le_norm _ _
    _ = ‖‖b‖⁻¹ • b-‖c‖⁻¹ • c‖ := by rw [norm_normalize_vector a ha,one_mul]
    _ ≤ 2*‖b-c‖/‖b‖ := normalize_vector_error b c hb hc
    _ ≤ 2*δ := by apply (div_le_iff₀ hbn).mpr; nlinarith

lemma unitCorrelation_pos_smul (a b : E) {r : ℝ} (hr : 0 < r) :
    unitCorrelation a (r • b) = unitCorrelation a b := by
  unfold unitCorrelation
  congr 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_inv_rev,smul_smul]
  congr 1
  field_simp

end Correlations

variable {I : Type*} [Fintype I]

lemma common_complex_weights {z : I → ℂ} (hz : complexValueVector z ≠ 0) :
    (∀ i, 0 ≤ ‖z i‖^2/‖complexValueVector z‖^2) ∧
      (∑ i, ‖z i‖^2/‖complexValueVector z‖^2) = 1 := by
  refine ⟨fun i => div_nonneg (sq_nonneg _) (sq_nonneg _),?_⟩
  rw [←Finset.sum_div,←complexValueVector_norm_sq]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))

lemma rotated_complex_unitCorrelation (z : I → ℂ) (θ : I → ℝ) :
    unitCorrelation (complexValueVector z) (complexValueVector (rotatedWaveValues z θ)) =
      ∑ i, (‖z i‖^2/‖complexValueVector z‖^2)*Real.cos (θ i) := by
  unfold unitCorrelation
  rw [real_inner_smul_left,real_inner_smul_right,complexValueVector_rotated_norm,
    complexValueVector_rotated_inner]
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div]
  ring

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ComplexGaussianRealValue
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma complex_stdGaussian_eq_map :
    stdGaussian ℂ = (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map
      (fun x => (x 0 : ℂ)+(x 1 : ℂ)*Complex.I) := by
  simpa [Complex.coe_orthonormalBasisOneI,Fin.sum_univ_two,Algebra.smul_def]
    using stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI

lemma complex_gaussian_pair :
    MeasurePreserving (fun x : ℝ × ℝ => (x.1 : ℂ)+(x.2 : ℂ)*Complex.I)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (stdGaussian ℂ) := by
  have hp := (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).symm
  have hm : MeasurePreserving (fun x : Fin 2 → ℝ => (x 0 : ℂ)+(x 1 : ℂ)*Complex.I)
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) (stdGaussian ℂ) :=
    ⟨by fun_prop,complex_stdGaussian_eq_map.symm⟩
  exact hm.comp hp

lemma gaussian_complex_conj :
    MeasurePreserving (starRingEnd ℂ) (stdGaussian ℂ) (stdGaussian ℂ) :=
  ⟨Complex.continuous_conj.measurable,stdGaussian_map Complex.conjLIE⟩

lemma gaussian_complex_from_real_parts {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun x : (ι ⊕ ι) → ℝ =>
      fun i => (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I)
      (Measure.pi (fun _ : ι ⊕ ι => gaussianReal 0 1))
      (Measure.pi (fun _ : ι => stdGaussian ℂ)) := by
  have hsplit := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).symm
  have hc := gaussian_complex_conj.comp complex_gaussian_pair
  have hpi := measurePreserving_pi (fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ : ι => stdGaussian ℂ) (fun _ => hc)
  convert hpi.comp (hpair.comp hsplit) using 1
  all_goals try with_reducible_and_instances rfl
  ext x i
  simp [Function.comp_def,MeasurableEquiv.sumPiEquivProdPi,
    MeasurableEquiv.arrowProdEquivProdArrow, Complex.conj_ofReal,sub_eq_add_neg]


end

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_opposite_eq (a b : E) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hρ : |⟪a, b⟫| < 1) (m₁ m₂ : ℝ) :
    (stdGaussian E) {x | (m₁ + ⟪a, x⟫) * (m₂ + ⟪b, x⟫) < 0} =
      gaussianPairOppositeProbability (⟪a, b⟫, m₁, m₂) := by
  let ρ := ⟪a, b⟫
  let s := Real.sqrt (1 - ρ ^ 2)
  let c := s⁻¹ • (b - ρ • a)
  obtain ⟨hc, hac, hbc⟩ := correlated_pair_orthogonal a b ha hb hρ
  change ‖c‖ = 1 at hc
  change ⟪a, c⟫ = 0 at hac
  change b = ρ • a + s • c at hbc
  let S : Set (ℝ × ℝ) := {z | (m₁ + z.1) * (m₂ + ρ * z.1 + s * z.2) < 0}
  have hS : MeasurableSet S :=
    measurableSet_lt (by fun_prop) measurable_const
  let F : E → ℝ × ℝ := fun x => (⟪a, x⟫, ⟪c, x⟫)
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have hset : {x | (m₁ + ⟪a, x⟫) * (m₂ + ⟪b, x⟫) < 0} = F ⁻¹' S := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, F, S]
    rw [hbc]
    simp only [inner_add_left, real_inner_smul_left, add_assoc]
  rw [hset, ← Measure.map_apply hF hS]
  change ((stdGaussian E).map (fun x => (⟪a, x⟫, ⟪c, x⟫))) S = _
  rw [stdGaussian_map_orthonormal_pair a c ha hc hac,
    ← (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).map_eq,
    Measure.map_apply (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurable hS]
  rfl


end


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
variable {I : Type*} [Fintype I]

lemma complexGaussianRealValue_real_parts (z : I → ℂ) (x : (I ⊕ I) → ℝ) :
    complexGaussianRealValue z (fun i => (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I) =
      ⟪complexValueVector z,WithLp.toLp 2 x⟫ := by
  simp only [complexGaussianRealValue,PiLp.inner_apply,complexValueVector,
    Fintype.sum_sum_type, RCLike.inner_apply]
  simp only [Sum.elim_inl,Sum.elim_inr,starRingEnd_apply,star_trivial]
  simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,
    Complex.I_im,mul_zero,sub_zero,Complex.sub_im,Complex.mul_im,mul_one,
    add_zero,zero_sub,neg_mul,sub_neg_eq_add, Finset.sum_add_distrib]

lemma complex_gaussian_standardized_sign_law (z w : I → ℂ)
    (hz : complexValueVector z ≠ 0) (hw : complexValueVector w ≠ 0)
    (m₁ m₂ : ℝ) (hρ : |unitCorrelation (complexValueVector z) (complexValueVector w)| < 1) :
    (Measure.pi (fun _ : I => stdGaussian ℂ))
      {γ | (m₁+complexGaussianRealValue z γ)*(m₂+complexGaussianRealValue w γ) < 0} =
      gaussianPairOppositeProbability (unitCorrelation (complexValueVector z) (complexValueVector w),
        m₁/‖complexValueVector z‖,m₂/‖complexValueVector w‖) := by
  let a := complexValueVector z
  let b := complexValueVector w
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hb : 0 < ‖b‖ := norm_pos_iff.mpr hw
  let S : Set (I → ℂ) :=
    {γ | (m₁+complexGaussianRealValue z γ)*(m₂+complexGaussianRealValue w γ) < 0}
  have hS : MeasurableSet S := by
    apply measurableSet_lt _ measurable_const
    dsimp [complexGaussianRealValue]; fun_prop
  rw [←gaussian_complex_from_real_parts.map_eq,Measure.map_apply
    gaussian_complex_from_real_parts.measurable hS]
  let T : Set (EuclideanSpace ℝ (I ⊕ I)) :=
    {x | (m₁/‖a‖+⟪‖a‖⁻¹ • a,x⟫)*(m₂/‖b‖+⟪‖b‖⁻¹ • b,x⟫) < 0}
  have hset : (fun x : (I ⊕ I) → ℝ => fun i =>
      (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I) ⁻¹' S =
        (WithLp.toLp 2) ⁻¹' T := by
    ext x
    simp only [S,T,Set.mem_preimage,Set.mem_ofPred_eq,complexGaussianRealValue_real_parts,
      real_inner_smul_left]
    change (m₁+⟪a,WithLp.toLp 2 x⟫)*(m₂+⟪b,WithLp.toLp 2 x⟫) < 0 ↔ _
    rw [show m₁/‖a‖+‖a‖⁻¹*⟪a,WithLp.toLp 2 x⟫ =
      (m₁+⟪a,WithLp.toLp 2 x⟫)/‖a‖ by ring,
      show m₂/‖b‖+‖b‖⁻¹*⟪b,WithLp.toLp 2 x⟫ =
      (m₂+⟪b,WithLp.toLp 2 x⟫)/‖b‖ by ring,div_mul_div_comm]
    rw [div_lt_iff₀ (mul_pos ha hb),zero_mul]
  change (Measure.pi (fun _ : I ⊕ I => gaussianReal 0 1))
      ((fun x => fun i => (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I) ⁻¹' S) = _
  rw [hset,←Measure.map_apply (PiLp.continuous_toLp 2 _).measurable
    (show MeasurableSet T by
      apply measurableSet_lt _ measurable_const
      fun_prop),map_pi_eq_stdGaussian]
  exact stdGaussian_opposite_eq _ _ (norm_normalize_vector a hz) (norm_normalize_vector b hw) hρ (m₁/‖a‖) (m₂/‖b‖)

theorem complex_gaussian_sign_uniform (α β M : ℝ) (hα : -1 < α) (hαβ : α ≤ β)
    (hβ : β < 1) (hM : 0 ≤ M) :
    ∃ q > 0, ∀ (I : Type) [Fintype I] (z w : I → ℂ) (m₁ m₂ : ℝ),
      complexValueVector z ≠ 0 → complexValueVector w ≠ 0 →
      α ≤ unitCorrelation (complexValueVector z) (complexValueVector w) →
      unitCorrelation (complexValueVector z) (complexValueVector w) ≤ β →
      |m₁/‖complexValueVector z‖| ≤ M → |m₂/‖complexValueVector w‖| ≤ M →
      ENNReal.ofReal q ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (m₁+complexGaussianRealValue z γ)*(m₂+complexGaussianRealValue w γ) < 0} := by
  obtain ⟨q,hq,hprob⟩ := gaussian_opposite_uniform α β M hα hαβ hβ hM
  refine ⟨q,hq,?_⟩
  intro I _ z w m₁ m₂ hz hw hlo hhi hm₁ hm₂
  rw [complex_gaussian_standardized_sign_law z w hz hw m₁ m₂
    (abs_lt.mpr ⟨hα.trans_le hlo,hhi.trans_lt hβ⟩)]
  exact hprob _ hlo hhi hm₁ hm₂


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_UnitCorrelationSymm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace YauCounterexamples

lemma unitCorrelation_symm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) : unitCorrelation a b = unitCorrelation b a := real_inner_comm _ _

lemma unitCorrelation_two_errors {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a₀ b₀ a b : E) (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) {δ : ℝ} (hδ : δ < 1)
    (ha : ‖a₀-a‖ ≤ δ*‖a₀‖) (hb : ‖b₀-b‖ ≤ δ*‖b₀‖) :
    a ≠ 0 ∧ b ≠ 0 ∧ |unitCorrelation a₀ b₀-unitCorrelation a b| ≤ 4*δ := by
  obtain ⟨hb',hhb⟩ := unitCorrelation_error a₀ b₀ b ha₀ hb₀ hδ hb
  obtain ⟨ha',hha⟩ := unitCorrelation_error b a₀ a hb' ha₀ hδ ha
  rw [unitCorrelation_symm b a₀,unitCorrelation_symm b a] at hha
  refine ⟨ha',hb',?_⟩
  calc
    _ ≤ |unitCorrelation a₀ b₀-unitCorrelation a₀ b|+
        |unitCorrelation a₀ b-unitCorrelation a b| := abs_sub_le _ _ _
    _ ≤ 2*δ+2*δ := add_le_add hhb hha
    _ = 4*δ := by ring

section NearFar
variable {I : Type*} [Fintype I]

theorem perturbed_three_axis_correlation_gap {z : I → ℂ} (hz : complexValueVector z ≠ 0)
    (v : I → ℂ) (w : Fin 3 → I → ℂ) (α : Fin 3 → ℝ) (hα : ∀ j, 0 < α j)
    (θ : I → Fin 3 → ℝ) {κ δ : ℝ} (hκ : 0 < κ)
    (hδsmall : δ ≤ 1/16) (hδgap : δ ≤ κ/96)
    (hθ : ∀ i j, |θ i j| ≤ 1) (henergy : ∀ i, κ ≤ ∑ j, (θ i j)^2)
    (hbase : ‖complexValueVector z-complexValueVector v‖ ≤ δ*‖complexValueVector z‖)
    (herror : ∀ j, ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)
        -complexValueVector (w j)‖ ≤
      δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)‖) :
    complexValueVector v ≠ 0 ∧ (∀ j, complexValueVector (w j) ≠ 0) ∧
      ∃ j, 1/4 ≤ unitCorrelation (complexValueVector v) (complexValueVector (w j)) ∧
        unitCorrelation (complexValueVector v) (complexValueVector (w j)) ≤ 1-κ/24 := by
  let ρ : Fin 3 → ℝ := fun j => unitCorrelation (complexValueVector v) (complexValueVector (w j))
  let c : Fin 3 → ℝ := fun j => ∑ i, (‖z i‖^2/‖complexValueVector z‖^2)*Real.cos (θ i j)
  have herr (j) : complexValueVector v ≠ 0 ∧
      complexValueVector (w j) ≠ 0 ∧ |c j-ρ j| ≤ 4*δ := by
    have hb : complexValueVector (rotatedWaveValues z (fun i => θ i j)) ≠ 0 := by
      rw [←norm_ne_zero_iff,complexValueVector_rotated_norm]
      exact norm_ne_zero_iff.mpr hz
    have hbb : complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i) ≠ 0 := by
      rw [complexValueVector_real_smul]
      exact smul_ne_zero (ne_of_gt (hα j)) hb
    have hh := unitCorrelation_two_errors (complexValueVector z) _
      (complexValueVector v) (complexValueVector (w j)) hz hbb
      (show δ < 1 by linarith) hbase (herror j)
    rw [complexValueVector_real_smul,unitCorrelation_pos_smul _ _ (hα j),
      rotated_complex_unitCorrelation] at hh
    exact hh
  obtain ⟨hlow,hsum⟩ := common_weight_cosine_gap _ (common_complex_weights hz).1
    (common_complex_weights hz).2 θ hθ henergy
  have hl (j) : 1/4 ≤ ρ j := by
    have hh := (abs_le.mp (herr j).2.2).2
    have hc := hlow j
    change 1/2 ≤ c j at hc
    linarith
  have hg : 1/8 ≤ (∑ j, (1-ρ j))/κ := by
    have hh : (∑ j, (1-c j)) ≤ (∑ j, (1-ρ j))+12*δ := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (f := fun j => 1-c j) (g := fun j => 1-ρ j+4*δ)
        (fun j _ => by have hj := (abs_le.mp (herr j).2.2).1; linarith)
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
      norm_num at hh ⊢
      linarith
    change κ/4 ≤ ∑ j, (1-c j) at hsum
    apply (le_div_iff₀ hκ).mpr
    linarith
  have haxis : ∃ j, κ/24 ≤ 1-ρ j := by
    by_contra! h
    have hsumρ := (le_div_iff₀ hκ).mp hg
    simp only [Fin.sum_univ_three] at hsumρ
    linarith [h 0,h 1,h 2]
  obtain ⟨j,hj⟩ := haxis
  exact ⟨(herr 0).1,fun j => (herr j).2.1,j,hl j,by dsimp [ρ] at hj ⊢; linarith⟩

end NearFar

theorem common_near_wave_sign_probability_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ q > 0, ∀ (I : Type) [Fintype I] (z v : I → ℂ) (w : Fin 3 → I → ℂ)
      (α : Fin 3 → ℝ) (θ : I → Fin 3 → ℝ) (m : ℝ) (m' : Fin 3 → ℝ) (δ : ℝ),
      complexValueVector z ≠ 0 → (∀ j, 0 < α j) → δ ≤ 1/16 → δ ≤ κ/96 →
      (∀ i j, |θ i j| ≤ 1) → (∀ i, κ ≤ ∑ j, (θ i j)^2) →
      ‖complexValueVector z-complexValueVector v‖ ≤ δ*‖complexValueVector z‖ →
      (∀ j, ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)
        -complexValueVector (w j)‖ ≤
        δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)‖) →
      |m/‖complexValueVector v‖| ≤ 1 → (∀ j, |m' j/‖complexValueVector (w j)‖| ≤ 1) →
      ∃ j, ENNReal.ofReal q ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (m+complexGaussianRealValue v γ)*(m' j+complexGaussianRealValue (w j) γ) < 0} := by
  obtain ⟨q,hq,hprob⟩ := complex_gaussian_sign_uniform (1/4) (1-κ/24) 1
    (by norm_num) (by linarith) (by linarith) zero_le_one
  refine ⟨q,hq,?_⟩
  intro I _ z v w α θ m m' δ hz hα hδsmall hδgap hθ henergy hbase herror hm hm'
  obtain ⟨hv,hw,j,hlo,hhi⟩ := perturbed_three_axis_correlation_gap hz v w α hα θ hκ
    hδsmall hδgap hθ henergy hbase herror
  exact ⟨j,hprob I v (w j) m (m' j) hv (hw j) hlo hhi hm (hm' j)⟩

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.common_near_wave_sign_probability_oai := @OAI.YauCounterexamples.common_near_wave_sign_probability_oai
