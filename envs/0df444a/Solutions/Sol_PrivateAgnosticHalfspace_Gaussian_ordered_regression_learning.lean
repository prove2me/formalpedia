-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.ordered_regression_learning
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:47.519013+00:00
-- url     : https://prove2.me/submissions/19dea406-8e49-4991-9234-766fb262086e

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_OptimizerRealization
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_projected_regression_expected_error
import Definitions.Def_NonconvexAG_StochComposite_RSAG
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ChapterHermiteProductBasis
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_3
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_5
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_7
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_10
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_C_2
import Mathlib.Probability.Kernel.Composition.MeasureComp
set_option Elab.async false
set_option linter.all false

section
-- Solutions.CoefficientEnumeration
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma ofDigits_ofFn_sum (b d : ℕ) (f : Fin d → ℕ) :
    Nat.ofDigits b (List.ofFn f) = ∑ i, f i*b^i.val := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.ofFn_succ,Nat.ofDigits_cons,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
lemma indexCode_injective (d p : ℕ) : Function.Injective (@indexCode d p) := by
  intro κ ξ h
  by_cases hp : p = 0
  · subst p
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hκ := (κ.val i).isLt
    have hξ := (ξ.val i).isLt
    omega
  · have he : Nat.ofDigits (p+1) (List.ofFn (fun i => (κ.val i).val)) =
        Nat.ofDigits (p+1) (List.ofFn (fun i => (ξ.val i).val)) := by
      simpa only [ofDigits_ofFn_sum,indexCode] using h
    have hκ : ∀ a ∈ List.ofFn (fun i => (κ.val i).val), a < p+1 := by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact (κ.val i).isLt
    have hξ : ∀ a ∈ List.ofFn (fun i => (ξ.val i).val), a < p+1 := by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact (ξ.val i).isLt
    have hl := Nat.ofDigits_inj_of_len_eq (by omega : 1 < p+1) (by simp) hκ hξ he
    have hf := List.ofFn_injective hl
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun hf i
lemma indexRank_strictMono_code {d p : ℕ} (κ ξ : Index d p) (h : indexCode κ < indexCode ξ) :
    indexRank κ < indexRank ξ := by
  classical
  unfold indexRank
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro η hη
    simp only [mem_filter,mem_univ,true_and] at hη ⊢
    exact lt_trans hη h
  · intro he
    have hκ : κ ∈ (univ.filter (fun η : Index d p => indexCode η < indexCode ξ)) := by simp [h]
    rw [← he] at hκ
    simpa using hκ
lemma indexRank_injective (d p : ℕ) : Function.Injective (@indexRank d p) := by
  intro κ ξ h
  apply indexCode_injective d p
  rcases lt_trichotomy (indexCode κ) (indexCode ξ) with hc|hc|hc
  · have hr := indexRank_strictMono_code κ ξ hc
    omega
  · exact hc
  · have hr := indexRank_strictMono_code ξ κ hc
    omega
lemma indexRank_lt (d p : ℕ) (κ : Index d p) : indexRank κ < featureDimension d p := by
  classical
  have hc := ((lemma_B_8 d).2.2.2 p).2.1
  rw [← hc]
  unfold indexRank
  change (univ.filter (fun ξ : Index d p => indexCode ξ < indexCode κ)).card < univ.card
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨filter_subset _ _,?_⟩
  intro he
  have hκ : κ ∈ (univ.filter (fun ξ : Index d p => indexCode ξ < indexCode κ)) := by rw [he]; simp
  simpa using hκ
noncomputable def coefficientIndexEquiv (d p : ℕ) : Index d p ≃ Fin (featureDimension d p) :=
  Equiv.ofBijective (fun κ => ⟨indexRank κ,indexRank_lt d p κ⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro κ ξ h
      exact indexRank_injective d p (congrArg Fin.val h),by
      simpa only [Fintype.card_fin] using ((lemma_B_8 d).2.2.2 p).2.1⟩)
noncomputable def coefficientIsometry (d p : ℕ) : Coeff d p ≃ₗᵢ[ℝ] Vec (featureDimension d p) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (coefficientIndexEquiv d p)
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianMoments
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
local instance (d : ℕ) : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
local instance (d : ℕ) : IsGaussian (gaussian d) := by unfold gaussian; infer_instance
lemma holder_double (p : ℝ≥0∞) : ENNReal.HolderTriple (2*p) (2*p) p := by
  constructor
  rw [ENNReal.mul_inv (by left; norm_num) (by left; norm_num),← add_mul]
  have hh : (2:ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  rw [hh,one_mul]

lemma memLp_all_mul {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (f g : Z → ℝ)
    (hf : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ) (hg : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp g p μ) :
    ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun z => f z*g z) p μ := by
  intro p hp
  haveI := holder_double p
  exact (hg (2*p) (ENNReal.mul_ne_top (by norm_num) hp)).mul'
    (hf (2*p) (ENNReal.mul_ne_top (by norm_num) hp))

lemma gaussian_polynomial_memLp (d : ℕ) (Q : MvPolynomial (Fin d) ℝ) :
    ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun x : Vec d => MvPolynomial.eval (fun i => x i) Q) p (gaussian d) := by
  induction Q using MvPolynomial.induction_on with
  | C a => intro p hp; simpa using (memLp_const a (μ := gaussian d) (p := p))
  | add Q T hQ hT =>
    intro p hp
    convert! (hQ p hp).add (hT p hp) using 1
    ext x; simp only [map_add,Pi.add_apply]
  | mul_X Q i hQ =>
    have hcoord : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun x : Vec d => x i) p (gaussian d) := by
      intro p hp
      have h := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (ProbabilityTheory.IsGaussian.memLp_id (gaussian d) p hp)
      simpa only [Function.comp_def,EuclideanSpace.coe_proj,id_eq] using h
    simpa only [map_mul,MvPolynomial.eval_X] using memLp_all_mul (gaussian d) _ _ hQ hcoord
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def momentHermiteR (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)
noncomputable def momentHermiteFactor {d : ℕ} (i : Fin d) (n : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ k ∈ Finset.range (n+1), MvPolynomial.C ((momentHermiteR n).coeff k / Real.sqrt (n.factorial : ℝ)) *
    MvPolynomial.X i ^ k
noncomputable def momentHermiteTensor (d : ℕ) (κ : Fin d → ℕ) : MvPolynomial (Fin d) ℝ :=
  ∏ i, momentHermiteFactor i (κ i)
lemma eval_momentHermiteFactor {d : ℕ} (i : Fin d) (n : ℕ) (x : Vec d) :
    MvPolynomial.eval (fun j => x j) (momentHermiteFactor i n) = AMPLowDeg.RankOne.hermNorm n (x i) := by
  simp only [momentHermiteFactor,map_sum,map_mul,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X]
  have hh := Polynomial.eval_eq_sum_range (p := momentHermiteR n) (x i)
  have hd : (momentHermiteR n).natDegree = n := by
    rw [momentHermiteR,Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)),Polynomial.natDegree_hermite]
  rw [hd] at hh
  change (∑ k ∈ Finset.range (n+1), (momentHermiteR n).coeff k / Real.sqrt (n.factorial : ℝ) * (x i)^k) =
    (momentHermiteR n).eval (x i) / Real.sqrt (n.factorial : ℝ)
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,← hh]
lemma eval_momentHermiteTensor (d : ℕ) (κ : Fin d → ℕ) (x : Vec d) :
    MvPolynomial.eval (fun j => x j) (momentHermiteTensor d κ) = hermite d κ x := by
  simp only [momentHermiteTensor,map_prod,eval_momentHermiteFactor,hermite]
noncomputable def cutoffPolynomial (d p : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ κ : Index d p, momentHermiteTensor d (fun i => (κ.val i).val) ^ 2
lemma eval_cutoffPolynomial (d p : ℕ) (x : Vec d) :
    MvPolynomial.eval (fun i => x i) (cutoffPolynomial d p) = ‖features d p x‖ ^ 2 := by
  simp only [cutoffPolynomial,map_sum,map_pow,eval_momentHermiteTensor,EuclideanSpace.real_norm_sq_eq]
  rfl
lemma feature_norm_sq_integrable (d p : ℕ) :
    Integrable (fun x => ‖features d p x‖ ^ 2) (gaussian d) := by
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have h := (gaussian_polynomial_memLp d (cutoffPolynomial d p) 1 (by norm_num)).integrable (by norm_num)
  simpa only [eval_cutoffPolynomial] using h
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma feature_norm_sq_mean (d p : ℕ) :
    (∫ x, ‖features d p x‖ ^ 2 ∂gaussian d) = featureDimension d p := by
  classical
  have ho := ((lemma_B_8 d).2.2.2 p).2.2
  have hi (κ : Index d p) : Integrable (fun x => hermite d (fun i => (κ.val i).val) x ^ 2) (gaussian d) := by
    simpa only [pow_two] using (ho κ κ).1
  have he (κ : Index d p) :
      (∫ x, hermite d (fun i => (κ.val i).val) x ^ 2 ∂gaussian d) = 1 := by
    simpa only [pow_two,ite_true] using (ho κ κ).2
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∫ x, ∑ κ : Index d p, hermite d (fun i => (κ.val i).val) x ^ 2 ∂gaussian d) = _
  rw [integral_finsetSum _ (fun κ _ => hi κ)]
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact congrArg Nat.cast (((lemma_B_8 d).2.2.2 p).2.1)
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RegressionOracleGeometry
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def absoluteLinearLoss (a : E) (y : ℝ) (v : E) : ℝ := |inner ℝ v a-y|
noncomputable def absoluteLinearSubgradient (a : E) (y : ℝ) (v : E) : E :=
  if 0 ≤ inner ℝ v a-y then a else -a
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.FeatureClippingGeometry
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
lemma featureDimension_pos (d p : ℕ) : 0 < featureDimension d p := Nat.choose_pos (by omega)
lemma radius_pos (d p : ℕ) : 0 < radius d p := by
  have h : (0 : ℝ) < featureDimension d p := by exact_mod_cast featureDimension_pos d p
  unfold radius
  positivity
lemma continuous_features (d p : ℕ) : Continuous (features d p) := by
  unfold features
  apply Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Index d p => ℝ))
  apply continuous_pi
  intro κ
  unfold hermite AMPLowDeg.RankOne.hermNorm
  fun_prop
lemma clipScale_bounds (d p : ℕ) (x : Vec d) : 0 ≤ clipScale d p x ∧ clipScale d p x ≤ 1 := by
  unfold clipScale
  have hp : 0 < max (radius d p) ‖features d p x‖ := lt_of_lt_of_le (radius_pos d p) (le_max_left _ _)
  refine ⟨div_nonneg (radius_pos d p).le hp.le,?_⟩
  exact (div_le_one hp).mpr (le_max_left _ _)
lemma continuous_clipped (d p : ℕ) : Continuous (clipped d p) := by
  unfold clipped clipScale
  have hs : Continuous (fun x : Vec d => radius d p / max (radius d p) ‖features d p x‖) := by
    apply continuous_const.div (continuous_const.max (continuous_features d p).norm)
    intro x
    exact (lt_of_lt_of_le (radius_pos d p) (le_max_left _ _)).ne'
  exact continuous_smul.comp (hs.prodMk (continuous_features d p))
lemma norm_clipped_le_radius (d p : ℕ) (x : Vec d) : ‖clipped d p x‖ ≤ radius d p := by
  rw [clipped, norm_smul, Real.norm_eq_abs, abs_of_nonneg (clipScale_bounds d p x).1]
  unfold clipScale
  have hp : 0 < max (radius d p) ‖features d p x‖ := lt_of_lt_of_le (radius_pos d p) (le_max_left _ _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) (radius_pos d p).le
lemma norm_clipped_le_features (d p : ℕ) (x : Vec d) : ‖clipped d p x‖ ≤ ‖features d p x‖ := by
  rw [clipped, norm_smul, Real.norm_eq_abs, abs_of_nonneg (clipScale_bounds d p x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (clipScale_bounds d p x).2
lemma clipped_memLp_two (d p : ℕ) : MemLp (clipped d p) 2 (gaussian d) := by
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  exact MemLp.of_bound (continuous_clipped d p).aestronglyMeasurable (radius d p)
    (ae_of_all _ (norm_clipped_le_radius d p))
lemma clipped_second_moment (d p : ℕ) :
    (∫ x, ‖clipped d p x‖^2 ∂gaussian d) ≤ featureDimension d p := by
  rw [← feature_norm_sq_mean d p]
  apply integral_mono ((memLp_two_iff_integrable_sq_norm
    (continuous_clipped d p).aestronglyMeasurable).mp (clipped_memLp_two d p))
    (feature_norm_sq_integrable d p)
  intro x
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_clipped_le_features d p x) 2
lemma clipping_loss_bound (s q c y : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| = 1) (hy : |y| = 1) :
    |s*q-y| ≤ |q-c|+|c-y|+(1-s) := by
  have he : s*q-y = s*(q-y)+(s-1)*y := by ring
  have hb : |s*q-y| ≤ s*|q-y|+(1-s) := by
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hs.1, hy, mul_one, abs_of_nonpos (by linarith : s-1 ≤ 0)]
    linarith
  have ht := abs_sub_le q c y
  have hmul : s*|q-y| ≤ |q-y| := mul_le_of_le_one_left (abs_nonneg _) hs.2
  linarith
lemma clipping_scale_loss_indicator (d p : ℕ) (x : Vec d) :
    1-clipScale d p x ≤ {x : Vec d | radius d p < ‖features d p x‖}.indicator (fun _ => (1 : ℝ)) x := by
  change 1-clipScale d p x ≤ if radius d p < ‖features d p x‖ then 1 else 0
  by_cases hx : radius d p < ‖features d p x‖
  · rw [if_pos hx]
    linarith [(clipScale_bounds d p x).1]
  · rw [if_neg hx]
    unfold clipScale
    rw [max_eq_left (le_of_not_gt hx), div_self (radius_pos d p).ne', sub_self]
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.AcceleratedRegressionSchedule
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def accelAlpha (k : ℕ) : ℝ := 2/((k : ℝ)+1)
noncomputable def accelLambda (β : ℝ) (k : ℕ) : ℝ := (k : ℝ)*β/2
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AcceleratedPath
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open NonconvexAG.StochComposite
lemma batchEnd_one (k : ℕ) : batchEnd (fun _ => 1) k = k := by
  simp [batchEnd,Nat.card_Icc]
lemma sampleAvg_one {D : ℕ} {Ξ : Type*} (G : Vec D → Ξ → Vec D)
    (k : ℕ) (hk : 1 ≤ k) (v : Vec D) (s : ℕ → Ξ) :
    sampleAvg G (fun _ => 1) k v s = G v (s k) := by
  simp [sampleAvg,batchEnd_one,Nat.sub_add_cancel hk]
noncomputable def finiteNoiseSequence {Ξ : Type*} {N : ℕ} (z0 : Ξ)
    (s : Fin (N+1) → Ξ) (k : ℕ) : Ξ := if hk : k < N+1 then s ⟨k,hk⟩ else z0
lemma finiteNoiseSequence_apply {Ξ : Type*} {N : ℕ} (z0 : Ξ) (s : Fin (N+1) → Ξ)
    (k : ℕ) (hk : k ≤ N) : finiteNoiseSequence z0 s k = s ⟨k,by omega⟩ := by
  simp [finiteNoiseSequence,show k < N+1 by omega]
lemma finiteNoiseSequence_measurable {Ξ : Type*} [MeasurableSpace Ξ] {N : ℕ}
    (z0 : Ξ) (k : ℕ) : Measurable (fun s : Fin (N+1) → Ξ => finiteNoiseSequence z0 s k) := by
  unfold finiteNoiseSequence
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const
lemma rsagPath_one_measurable {D : ℕ} {Ξ W : Type*} [MeasurableSpace Ξ] [MeasurableSpace W]
    (G : Vec D → Ξ → Vec D) (hG : Measurable (Function.uncurry G))
    (P : Vec D → Vec D → ℝ → Vec D) (hP : Measurable (fun q : (Vec D × Vec D) × ℝ => P q.1.1 q.1.2 q.2))
    (α β lam : ℕ → ℝ) (x0 : Vec D) (ξ : ℕ → W → Ξ) (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Measurable (fun ω => rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hmd : Measurable (fun ω => (1-α (k+1)) •
        (rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k).2 + α (k+1) •
        (rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k).1) :=
      by convert! (ih.snd.const_smul (1-α (k+1))).add (ih.fst.const_smul (α (k+1))) using 1
    have hg : Measurable (fun ω => G ((1-α (k+1)) •
        (rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k).2 + α (k+1) •
        (rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k).1) (ξ (k+1) ω)) :=
      by convert! hG.comp (hmd.prodMk (hξ (k+1))) using 1
    simp only [rsagPath,sampleAvg_one G (k+1) (by omega)]
    convert! (hP.comp ((ih.fst.prodMk hg).prodMk measurable_const)).prodMk
      (hP.comp ((hmd.prodMk hg).prodMk measurable_const)) using 1
lemma rsagPath_projected_mem {D : ℕ} {Ξ : Type*} (G : Vec D → Ξ → Vec D)
    (Ω : Set (Vec D)) (π : Vec D → Vec D) (hπ : ∀ x, π x ∈ Ω)
    (α β lam : ℕ → ℝ) (x0 : Vec D) (hx0 : x0 ∈ Ω) (s : ℕ → Ξ) (k : ℕ) :
    (rsagPath G (fun x y c => π (x-c • y)) α β lam (fun _ => 1) x0 s k).1 ∈ Ω ∧
      (rsagPath G (fun x y c => π (x-c • y)) α β lam (fun _ => 1) x0 s k).2 ∈ Ω := by
  cases k with
  | zero => exact ⟨hx0,hx0⟩
  | succ k => exact ⟨hπ _,hπ _⟩
lemma rsagPath_one_parameter {D : ℕ} {Z Ξ : Type*} (G : Z → Vec D → Ξ → Vec D)
    (P : Vec D → Vec D → ℝ → Vec D) (α β lam : ℕ → ℝ) (x0 : Vec D)
    (z : Z) (s : ℕ → Ξ) (k : ℕ) :
    rsagPath (fun (v : Vec D) (q : Z × Ξ) => G q.1 v q.2) P α β lam (fun _ => 1) x0 (fun j => (z,s j)) k =
      rsagPath (G z) P α β lam (fun _ => 1) x0 s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rsagPath,ih,sampleAvg_one _ (k+1) (by omega)]
end PrivateAgnosticHalfspace.Gaussian


end

section
-- Solutions.ConvexERMGeometry
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ProjectedProxMap
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AcceleratedFiniteUtility
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open NonconvexAG.StochComposite
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteNoiseIntegration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteOracleMoments
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.UnitBallProjection
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def unitProjection {D : ℕ} (x : Vec D) : Vec D := (max 1 ‖x‖)⁻¹ • x
lemma unitProjection_continuous (D : ℕ) : Continuous (@unitProjection D) := by
  have hscalar : Continuous (fun x : Vec D => (max 1 ‖x‖)⁻¹) := by
    apply Continuous.inv₀ (continuous_const.max continuous_norm)
    intro x
    have : 0 < max (1 : ℝ) ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact this.ne'
  convert! hscalar.smul (continuous_id : Continuous (fun x : Vec D => x)) using 1
lemma unitProjection_norm {D : ℕ} (x : Vec D) : ‖unitProjection x‖ ≤ 1 := by
  have hm : 0 < max (1 : ℝ) ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [unitProjection,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hm.le),
    inv_mul_le_iff₀ hm]
  simpa using le_max_right (1 : ℝ) ‖x‖
lemma unitProjection_of_norm_le {D : ℕ} (x : Vec D) (hx : ‖x‖ ≤ 1) : unitProjection x = x := by
  simp [unitProjection,max_eq_left hx]
lemma unitProjection_distance {D : ℕ} (x : Vec D) (hx : 1 < ‖x‖) :
    ‖unitProjection x-x‖ = ‖x‖-1 := by
  have hp : 0 < ‖x‖ := lt_trans zero_lt_one hx
  have hi : ‖x‖⁻¹ ≤ 1 := by apply (inv_le_one₀ hp).mpr; exact hx.le
  have he : ‖x‖⁻¹ • x - x = (‖x‖⁻¹-1) • x := by rw [sub_smul,one_smul]
  rw [unitProjection,max_eq_right hx.le,he,norm_smul,
    Real.norm_eq_abs,abs_of_nonpos (by linarith : ‖x‖⁻¹-1 ≤ 0)]
  field_simp
  ring
lemma unitProjection_isProjection (D : ℕ) :
    IsProjection D (Metric.closedBall 0 1) (@unitProjection D) := by
  intro x
  refine ⟨?_,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using unitProjection_norm x
  · intro w hw
    have hw' : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    by_cases hx : ‖x‖ ≤ 1
    · rw [unitProjection_of_norm_le x hx,sub_self,norm_zero]
      exact norm_nonneg _
    · rw [unitProjection_distance x (lt_of_not_ge hx)]
      have h := norm_sub_norm_le x w
      rw [norm_sub_rev x w] at h
      linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteProjectedOptimizer
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open NonconvexAG.StochComposite
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.EuclideanVariance
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def euclideanVariance {Z : Type*} [MeasurableSpace Z] {D : ℕ}
    (μ : Measure Z) (f : Z → Vec D) : ℝ := ∫ z, ‖f z-∫ x, f x ∂μ‖^2 ∂μ
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ThresholdTranslation
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def thresholdStep (θ x : ℝ) : ℝ := if θ ≤ x then 1 else -1
lemma thresholdStep_measurable (θ : ℝ) : Measurable (thresholdStep θ) := by
  unfold thresholdStep
  exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
lemma thresholdStep_abs (θ x : ℝ) : |thresholdStep θ x| = 1 := by
  unfold thresholdStep; split_ifs <;> norm_num
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.L2Integral
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianAbsoluteSmoothing
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
local instance : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
noncomputable def smoothAbs (s b : ℝ) : ℝ := ∫ z, |b+s*z| ∂gaussianReal 0 1
noncomputable def smoothAbsSlope (s b : ℝ) : ℝ :=
  ∫ z, thresholdStep 0 (b+s*z) ∂gaussianReal 0 1
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianAbsoluteSlope
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.SmoothedRegressionLoss
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
noncomputable def smoothedLinearLoss (r : ℝ) (a : E) (y : ℝ) (v : E) : ℝ :=
  smoothAbs (r*‖a‖) (inner ℝ v a-y)
noncomputable def smoothedLinearGradient (r : ℝ) (a : E) (y : ℝ) (v : E) : E :=
  smoothAbsSlope (r*‖a‖) (inner ℝ v a-y) • a
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.SmoothedEmpiricalRegression
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
noncomputable def linearEmpirical {n : ℕ} (a : Fin n → E) (y : Fin n → ℝ) (v : E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, absoluteLinearLoss (a i) (y i) v
noncomputable def smoothedEmpirical {n : ℕ} (r : ℝ) (a : Fin n → E) (y : Fin n → ℝ) (v : E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, smoothedLinearLoss r (a i) (y i) v
noncomputable def smoothedEmpiricalGradient {n : ℕ} (r : ℝ) (a : Fin n → E) (y : Fin n → ℝ) (v : E) : E :=
  (n : ℝ)⁻¹ • ∑ i, smoothedLinearGradient r (a i) (y i) v
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.SmoothedRegressionOracle
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
noncomputable def scalarSmoothedSubgradient {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ)
    (v : Vec D) (z : ℝ) : Vec D :=
  thresholdStep 0 (inner ℝ v a-y+r*‖a‖*z) • a
lemma scalarSmoothedSubgradient_norm {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ) (v : Vec D) (z : ℝ) :
    ‖scalarSmoothedSubgradient r a y v z‖ = ‖a‖ := by
  simp only [scalarSmoothedSubgradient,norm_smul,Real.norm_eq_abs,thresholdStep_abs,one_mul]
noncomputable def batchSmoothedSubgradient {D n : ℕ} (r : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ)
    (v : Vec D) (z : Fin n → ℝ) : Vec D :=
  (n : ℝ)⁻¹ • ∑ i, scalarSmoothedSubgradient r (a i) (y i) v (z i)
lemma batchSmoothedSubgradient_measurable {D n : ℕ} (r : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) :
    Measurable (fun q : Vec D × (Fin n → ℝ) => batchSmoothedSubgradient r a y q.1 q.2) := by
  have hi (i : Fin n) : Measurable (fun q : Vec D × (Fin n → ℝ) =>
      scalarSmoothedSubgradient r (a i) (y i) q.1 (q.2 i)) :=
    by
      unfold scalarSmoothedSubgradient
      exact ((thresholdStep_measurable 0).comp (by fun_prop)).smul measurable_const
  have hsum : Measurable (fun q : Vec D × (Fin n → ℝ) =>
      ∑ i, scalarSmoothedSubgradient r (a i) (y i) q.1 (q.2 i)) :=
    Finset.measurable_sum univ (fun i _ => hi i)
  convert! hsum.const_smul (n : ℝ)⁻¹ using 1
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.UnivariateGaussianBasis
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def reindexHilbertBasis {ι κ E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (b : HilbertBasis ι ℝ E) (e : κ ≃ ι) : HilbertBasis κ ℝ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (fun j => b (e j)) = Set.range b := by
      exact e.surjective.range_comp b
    change ⊤ ≤ (Submodule.span ℝ (Set.range (fun j => b (e j)))).topologicalClosure
    rw [hr, b.dense_span])
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.StandardGaussianMoments
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.NoisyRegressionOracle
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
local instance (D : ℕ) : IsProbabilityMeasure (gaussian D) := by unfold gaussian; infer_instance
abbrev RegressionNoise (n D : ℕ) := (Fin n → ℝ) × Vec D
noncomputable def regressionNoiseLaw (n D : ℕ) : Measure (RegressionNoise n D) :=
  (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussian D)
instance regressionNoiseLaw_probability (n D : ℕ) : IsProbabilityMeasure (regressionNoiseLaw n D) := by
  unfold regressionNoiseLaw
  infer_instance
noncomputable def noisyRegressionOracle {D n : ℕ} (r τ : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ)
    (v : Vec D) (q : RegressionNoise n D) : Vec D :=
  batchSmoothedSubgradient r a y v q.1 + τ • q.2
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.SmoothedEmpiricalProperties
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
lemma linearEmpirical_bound {D n : ℕ} (hn : 0 < n) (T Y : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (hy : ∀ i, |y i| ≤ Y)
    (v : Vec D) (hv : ‖v‖ ≤ 1) : linearEmpirical a y v ≤ T+Y := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold linearEmpirical
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (T+Y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro i hi
      change |inner ℝ v (a i)-y i| ≤ T+Y
      calc
        _ ≤ |inner ℝ v (a i)|+|y i| := abs_sub _ _
        _ ≤ ‖v‖*‖a i‖+Y := add_le_add (by simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) v (a i))) (hy i)
        _ ≤ T+Y := by nlinarith [norm_nonneg v,norm_nonneg (a i),ha i]
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.AcceleratedStepsizeBound
open Finset
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def regressionStepsize (L σ : ℝ) (N : ℕ) : ℝ :=
  min (1/(2*L)) (1/(σ*N*Real.sqrt N))
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.SmoothedRegressionOptimization
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
open NonconvexAG.StochComposite
noncomputable def regressionVectorOutput {D n : ℕ} (r τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ)
    (s : Fin (n+1) → RegressionNoise n D) : Vec D :=
  xagSeq (noisyRegressionOracle r τ a y) (fun x z c => unitProjection (x-c • z))
    accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) 0
    (fun k s => finiteNoiseSequence (0,0) s k) n s
lemma regressionVectorOutput_norm {D n : ℕ} (r τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (s : Fin (n+1) → RegressionNoise n D) :
    ‖regressionVectorOutput r τ β a y s‖ ≤ 1 := by
  have h := rsagPath_projected_mem (noisyRegressionOracle r τ a y) (Metric.closedBall 0 1) unitProjection
    (fun x => (unitProjection_isProjection D x).1) accelAlpha (fun _ => β) (accelLambda β) 0 (by simp)
    (finiteNoiseSequence (0,0) s) n
  simpa only [Metric.mem_closedBall,dist_zero_right,regressionVectorOutput,xagSeq] using h.2
lemma regressionVectorOutput_expected {D n : ℕ} (hn : 0 < n) (r τ T Y σ : ℝ)
    (hr : 0 < r) (hT : 0 < T) (hσ : 0 < σ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (hy : ∀ i, |y i| ≤ Y)
    (hσbound : 2*T^2/(n : ℝ)+2*τ^2*D ≤ σ^2) (vstar : Vec D) (hvstar : ‖vstar‖ ≤ 1) :
    let L := 2*T/r
    let β := regressionStepsize L σ n
    let out := regressionVectorOutput r τ β a y
    let ν := Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D)
    Integrable (fun s => linearEmpirical a y (out s)-linearEmpirical a y vstar) ν ∧
      (∫ s, linearEmpirical a y (out s)-linearEmpirical a y vstar ∂ν) ≤
        r*T+4*L/(n : ℝ)^2+5*σ/Real.sqrt n := by
  exact PrivateAgnosticHalfspace.Gaussian.projected_regression_expected_error hn r τ T Y σ hr hT hσ a y ha hy hσbound vstar hvstar
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.CoefficientRegression
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
noncomputable def coefficientFeatures (d p : ℕ) {n : ℕ} (S : Fin n → Example d) :
    Fin n → Vec (featureDimension d p) := fun i => coefficientIsometry d p (clipped d p (S i).1)
noncomputable def coefficientLabels {d n : ℕ} (S : Fin n → Example d) : Fin n → ℝ :=
  fun i => label (S i).2
lemma coefficientFeatures_bound (d p : ℕ) {n : ℕ} (S : Fin n → Example d) (i : Fin n) :
    ‖coefficientFeatures d p S i‖ ≤ radius d p := by
  rw [coefficientFeatures,(coefficientIsometry d p).norm_map]
  exact norm_clipped_le_radius d p (S i).1
lemma coefficientLabels_abs {d n : ℕ} (S : Fin n → Example d) (i : Fin n) :
    |coefficientLabels S i| = 1 := by
  unfold coefficientLabels label
  split_ifs <;> norm_num
lemma coefficientFeatures_measurable (d p n : ℕ) :
    Measurable (fun S : Fin n → Example d => coefficientFeatures d p S) := by
  apply measurable_pi_lambda
  intro i
  exact (coefficientIsometry d p).continuous.measurable.comp
    ((continuous_clipped d p).measurable.comp (measurable_pi_apply i).fst)
lemma coefficientLabels_measurable (d n : ℕ) :
    Measurable (fun S : Fin n → Example d => coefficientLabels S) := by
  apply measurable_pi_lambda
  intro i
  unfold coefficientLabels label
  exact measurable_const.ite (measurableSet_eq_fun (measurable_pi_apply i).snd measurable_const) measurable_const
lemma linearEmpirical_coefficient (d p : ℕ) {n : ℕ} (S : Fin n → Example d) (v : Coeff d p) :
    linearEmpirical (coefficientFeatures d p S) (coefficientLabels S) (coefficientIsometry d p v) =
      empiricalLoss d p S v := by
  unfold linearEmpirical absoluteLinearLoss coefficientFeatures coefficientLabels empiricalLoss score
  simp_rw [(coefficientIsometry d p).inner_map_map]
  ring
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.VariableRegressionOracle
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
lemma noisyRegressionOracle_variable_measurable {Z : Type*} [MeasurableSpace Z] {D n : ℕ}
    (r τ : ℝ) (a : Z → Fin n → Vec D) (y : Z → Fin n → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) (hy : ∀ i, Measurable (fun z => y z i)) :
    Measurable (fun q : Vec D × (Z × RegressionNoise n D) =>
      noisyRegressionOracle r τ (a q.2.1) (y q.2.1) q.1 q.2.2) := by
  have hi (i : Fin n) : Measurable (fun q : Vec D × (Z × RegressionNoise n D) =>
      scalarSmoothedSubgradient r (a q.2.1 i) (y q.2.1 i) q.1 (q.2.2.1 i)) := by
    have ha' : Measurable (fun q : Vec D × (Z × RegressionNoise n D) => a q.2.1 i) :=
      (ha i).comp measurable_snd.fst
    have hy' : Measurable (fun q : Vec D × (Z × RegressionNoise n D) => y q.2.1 i) :=
      (hy i).comp measurable_snd.fst
    have harg : Measurable (fun q : Vec D × (Z × RegressionNoise n D) =>
        inner ℝ q.1 (a q.2.1 i)-y q.2.1 i+r*‖a q.2.1 i‖*q.2.2.1 i) := by
      convert! ((measurable_fst.inner ha').sub hy').add
        ((ha'.norm.const_mul r).mul ((measurable_pi_apply i).comp measurable_snd.snd.fst)) using 1
    convert! ((thresholdStep_measurable 0).comp harg).smul ha' using 1
  have hs := Finset.measurable_sum univ (fun i _ => hi i)
  convert! (hs.const_smul (n : ℝ)⁻¹).add (measurable_snd.snd.snd.const_smul τ) using 1
lemma regressionVectorOutput_variable_measurable {Z : Type*} [MeasurableSpace Z] {D n : ℕ}
    (r τ β : ℝ) (a : Z → Fin n → Vec D) (y : Z → Fin n → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) (hy : ∀ i, Measurable (fun z => y z i)) :
    Measurable (fun q : Z × (Fin (n+1) → RegressionNoise n D) =>
      regressionVectorOutput r τ β (a q.1) (y q.1) q.2) := by
  let G := fun (v : Vec D) (q : Z × RegressionNoise n D) => noisyRegressionOracle r τ (a q.1) (y q.1) v q.2
  let ξ := fun k (q : Z × (Fin (n+1) → RegressionNoise n D)) => (q.1,finiteNoiseSequence (0,0) q.2 k)
  let P := fun (x z : Vec D) (c : ℝ) => unitProjection (x-c • z)
  have hP : Measurable (fun q : (Vec D × Vec D) × ℝ => P q.1.1 q.1.2 q.2) :=
    (unitProjection_continuous D).measurable.comp (by fun_prop)
  have hξ (k) : Measurable (ξ k) := measurable_fst.prodMk
    ((finiteNoiseSequence_measurable (N := n) (0,0) k).comp measurable_snd)
  have hG : Measurable (Function.uncurry G) := noisyRegressionOracle_variable_measurable r τ a y ha hy
  have h := rsagPath_one_measurable G hG P hP accelAlpha (fun _ => β) (accelLambda β) 0 ξ hξ n
  convert! h.snd using 1
  funext q
  have he := rsagPath_one_parameter (fun z => noisyRegressionOracle r τ (a z) (y z))
    P accelAlpha (fun _ => β) (accelLambda β) 0 q.1 (finiteNoiseSequence (0,0) q.2) n
  exact (congrArg Prod.snd he).symm
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry

end

section
-- Solutions.RegressionPrivacyParameters
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def regressionTau (T : ℝ) (n : ℕ) (ε δ : ℝ) : ℝ :=
  8*T*Real.sqrt (Real.log (1/δ)/n)/ε
noncomputable def regressionSigma (T : ℝ) (D n : ℕ) (ε δ : ℝ) : ℝ :=
  20*T*Real.sqrt ((D : ℝ)*Real.log (1/δ))/(Real.sqrt n*ε)
lemma privacyLog_lower (δ : ℝ) (hδ : 0 < δ ∧ δ ≤ 1/2) : 1/2 ≤ Real.log (1/δ) := by
  have h := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hδ.1)
  simp only [one_div,inv_inv] at h
  simpa only [one_div] using (show (1:ℝ)/2 ≤ Real.log δ⁻¹ by linarith [hδ.2])
lemma regressionTau_sq (T : ℝ) (n : ℕ) (hn : 0 < n) (ε δ : ℝ) (hδ : 0 < δ ∧ δ ≤ 1/2) :
    regressionTau T n ε δ ^2 = 64*T^2*Real.log (1/δ)/((n : ℝ)*ε^2) := by
  have hl : 0 ≤ Real.log (1/δ) := by linarith [privacyLog_lower δ hδ]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold regressionTau
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (div_nonneg hl (Nat.cast_nonneg n))]
  field_simp
  ring
lemma regressionSigma_sq (T : ℝ) (D n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hδ : 0 < δ ∧ δ ≤ 1/2) :
    regressionSigma T D n ε δ ^2 = 400*T^2*((D : ℝ)*Real.log (1/δ))/((n : ℝ)*ε^2) := by
  have hl : 0 ≤ Real.log (1/δ) := by linarith [privacyLog_lower δ hδ]
  unfold regressionSigma
  rw [div_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg D) hl),
    Real.sq_sqrt (Nat.cast_nonneg n)]
  ring
lemma regressionTau_pos (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ ∧ δ ≤ 1/2) : 0 < regressionTau T n ε δ := by
  have hl : 0 < Real.log (1/δ) := by linarith [privacyLog_lower δ hδ]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold regressionTau
  positivity
lemma regressionSigma_pos (T : ℝ) (hT : 0 < T) (D n : ℕ) (hD : 1 ≤ D) (hn : 0 < n)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ ∧ δ ≤ 1/2) : 0 < regressionSigma T D n ε δ := by
  have hl : 0 < Real.log (1/δ) := by linarith [privacyLog_lower δ hδ]
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold regressionSigma
  positivity
lemma regressionSigma_variance (T : ℝ) (D n : ℕ) (hD : 1 ≤ D) (hn : 0 < n)
    (ε δ : ℝ) (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) :
    2*T^2/(n : ℝ)+2*regressionTau T n ε δ ^2*D ≤ regressionSigma T D n ε δ ^2 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hl := privacyLog_lower δ hδ
  have hDl : 1/2 ≤ (D : ℝ)*Real.log (1/δ) := by nlinarith
  have he : ε^2 ≤ 1/4 := by nlinarith [hε.1,hε.2]
  rw [regressionTau_sq T n hn ε δ hδ,regressionSigma_sq T D n hn ε δ hδ]
  have heq : 2*T^2/(n : ℝ)+2*(64*T^2*Real.log (1/δ)/((n : ℝ)*ε^2))*D =
      (2*T^2*ε^2+128*T^2*((D : ℝ)*Real.log (1/δ)))/((n : ℝ)*ε^2) := by
    field_simp [hnr.ne',hε.1.ne']
    ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnum : 0 ≤ 272*((D : ℝ)*Real.log (1/δ))-2*ε^2 := by linarith
  nlinarith [mul_nonneg (sq_nonneg T) hnum]
lemma regressionSigma_rate (T : ℝ) (n D : ℕ) (hn : 0 < n) (ε δ : ℝ) :
    5*regressionSigma T D n ε δ/Real.sqrt n =
      100*T*Real.sqrt ((D : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  by_cases he : ε = 0
  · simp [he,regressionSigma]
  · unfold regressionSigma
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
    field_simp [he,hs,hn0]
    nlinarith [congrArg (fun x : ℝ => 100*T*Real.sqrt ((D : ℝ)*Real.log (1/δ))*x) hsq]
lemma regression_parameter_rate (T : ℝ) (hT : 0 ≤ T) (n D : ℕ) (hn : 0 < n) (hD : 1 ≤ D)
    (ε δ : ℝ) (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) :
    ((n : ℝ)⁻¹)*T + 4*(2*T/((n : ℝ)⁻¹))/(n : ℝ)^2 +
      5*regressionSigma T D n ε δ/Real.sqrt n ≤
        120*T*Real.sqrt ((D : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hl := privacyLog_lower δ hδ
  have hDl : 1/2 ≤ (D : ℝ)*Real.log (1/δ) := by nlinarith
  have hroot : ε ≤ Real.sqrt ((D : ℝ)*Real.log (1/δ)) := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ (D : ℝ)*Real.log (1/δ))
    have hs0 := Real.sqrt_nonneg ((D : ℝ)*Real.log (1/δ))
    nlinarith [hε.1,hε.2]
  have hq : T/(n : ℝ) ≤ T*Real.sqrt ((D : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) := by
    apply (div_le_div_iff₀ hnr (mul_pos hnr hε.1)).mpr
    nlinarith [mul_nonneg (mul_nonneg hT hnr.le) (sub_nonneg.mpr hroot)]
  have he : ((n : ℝ)⁻¹)*T+4*(2*T/((n : ℝ)⁻¹))/(n : ℝ)^2 = 9*(T/n) := by
    field_simp [hnr.ne']
    ring
  rw [he,regressionSigma_rate T n D hn ε δ]
  have hq0 : 0 ≤ T*Real.sqrt ((D : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) :=
    div_nonneg (mul_nonneg hT (Real.sqrt_nonneg _)) (mul_pos hnr hε.1).le
  calc
    _ = 9*(T/n)+100*(T*Real.sqrt ((D : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)) := by ring
    _ ≤ 120*(T*Real.sqrt ((D : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)) := by nlinarith
    _ = _ := by ring
lemma regression_noise_calibration (T : ℝ) (n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ ∧ δ ≤ 1/2) :
    32*T^2*Real.log (1/δ) ≤ (n : ℝ)*ε^2*regressionTau T n ε δ ^2 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [regressionTau_sq T n hn ε δ hδ]
  have he : (n : ℝ)*ε^2*(64*T^2*Real.log (1/δ)/((n : ℝ)*ε^2)) = 64*T^2*Real.log (1/δ) := by
    field_simp
  rw [he]
  have hl : 0 ≤ Real.log (1/δ) := by linarith [privacyLog_lower δ hδ]
  nlinarith [mul_nonneg (sq_nonneg T) hl]
end PrivateAgnosticHalfspace.Gaussian

end

section
-- Solutions.ParametricMeasureMap
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma measurable_parametric_measure_map {Z Ξ E : Type*}
    [MeasurableSpace Z] [MeasurableSpace Ξ] [MeasurableSpace E]
    (μ : Measure Ξ) [SFinite μ] (f : Z × Ξ → E) (hf : Measurable f) :
    Measurable (fun z => μ.map (fun s => f (z,s))) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hi : Measurable (fun q : Z × Ξ => (f ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) q) :=
    measurable_const.indicator (hA.preimage hf)
  have hm : Measurable (fun z : Z => ∫⁻ s : Ξ, (f ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) (z,s) ∂μ) := by
    apply Measurable.lintegral_prod_right
    convert! hi using 1
  convert! hm using 1
  funext z
  have hz : Measurable (fun s : Ξ => f (z,s)) := by
    convert! hf.comp (measurable_const.prodMk measurable_id) using 1
  rw [Measure.map_apply hz hA]
  symm
  have hAz : MeasurableSet {s : Ξ | f (z,s) ∈ A} := hA.preimage hz
  convert! lintegral_indicator_one hAz using 1
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ConcreteRegressionOptimizer
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
noncomputable def optimizerStep (d p n : ℕ) (ε δ : ℝ) : ℝ :=
  regressionStepsize (2*radius d p/((n : ℝ)⁻¹))
    (regressionSigma (radius d p) (featureDimension d p) n ε δ) n
noncomputable def optimizerDraw (d p n : ℕ) (ε δ : ℝ) (S : Fin n → Example d)
    (s : Fin (n+1) → RegressionNoise n (featureDimension d p)) : UnitBall d p :=
  ⟨(coefficientIsometry d p).symm
    (regressionVectorOutput ((n : ℝ)⁻¹) (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ)
      (coefficientFeatures d p S) (coefficientLabels S) s),by
    rw [(coefficientIsometry d p).symm.norm_map]
    exact regressionVectorOutput_norm _ _ _ _ _ _⟩
lemma optimizerDraw_measurable_joint (d p n : ℕ) (ε δ : ℝ) :
    Measurable (fun q : (Fin n → Example d) × (Fin (n+1) → RegressionNoise n (featureDimension d p)) =>
      optimizerDraw d p n ε δ q.1 q.2) := by
  have hv := regressionVectorOutput_variable_measurable ((n : ℝ)⁻¹)
    (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ)
    (coefficientFeatures d p) coefficientLabels
    (fun i => (measurable_pi_apply i).comp (coefficientFeatures_measurable d p n))
    (fun i => (measurable_pi_apply i).comp (coefficientLabels_measurable d n))
  exact ((coefficientIsometry d p).symm.continuous.measurable.comp hv).subtype_mk
lemma optimizerDraw_measurable (d p n : ℕ) (ε δ : ℝ) (S : Fin n → Example d) :
    Measurable (optimizerDraw d p n ε δ S) := by
  convert! (optimizerDraw_measurable_joint d p n ε δ).comp
    (measurable_const.prodMk measurable_id) using 1
noncomputable def concreteOptimizer : Optimizer := fun d p n ε δ S =>
  ⟨(Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n (featureDimension d p))).map
      (optimizerDraw d p n ε δ S),
    Measure.isProbabilityMeasure_map (optimizerDraw_measurable d p n ε δ S).aemeasurable⟩
lemma concreteOptimizer_measurable (d p n : ℕ) (ε δ : ℝ) :
    Measurable (fun S => (concreteOptimizer d p n ε δ S : Measure (UnitBall d p))) :=
  measurable_parametric_measure_map _ _ (optimizerDraw_measurable_joint d p n ε δ)
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ConcreteOptimizerUtility
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
lemma empiricalLoss_continuous (d p : ℕ) {n : ℕ} (S : Fin n → Example d) :
    Continuous (empiricalLoss d p S) := by
  unfold empiricalLoss score
  apply Continuous.div_const
  exact continuous_finsetSum _ (fun i _ => by fun_prop)
lemma optimizerDraw_vector (d p n : ℕ) (ε δ : ℝ) (S : Fin n → Example d)
    (s : Fin (n+1) → RegressionNoise n (featureDimension d p)) :
    coefficientIsometry d p (optimizerDraw d p n ε δ S s).val =
      regressionVectorOutput ((n : ℝ)⁻¹) (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ)
        (coefficientFeatures d p S) (coefficientLabels S) s :=
  (coefficientIsometry d p).apply_symm_apply _
lemma concreteOptimizer_regret (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (S : Fin n → Example d) (vstar : UnitBall d p) :
    Integrable (fun v : UnitBall d p => empiricalLoss d p S v.val-empiricalLoss d p S vstar.val)
      (concreteOptimizer d p n ε δ S : Measure (UnitBall d p)) ∧
    (∫ v : UnitBall d p, empiricalLoss d p S v.val-empiricalLoss d p S vstar.val
      ∂(concreteOptimizer d p n ε δ S : Measure (UnitBall d p))) ≤
        120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) := by
  let D := featureDimension d p
  let T := radius d p
  let r := (n : ℝ)⁻¹
  let τ := regressionTau T n ε δ
  let σ := regressionSigma T D n ε δ
  let a := coefficientFeatures d p S
  let y := coefficientLabels S
  let out := optimizerDraw d p n ε δ S
  let ν := Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D)
  let f := fun v : UnitBall d p => empiricalLoss d p S v.val-empiricalLoss d p S vstar.val
  have hT : 0 < T := radius_pos d p
  have hD : 1 ≤ D := featureDimension_pos d p
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := inv_pos.mpr hnr
  have hσ : 0 < σ := regressionSigma_pos T hT D n hD hn ε δ hε.1 hδ
  have ha : ∀ i, ‖a i‖ ≤ T := coefficientFeatures_bound d p S
  have hy : ∀ i, |y i| ≤ 1 := fun i => (coefficientLabels_abs S i).le
  have hvstar : ‖coefficientIsometry d p vstar.val‖ ≤ 1 := by
    rw [(coefficientIsometry d p).norm_map]
    exact vstar.property
  have hi := regressionVectorOutput_expected hn r τ T 1 σ hr hT hσ a y ha hy
    (regressionSigma_variance T D n hD hn ε δ hε hδ) (coefficientIsometry d p vstar.val) hvstar
  let H := fun s : Fin (n+1) → RegressionNoise n D =>
    linearEmpirical a y (regressionVectorOutput r τ (optimizerStep d p n ε δ) a y s)-
      linearEmpirical a y (coefficientIsometry d p vstar.val)
  have he (s) : f (out s) = H s := by
    dsimp [f,H,out,a,y]
    rw [← linearEmpirical_coefficient d p S (optimizerDraw d p n ε δ S s).val,
      ← linearEmpirical_coefficient d p S vstar.val,optimizerDraw_vector]
  have hf : Measurable f := ((empiricalLoss_continuous d p S).measurable.comp measurable_subtype_coe).sub measurable_const
  have hout : Measurable out := optimizerDraw_measurable d p n ε δ S
  have hH : Integrable H ν := hi.1
  have hiOut : Integrable (f ∘ out) ν := hH.congr (ae_of_all _ (fun s => (he s).symm))
  have hmeas : (concreteOptimizer d p n ε δ S : Measure (UnitBall d p)) = ν.map out := rfl
  rw [hmeas]
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hout.aemeasurable).mpr hiOut,?_⟩
  rw [integral_map hout.aemeasurable hf.aestronglyMeasurable]
  have hint : (∫ s, f (out s) ∂ν) = ∫ s, H s ∂ν := integral_congr_ae (ae_of_all _ he)
  change (∫ s, f (out s) ∂ν) ≤ _
  rw [hint]
  have hstat : (∫ s, H s ∂ν) ≤ r*T+4*(2*T/r)/(n : ℝ)^2+5*σ/Real.sqrt n := hi.2
  exact hstat.trans (regression_parameter_rate T hT.le n D hn hD ε δ hε hδ)
lemma empiricalLoss_minimum_attained (d p : ℕ) {n : ℕ} (S : Fin n → Example d) :
    ∃ v : UnitBall d p, empiricalLoss d p S v.val =
      sInf (empiricalLoss d p S '' Metric.closedBall 0 1) := by
  obtain ⟨v,hv,hmin⟩ := (isCompact_closedBall (0 : Coeff d p) 1).exists_isMinOn
    (show (Metric.closedBall (0 : Coeff d p) 1).Nonempty from ⟨0,by simp⟩)
    (empiricalLoss_continuous d p S).continuousOn
  have hv' : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  refine ⟨⟨v,hv'⟩,?_⟩
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨v,hv,rfl⟩,?_⟩
  rintro z ⟨w,hw,rfl⟩
  exact hmin hw
lemma concreteOptimizer_excess (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) (S : Fin n → Example d) :
    Integrable (fun v : UnitBall d p => empiricalLoss d p S v.val-
      sInf (empiricalLoss d p S '' Metric.closedBall 0 1))
      (concreteOptimizer d p n ε δ S : Measure (UnitBall d p)) ∧
    (∫ v : UnitBall d p, empiricalLoss d p S v.val-sInf (empiricalLoss d p S '' Metric.closedBall 0 1)
      ∂(concreteOptimizer d p n ε δ S : Measure (UnitBall d p))) ≤
        120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) := by
  obtain ⟨v,hv⟩ := empiricalLoss_minimum_attained d p S
  simpa only [hv] using concreteOptimizer_regret d p n hn ε δ hε hδ S v
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.MidpointGrid
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def gridThreshold (M : ℕ) (l : Fin M) : ℝ := -1+(2*(l.val : ℝ)+1)/M
lemma midpoint_grid_pointwise (M : ℕ) (hM : 0 < M) (z : ℝ) (y : Bool) :
    ((∑ l : Fin M, if sign (z-gridThreshold M l) ≠ y then (1 : ℝ) else 0)/M) ≤
      |z-label y|/2 + 1/(2*M) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  classical
  cases y with
  | false =>
    let A : Finset (Fin M) := univ.filter (fun l => gridThreshold M l ≤ z)
    have he : (∑ l : Fin M, if sign (z-gridThreshold M l) ≠ false then (1 : ℝ) else 0) = (A.card : ℝ) := by
      simp only [sign, ne_eq, Bool.decide_eq_false, not_not, sub_nonneg]
      rw [← Finset.sum_filter]
      simp [A]
    rw [he]
    by_cases ha : A.Nonempty
    · let l := A.max' ha
      have hlA : l ∈ A := A.max'_mem ha
      have hl : gridThreshold M l ≤ z := (mem_filter.mp hlA).2
      have hcard : A.card ≤ l.val+1 := by
        apply (card_le_card (show A ⊆ Iic l from fun j hj => ?_)).trans
        · simpa using (Finset.card_Iic l).le
        · exact (mem_Iic.mpr (A.le_max' j hj))
      have hcr : (A.card : ℝ) ≤ l.val+1 := by exact_mod_cast hcard
      have hmid : (2*(l.val : ℝ)+1) ≤ (z+1)*M := by
        dsimp [gridThreshold] at hl
        apply (div_le_iff₀ hMr).mp
        linarith
      simp only [label, Bool.false_eq_true, ite_false]
      rw [div_le_iff₀ hMr]
      have hab := le_abs_self (z-(-1))
      field_simp
      nlinarith
    · have hz : A.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp ha)
      rw [hz]
      simp only [Nat.cast_zero,zero_div]
      positivity
  | true =>
    let A : Finset (Fin M) := univ.filter (fun l => z < gridThreshold M l)
    have he : (∑ l : Fin M, if sign (z-gridThreshold M l) ≠ true then (1 : ℝ) else 0) = (A.card : ℝ) := by
      have hs (l : Fin M) : (sign (z-gridThreshold M l) ≠ true) ↔ z < gridThreshold M l := by
        simp [sign, not_le, sub_neg]
      simp_rw [hs]
      rw [← Finset.sum_filter]
      simp [A]
    rw [he]
    by_cases ha : A.Nonempty
    · let l := A.min' ha
      have hlA : l ∈ A := A.min'_mem ha
      have hl : z < gridThreshold M l := (mem_filter.mp hlA).2
      have hcard : A.card ≤ M-l.val := by
        apply (card_le_card (show A ⊆ Ici l from fun j hj => ?_)).trans
        · simpa using (Finset.card_Ici l).le
        · exact mem_Ici.mpr (A.min'_le j hj)
      have hcr : (A.card : ℝ) ≤ (M : ℝ)-l.val := by
        have hh : (A.card : ℝ) ≤ ((M-l.val : ℕ) : ℝ) := by exact_mod_cast hcard
        rw [Nat.cast_sub l.isLt.le] at hh
        exact hh
      have hmid : (z+1)*M < 2*(l.val : ℝ)+1 := by
        dsimp [gridThreshold] at hl
        apply (lt_div_iff₀ hMr).mp
        linarith
      simp only [label, ite_true]
      rw [div_le_iff₀ hMr]
      have hab := neg_le_abs (z-1)
      field_simp
      nlinarith
    · have hz : A.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp ha)
      rw [hz]
      simp only [Nat.cast_zero,zero_div]
      positivity
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GridClassification
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal NNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma sign_measurable_grid : Measurable (sign : ℝ → Bool) := by
  apply measurable_to_bool
  have he : sign ⁻¹' {true} = Ici (0 : ℝ) := by ext z; simp [sign]
  rw [he]
  exact measurableSet_Ici
lemma classification_error_integrable {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (h : X → Bool) (hh : Measurable h) :
    Integrable (fun z => if h z.1 ≠ z.2 then (1 : ℝ) else 0) P := by
  have hs : MeasurableSet {z : X × Bool | h z.1 ≠ z.2} :=
    (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl
  convert! (integrable_const (μ := P) (1 : ℝ)).indicator hs using 1
  funext z
  simp only [indicator_apply,mem_setOf_eq]
lemma classification_error_integral {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (h : X → Bool) (hh : Measurable h) :
    (∫ z, if h z.1 ≠ z.2 then (1 : ℝ) else 0 ∂P) = error P h := by
  have hs : MeasurableSet {z : X × Bool | h z.1 ≠ z.2} :=
    (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl
  have he : (fun z : X × Bool => if h z.1 ≠ z.2 then (1 : ℝ) else 0) =
      {z : X × Bool | h z.1 ≠ z.2}.indicator (fun _ => (1 : ℝ)) := by
    funext z
    simp only [indicator_apply,mem_setOf_eq]
  rw [he,integral_indicator hs,integral_const]
  simp [error]
lemma midpoint_grid_population_average {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (s : X → ℝ) (hs : Measurable s)
    (M : ℕ) (hM : 0 < M)
    (hi : Integrable (fun z : X × Bool => |s z.1-label z.2|) P) :
    (∑ l : Fin M, error P (fun x => sign (s x-gridThreshold M l)))/(M : ℝ) ≤
      (∫ z, |s z.1-label z.2| ∂P)/2 + 1/(2*M) := by
  have hh (l : Fin M) : Measurable (fun x => sign (s x-gridThreshold M l)) :=
    sign_measurable_grid.comp (hs.sub_const _)
  have hint (l : Fin M) := classification_error_integrable P _ (hh l)
  have hleft : Integrable (fun z : X × Bool =>
      (∑ l : Fin M, if sign (s z.1-gridThreshold M l) ≠ z.2 then (1 : ℝ) else 0)/(M : ℝ)) P :=
    (integrable_finsetSum univ (fun l _ => hint l)).div_const _
  have hright : Integrable (fun z : X × Bool => |s z.1-label z.2|/2+1/(2*M)) P :=
    (hi.div_const 2).add (integrable_const _)
  have h := integral_mono hleft hright (fun z => midpoint_grid_pointwise M hM (s z.1) z.2)
  change (∫ z, (∑ l : Fin M, if sign (s z.1-gridThreshold M l) ≠ z.2 then (1 : ℝ) else 0)/(M : ℝ) ∂P) ≤
    (∫ z, |s z.1-label z.2|/2+1/(2*M) ∂P) at h
  rw [integral_div,integral_finsetSum univ (fun l _ => hint l),integral_add (hi.div_const 2) (integrable_const _),
    integral_div,integral_const] at h
  simp only [classification_error_integral P _ (hh _),probReal_univ,one_smul] at h
  exact h
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.PopulationRegression
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
lemma measurable_label : Measurable label := by
  unfold label
  exact measurable_const.ite (measurableSet_singleton true) measurable_const
lemma label_abs (y : Bool) : |label y| = 1 := by cases y <;> norm_num [label]
lemma score_measurable_joint (d p : ℕ) : Measurable (fun q : Coeff d p × Vec d => score d p q.1 q.2) := by
  exact measurable_fst.inner ((continuous_clipped d p).measurable.comp measurable_snd)
lemma score_abs_bound (d p : ℕ) (v : Coeff d p) (x : Vec d) :
    |score d p v x| ≤ ‖v‖*radius d p := by
  apply (show |score d p v x| ≤ ‖v‖*‖clipped d p x‖ from by simpa only [score,Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) v (clipped d p x))).trans
  exact mul_le_mul_of_nonneg_left (norm_clipped_le_radius d p x) (norm_nonneg _)
lemma loss_abs_bound (d p : ℕ) (v : Coeff d p) (z : Example d) :
    |score d p v z.1-label z.2| ≤ ‖v‖*radius d p+1 := by
  exact (abs_sub _ _).trans (by rw [label_abs]; exact add_le_add (score_abs_bound d p v z.1) le_rfl)
lemma loss_integrable (d p : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P] (v : Coeff d p) :
    Integrable (fun z : Example d => |score d p v z.1-label z.2|) P := by
  have hm : Measurable (fun z : Example d => |score d p v z.1-label z.2|) :=
    (((score_measurable_joint d p).comp (measurable_const.prodMk measurable_fst)).sub
      (measurable_label.comp measurable_snd)).abs
  apply (integrable_const (‖v‖*radius d p+1)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,abs_abs] using loss_abs_bound d p v z)
lemma loss_difference_bound (d p : ℕ) (v w : Coeff d p) (z : Example d) :
    abs (abs (score d p v z.1-label z.2)-abs (score d p w z.1-label z.2)) ≤ ‖v-w‖*radius d p := by
  calc
    _ ≤ |(score d p v z.1-label z.2)-(score d p w z.1-label z.2)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |score d p (v-w) z.1| := by unfold score; rw [inner_sub_left]; congr 1; ring
    _ ≤ _ := score_abs_bound d p (v-w) z.1
lemma populationLoss_lipschitz (d p : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P] :
    LipschitzWith (radius d p).toNNReal (populationLoss d p P) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq,dist_eq_norm,Real.coe_toNNReal _ (radius_pos d p).le]
  have he : populationLoss d p P v-populationLoss d p P w =
      ∫ z, |score d p v z.1-label z.2|-|score d p w z.1-label z.2| ∂P := by
    rw [integral_sub (loss_integrable d p P v) (loss_integrable d p P w)]
    rfl
  rw [he,← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun z : Example d => |score d p v z.1-label z.2|-|score d p w z.1-label z.2|)
    (C := ‖v-w‖*radius d p) (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using loss_difference_bound d p v w z))
  simpa only [probReal_univ,mul_one,mul_comm,one_mul] using h
lemma populationLoss_nonneg (d p : ℕ) (P : Measure (Example d)) (v : Coeff d p) :
    0 ≤ populationLoss d p P v := integral_nonneg (fun z => abs_nonneg _)
lemma populationLoss_unit_bound (d p : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P]
    (v : Coeff d p) (hv : ‖v‖ ≤ 1) : populationLoss d p P v ≤ radius d p+1 := by
  have h := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun z : Example d => |score d p v z.1-label z.2|) (C := radius d p+1)
    (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (loss_abs_bound d p v z).trans (by nlinarith [radius_pos d p])))
  simp only [probReal_univ,mul_one,Real.norm_eq_abs] at h
  exact (le_abs_self (populationLoss d p P v)).trans h
lemma populationLoss_minimum_attained (d p : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P] :
    ∃ v : UnitBall d p, populationLoss d p P v.val = minimumLoss d p P := by
  obtain ⟨v,hv,hmin⟩ := (isCompact_closedBall (0 : Coeff d p) 1).exists_isMinOn
    (show (Metric.closedBall (0 : Coeff d p) 1).Nonempty from ⟨0,by simp⟩)
    (populationLoss_lipschitz d p P).continuous.continuousOn
  have hv' : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  refine ⟨⟨v,hv'⟩,?_⟩
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨v,hv,rfl⟩,?_⟩
  rintro z ⟨w,hw,rfl⟩
  exact hmin hw
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.EmpiricalPopulationMean
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
lemma empiricalLoss_unit_bound (d p n : ℕ) (hn : 0 < n) (S : Fin n → Example d) (v : UnitBall d p) :
    empiricalLoss d p S v.val ≤ radius d p+1 := by
  rw [← linearEmpirical_coefficient d p S v.val]
  apply linearEmpirical_bound hn (radius d p) 1 _ _ (coefficientFeatures_bound d p S)
    (fun i => (coefficientLabels_abs S i).le)
  rw [(coefficientIsometry d p).norm_map]
  exact v.property
lemma empiricalLoss_nonneg (d p : ℕ) {n : ℕ} (S : Fin n → Example d) (v : Coeff d p) :
    0 ≤ empiricalLoss d p S v := div_nonneg (sum_nonneg (fun i _ => abs_nonneg _)) (Nat.cast_nonneg n)
lemma empiricalLoss_iid_integrable (d p n : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P]
    (v : Coeff d p) : Integrable (fun S : Fin n → Example d => empiricalLoss d p S v) (Measure.pi (fun _ => P)) := by
  have hi (i : Fin n) : Integrable (fun S : Fin n → Example d => |score d p v (S i).1-label (S i).2|)
      (Measure.pi (fun _ : Fin n => P)) := by
    convert! (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable (loss_integrable d p P v) using 1
  exact (integrable_finsetSum univ (fun i _ => hi i)).div_const _
lemma empiricalLoss_iid_mean (d p n : ℕ) (hn : 0 < n) (P : Measure (Example d)) [IsProbabilityMeasure P]
    (v : Coeff d p) : (∫ S : Fin n → Example d, empiricalLoss d p S v ∂Measure.pi (fun _ => P)) =
      populationLoss d p P v := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hi (i : Fin n) : Integrable (fun S : Fin n → Example d => |score d p v (S i).1-label (S i).2|)
      (Measure.pi (fun _ : Fin n => P)) := by
    convert! (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable (loss_integrable d p P v) using 1
  have he (i : Fin n) : (∫ S : Fin n → Example d, |score d p v (S i).1-label (S i).2| ∂Measure.pi (fun _ => P)) =
      populationLoss d p P v := by
    have hp := measurePreserving_eval (fun _ : Fin n => P) i
    rw [← integral_map (f := fun z : Example d => |score d p v z.1-label z.2|)
      hp.measurable.aemeasurable (by rw [hp.map_eq]; exact (loss_integrable d p P v).aestronglyMeasurable),hp.map_eq]
    rfl
  unfold empiricalLoss
  rw [integral_div,integral_finsetSum univ (fun i _ => hi i)]
  simp_rw [he]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianDensity
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace PrivateAgnosticHalfspace.Gaussian
lemma lintegral_fin_prod {n : ℕ} {Y : Fin n → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Y i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : Y 0 × ((i : Fin n) → Y i.succ),
          f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
          ∂(μ 0).prod (Measure.pi (fun i => μ i.succ)) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
        have hh := lintegral_prod_mul (μ := μ 0) (ν := Measure.pi (fun i : Fin n => μ i.succ))
          (f := f 0) (g := fun x => ∏ i : Fin n, f i.succ (x i))
          (hf 0).aemeasurable
          ((Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable)
        rw [ih _ _ (fun i => hf i.succ)] at hh
        exact hh
      _ = _ := by rw [Fin.prod_univ_succ]

lemma lintegral_fintype_prod {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Y i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ _ (fun i => hf _)

lemma pi_withDensity {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Y i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hfin : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  letI (i : ι) : SigmaFinite ((μ i).withDensity (f i)) :=
    SigmaFinite.withDensity_of_ne_top' (hfin i)
  apply Measure.pi_eq
  intro s hs
  have hm : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hm, ← lintegral_indicator hm]
  calc
    _ = ∫⁻ x, ∏ i, (s i).indicator (f i) (x i) ∂Measure.pi μ := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ Set.univ.pi s
      · have hx' : ∀ i, x i ∈ s i := by simpa using hx
        simp only [Set.indicator_of_mem hx]
        apply Finset.prod_congr rfl
        intro i _
        rw [Set.indicator_of_mem (hx' i)]
      · rw [Set.indicator_of_notMem hx]
        have hbad : ∃ i, x i ∉ s i := by simpa using hx
        obtain ⟨i,hi⟩ := hbad
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact Set.indicator_of_notMem hi _
    _ = ∏ i, ∫⁻ x, (s i).indicator (f i) x ∂μ i := lintegral_fintype_prod _ _ (fun i => (hf i).indicator (hs i))
    _ = ∏ i, (μ i).withDensity (f i) (s i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext U hU
  rw [Measure.map_apply e.measurable hU, withDensity_apply _ (e.measurable hU),
    withDensity_apply _ hU, ← lintegral_indicator (e.measurable hU), ← lintegral_indicator hU]
  have hmeas : Measurable (U.indicator (fun y => f (e.symm y))) := by
    simpa only [Function.comp_def] using (hf.comp e.symm.measurable).indicator hU
  rw [lintegral_map hmeas e.measurable]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ U <;> simp [Set.indicator, hx]
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_eq_productDensity (d : ℕ) :
    gaussian d = (volume : Measure (Vec d)).withDensity (fun x =>
      ∏ i : Fin d, gaussianPDF 0 1 (x i)) := by
  have heach : (fun _ : Fin d => gaussianReal 0 1) =
      (fun _ : Fin d => (volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    funext i
    exact gaussianReal_of_var_ne_zero 0 (by norm_num)
  rw [gaussian, ← map_pi_eq_stdGaussian, heach,
    pi_withDensity (fun _ : Fin d => (volume : Measure ℝ))
      (fun _ => gaussianPDF 0 1) (fun _ => measurable_gaussianPDF _ _)
      (fun _ _ => gaussianPDF_lt_top.ne)]
  let e := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hprod : Measurable (fun x : Fin d → ℝ => ∏ i, gaussianPDF 0 1 (x i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF _ _).comp (measurable_pi_apply i))
  have hh := map_withDensity_equiv e (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))
    (fun x => ∏ i, gaussianPDF 0 1 (x i)) hprod
  have hvol : (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).map e =
      (volume : Measure (Vec d)) := (PiLp.volume_preserving_toLp (Fin d)).map_eq
  rw [hvol] at hh
  exact hh
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def densityConstant (d : ℕ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ d
noncomputable def gaussianWeight (d : ℕ) (x : Vec d) : ℝ :=
  densityConstant d * Real.exp (-‖x‖ ^ 2 / 2)

lemma densityConstant_pos (d : ℕ) : 0 < densityConstant d := by
  unfold densityConstant
  positivity

lemma gaussianWeight_pos (d : ℕ) (x : Vec d) : 0 < gaussianWeight d x :=
  mul_pos (densityConstant_pos d) (Real.exp_pos _)

lemma continuous_gaussianWeight (d : ℕ) : Continuous (gaussianWeight d) := by
  unfold gaussianWeight
  fun_prop

lemma gaussianPDF_product (d : ℕ) (x : Vec d) :
    (∏ i : Fin d, gaussianPDF 0 1 (x i)) = ENNReal.ofReal (gaussianWeight d x) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  unfold gaussianWeight densityConstant
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

lemma gaussian_eq_withDensity (d : ℕ) :
    gaussian d = (volume : Measure (Vec d)).withDensity (fun x => ENNReal.ofReal (gaussianWeight d x)) := by
  rw [gaussian_eq_productDensity]
  congr 1
  funext x
  exact gaussianPDF_product d x

end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
open BookProof.HermiteProductCore
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
open BookProof.HermiteProductCore
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianPrivacyDensity
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_inner_map {d : ℕ} (v : Vec d) :
    (gaussian d).map (fun x => inner ℝ v x) = gaussianReal 0 (‖v‖^2).toNNReal := by
  change (stdGaussian (Vec d)).map (innerSL ℝ v) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]
lemma gaussian_linear_mgf {d : ℕ} (v : Vec d) (t : ℝ) :
    (∫ x, Real.exp (t*inner ℝ v x) ∂gaussian d) = Real.exp (t^2*‖v‖^2/2) := by
  have h := mgf_gaussianReal (gaussian_inner_map v) t
  simpa [mgf, Real.toNNReal_of_nonneg (sq_nonneg _), mul_comm] using h
lemma gaussian_linear_exp_integrable {d : ℕ} (v : Vec d) (t : ℝ) :
    Integrable (fun x => Real.exp (t*inner ℝ v x)) (gaussian d) := by
  have hi := integrable_exp_mul_gaussianReal (μ := 0) (v := (‖v‖^2).toNNReal) t
  rw [← gaussian_inner_map v] at hi
  simpa only [Function.comp_def] using
    (integrable_map_measure (f := fun x : Vec d => inner ℝ v x)
      (g := fun y : ℝ => Real.exp (t*y)) (by fun_prop) (by fun_prop)).mp hi
noncomputable def shiftedGaussian {d : ℕ} (m : Vec d) : Measure (Vec d) :=
  (gaussian d).map (fun x => m+x)
instance {d : ℕ} (m : Vec d) : IsProbabilityMeasure (shiftedGaussian m) := by
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  unfold shiftedGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)
lemma shiftedGaussian_density {d : ℕ} (m : Vec d) :
    shiftedGaussian m = (volume : Measure (Vec d)).withDensity
      (fun x => ENNReal.ofReal (gaussianWeight d (x-m))) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft m
  change (gaussian d).map e = _
  rw [gaussian_eq_withDensity, map_withDensity_equiv e _ _
    (continuous_gaussianWeight d).measurable.ennreal_ofReal]
  have he : (volume : Measure (Vec d)).map e = volume :=
    (measurePreserving_add_left volume m).map_eq
  rw [he]
  congr 1
  funext x
  simp [e, sub_eq_add_neg, add_comm]
noncomputable def gaussianPrivacyLoss {d : ℕ} (m m' x : Vec d) : ℝ :=
  inner ℝ (m-m') x + (‖m'‖^2-‖m‖^2)/2
lemma gaussianWeight_ratio {d : ℕ} (m m' x : Vec d) :
    gaussianWeight d (x-m) = gaussianWeight d (x-m') *
      Real.exp (gaussianPrivacyLoss m m' x) := by
  unfold gaussianWeight gaussianPrivacyLoss
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  rw [norm_sub_sq_real, norm_sub_sq_real]
  rw [real_inner_comm m x, real_inner_comm m' x, inner_sub_left]
  ring
lemma gaussianPrivacyLoss_shift {d : ℕ} (m m' z : Vec d) :
    gaussianPrivacyLoss m m' (m+z) = inner ℝ (m-m') z + ‖m-m'‖^2/2 := by
  unfold gaussianPrivacyLoss
  rw [inner_add_right, norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm m' m]
  ring
lemma gaussianPrivacyLoss_exp_integrable {d : ℕ} (m m' : Vec d) (t : ℝ) :
    Integrable (fun x => Real.exp (t*gaussianPrivacyLoss m m' x)) (shiftedGaussian m) := by
  rw [shiftedGaussian]
  apply (integrable_map_measure (f := fun z : Vec d => m+z)
    (g := fun x => Real.exp (t*gaussianPrivacyLoss m m' x))
    (by unfold gaussianPrivacyLoss; fun_prop) (by fun_prop)).mpr
  simp only [Function.comp_def, gaussianPrivacyLoss_shift, mul_add, Real.exp_add]
  exact (gaussian_linear_exp_integrable (m-m') t).mul_const _
lemma gaussianPrivacyLoss_mgf {d : ℕ} (m m' : Vec d) (t : ℝ) :
    (∫ x, Real.exp (t*gaussianPrivacyLoss m m' x) ∂shiftedGaussian m) =
      Real.exp ((t*(t+1)/2)*‖m-m'‖^2) := by
  rw [shiftedGaussian, integral_map (by fun_prop) (by unfold gaussianPrivacyLoss; fun_prop)]
  simp_rw [gaussianPrivacyLoss_shift, mul_add, Real.exp_add]
  rw [integral_mul_const, gaussian_linear_mgf, ← Real.exp_add]
  congr 1
  ring
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AdaptiveGaussianKernel
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
variable {X : Type*} [MeasurableSpace X] {d : ℕ}
lemma measurable_gaussian_shift_weight (f : X → Vec d) (hf : Measurable f) :
    Measurable (fun z : X × Vec d => ENNReal.ofReal (gaussianWeight d (z.2-f z.1))) :=
  ((continuous_gaussianWeight d).measurable.comp (measurable_snd.sub (hf.comp measurable_fst))).ennreal_ofReal
noncomputable def gaussianShiftKernel (f : X → Vec d) (_hf : Measurable f) : Kernel X (Vec d) :=
  (Kernel.const X (volume : Measure (Vec d))).withDensity
    (fun a y => ENNReal.ofReal (gaussianWeight d (y-f a)))
lemma gaussianShiftKernel_apply (f : X → Vec d) (hf : Measurable f) (a : X) :
    gaussianShiftKernel f hf a = shiftedGaussian (f a) := by
  rw [gaussianShiftKernel, Kernel.withDensity_apply _ (measurable_gaussian_shift_weight f hf),
    Kernel.const_apply, shiftedGaussian_density]
instance gaussianShiftKernel_markov (f : X → Vec d) (hf : Measurable f) :
    IsMarkovKernel (gaussianShiftKernel f hf) := by
  constructor
  intro a
  rw [gaussianShiftKernel_apply]
  infer_instance
lemma gaussianShiftKernel_compProd_density (μ : Measure X) [SFinite μ]
    (f : X → Vec d) (hf : Measurable f) :
    μ ⊗ₘ gaussianShiftKernel f hf = (μ.prod (volume : Measure (Vec d))).withDensity
      (fun z => ENNReal.ofReal (gaussianWeight d (z.2-f z.1))) := by
  letI : IsSFiniteKernel ((Kernel.const X (volume : Measure (Vec d))).withDensity
      (fun a y => ENNReal.ofReal (gaussianWeight d (y-f a)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  rw [gaussianShiftKernel, Measure.compProd_withDensity (measurable_gaussian_shift_weight f hf),
    Measure.compProd_const]
lemma gaussian_joint_likelihood (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L : X → ℝ) (hL : Measurable L)
    (hμ : μ = ν.withDensity (fun a => ENNReal.ofReal (Real.exp (L a))))
    (f g : X → Vec d) (hf : Measurable f) (hg : Measurable g) :
    μ ⊗ₘ gaussianShiftKernel f hf = (ν ⊗ₘ gaussianShiftKernel g hg).withDensity
      (fun z => ENNReal.ofReal (Real.exp (L z.1 + gaussianPrivacyLoss (f z.1) (g z.1) z.2))) := by
  have hfw := measurable_gaussian_shift_weight f hf
  have hgw := measurable_gaussian_shift_weight g hg
  have hpl : Measurable (fun z : X × Vec d =>
      ENNReal.ofReal (Real.exp (L z.1 + gaussianPrivacyLoss (f z.1) (g z.1) z.2))) := by
    unfold gaussianPrivacyLoss
    fun_prop
  have hlift : Measurable (fun z : X × Vec d => ENNReal.ofReal (Real.exp (L z.1))) :=
    ((hL.comp measurable_fst).exp).ennreal_ofReal
  rw [gaussianShiftKernel_compProd_density μ f hf, gaussianShiftKernel_compProd_density ν g hg,
    hμ, prod_withDensity_left hL.exp.ennreal_ofReal,
    ← withDensity_mul _ hlift hfw, ← withDensity_mul _ hgw hpl]
  congr 1
  funext z
  simp only [Pi.mul_apply]
  rw [gaussianWeight_ratio (f z.1) (g z.1) z.2, Real.exp_add]
  simp only [ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_mul (gaussianWeight_pos d _).le]
  ring
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AdaptiveGaussianMGF
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_joint_mgf {X : Type*} [MeasurableSpace X] {d : ℕ}
    (μ : Measure X) [IsProbabilityMeasure μ] (L : X → ℝ) (hL : Measurable L)
    (f g : X → Vec d) (hf : Measurable f) (hg : Measurable g)
    (c t : ℝ) (ht : 0 < t) (hc : ∀ a, ‖f a-g a‖^2/2 ≤ c)
    (hi : Integrable (fun a => Real.exp (t*L a)) μ) :
    Integrable (fun z : X × Vec d =>
      Real.exp (t*(L z.1+gaussianPrivacyLoss (f z.1) (g z.1) z.2)))
        (μ ⊗ₘ gaussianShiftKernel f hf) ∧
    (∫ z : X × Vec d, Real.exp (t*(L z.1+gaussianPrivacyLoss (f z.1) (g z.1) z.2))
        ∂(μ ⊗ₘ gaussianShiftKernel f hf)) ≤
      Real.exp (c*t*(t+1)) * ∫ a, Real.exp (t*L a) ∂μ := by
  let F : X × Vec d → ℝ := fun z =>
    Real.exp (t*(L z.1+gaussianPrivacyLoss (f z.1) (g z.1) z.2))
  let κ := gaussianShiftKernel f hf
  have hFm : Measurable F := by unfold F gaussianPrivacyLoss; fun_prop
  have hFi (a : X) : Integrable (fun y => F (a,y)) (κ a) := by
    rw [show κ a = shiftedGaussian (f a) from gaussianShiftKernel_apply f hf a]
    simp only [F, mul_add, Real.exp_add]
    exact (gaussianPrivacyLoss_exp_integrable (f a) (g a) t).const_mul _
  have hval (a : X) : (∫ y, F (a,y) ∂κ a) =
      Real.exp (t*L a) * Real.exp ((t*(t+1)/2)*‖f a-g a‖^2) := by
    rw [show κ a = shiftedGaussian (f a) from gaussianShiftKernel_apply f hf a]
    simp only [F, mul_add, Real.exp_add]
    rw [integral_const_mul, gaussianPrivacyLoss_mgf]
    congr 1
    congr 1
    ring
  have hvbound (a : X) : (∫ y, F (a,y) ∂κ a) ≤
      Real.exp (c*t*(t+1))*Real.exp (t*L a) := by
    rw [hval, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ht.le (show 0 ≤ t+1 by linarith), hc a]
  have hnorm (a : X) : (∫ y, ‖F (a,y)‖ ∂κ a) = ∫ y, F (a,y) ∂κ a := by
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by simp only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])
  have hout : Integrable (fun a => ∫ y, ‖F (a,y)‖ ∂κ a) μ := by
    simp_rw [hnorm]
    apply (hi.const_mul (Real.exp (c*t*(t+1)))).mono'
      (hFm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).aestronglyMeasurable
    exact ae_of_all μ (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => (Real.exp_pos _).le))]
      exact hvbound a)
  have hj : Integrable F (μ ⊗ₘ κ) :=
    (Measure.integrable_compProd_iff hFm.aestronglyMeasurable).mpr ⟨ae_of_all μ hFi,hout⟩
  refine ⟨hj,?_⟩
  change (∫ z, F z ∂μ ⊗ₘ κ) ≤ _
  rw [Measure.integral_compProd hj, ← integral_const_mul]
  apply integral_mono (by simpa only [hnorm] using hout) (hi.const_mul _)
  exact hvbound
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.LikelihoodPrivacy
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma privacy_measure_le_of_likelihood {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L : Y → ℝ) (hL : Measurable L)
    (hd : μ = ν.withDensity (fun y => ENNReal.ofReal (Real.exp (L y))))
    (ε δ : ℝ) (hδ : 0 ≤ δ) (ht : μ.real {y | ε < L y} ≤ δ)
    (A : Set Y) (hA : MeasurableSet A) :
    μ.real A ≤ Real.exp ε * ν.real A + δ := by
  let B : Set Y := {y | ε < L y}
  let G : Set Y := {y | L y ≤ ε}
  have hG : MeasurableSet G := measurableSet_le hL measurable_const
  have hB : MeasurableSet B := measurableSet_lt measurable_const hL
  have hgood : μ (A ∩ G) ≤ ENNReal.ofReal (Real.exp ε) * ν A := by
    rw [hd, withDensity_apply _ (hA.inter hG)]
    calc
      _ ≤ ∫⁻ _ in A ∩ G, ENNReal.ofReal (Real.exp ε) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (hA.inter hG)] with y hy
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hy.2)
      _ = ENNReal.ofReal (Real.exp ε) * ν (A ∩ G) := by simp
      _ ≤ _ := by gcongr; exact inter_subset_left
  have htail : μ B ≤ ENNReal.ofReal δ := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ B) ENNReal.ofReal_ne_top).mp
    simpa [B, measureReal_def, ENNReal.toReal_ofReal hδ] using ht
  have hsplit : μ A ≤ μ (A ∩ G) + μ B := by
    apply (measure_mono (show A ⊆ (A ∩ G) ∪ B from fun y hy => by
      by_cases hg : L y ≤ ε
      · exact Or.inl ⟨hy,hg⟩
      · exact Or.inr (lt_of_not_ge hg))).trans
    exact measure_union_le _ _
  have hmain := hsplit.trans (add_le_add hgood htail)
  have hfin : ENNReal.ofReal (Real.exp ε) * ν A + ENNReal.ofReal δ ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν A),
      ENNReal.ofReal_ne_top⟩
  have hreal := ENNReal.toReal_mono hfin hmain
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν A))
    ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos ε).le, ENNReal.toReal_ofReal hδ] at hreal
  exact hreal
lemma exponential_tail_bound {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (L : Y → ℝ) (t ε : ℝ) (ht : 0 < t)
    (hi : Integrable (fun y => Real.exp (t*L y)) μ) :
    μ.real {y | ε < L y} ≤ (∫ y, Real.exp (t*L y) ∂μ) / Real.exp (t*ε) := by
  have hsubset : {y | ε < L y} ⊆ {y | Real.exp (t*ε) ≤ Real.exp (t*L y)} := by
    intro y hy
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy.le ht.le))
  have hm := measureReal_mono (μ := μ) hsubset
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (fun y => (Real.exp_pos _).le)) hi (Real.exp (t*ε))
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  nlinarith [Real.exp_pos (t*ε)]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianPrivacyCalibration
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma likelihood_tail_of_quadratic_mgf {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (L : Y → ℝ) (c ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (hc : c ≤ ε^2/(16*Real.log (1/δ)))
    (hi : ∀ t : ℝ, 0 < t → Integrable (fun y => Real.exp (t*L y)) μ)
    (hm : ∀ t : ℝ, 0 < t → (∫ y, Real.exp (t*L y) ∂μ) ≤ Real.exp (c*t*(t+1))) :
    μ.real {y | ε < L y} ≤ δ := by
  let r := Real.log (1/δ)
  have hrhalf : 1/2 ≤ r := by
    have h := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hδ.1)
    simp only [one_div, inv_inv] at h
    dsimp [r]
    simpa only [one_div] using (show (1:ℝ)/2 ≤ Real.log δ⁻¹ by linarith [hδ.2])
  have hr : 0 < r := by linarith
  let t := 2*r/ε
  have ht : 0 < t := div_pos (mul_pos (by norm_num) hr) hε.1
  have hct : c*t*(t+1) ≤ r := by
    calc
      _ ≤ (ε^2/(16*r))*t*(t+1) := by gcongr
      _ = r/4+ε/8 := by dsimp [t]; field_simp [hε.1.ne',hr.ne']; ring
      _ ≤ r := by linarith [hε.2]
  have hte : t*ε = 2*r := by dsimp [t]; field_simp [hε.1.ne']
  calc
    _ ≤ (∫ y, Real.exp (t*L y) ∂μ)/Real.exp (t*ε) := exponential_tail_bound μ L t ε ht (hi t ht)
    _ ≤ Real.exp (c*t*(t+1))/Real.exp (t*ε) :=
      div_le_div_of_nonneg_right (hm t ht) (Real.exp_pos _).le
    _ = Real.exp (c*t*(t+1)-t*ε) := (Real.exp_sub _ _).symm
    _ ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by rw [hte]; linarith)
    _ = δ := by rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hδ.1)]; simp
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AdaptiveGaussianPrivacy
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
/-- An exact likelihood ratio together with its Gaussian exponential-moment bound. -/
def GaussianPrivacyCertificate {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (c : ℝ) : Prop :=
  ∃ L : X → ℝ, Measurable L ∧
    μ = ν.withDensity (fun a => ENNReal.ofReal (Real.exp (L a))) ∧
    ∀ t : ℝ, 0 < t → Integrable (fun a => Real.exp (t*L a)) μ ∧
      (∫ a, Real.exp (t*L a) ∂μ) ≤ Real.exp (c*t*(t+1))
lemma GaussianPrivacyCertificate.refl {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] : GaussianPrivacyCertificate μ μ 0 := by
  refine ⟨fun _ => 0, measurable_const, ?_, ?_⟩
  · simp
  · intro t ht
    constructor
    · simp
    · simp
lemma GaussianPrivacyCertificate.gaussian_step {X : Type*} [MeasurableSpace X] {d : ℕ}
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c0 : ℝ}
    (hcert : GaussianPrivacyCertificate μ ν c0)
    (f g : X → Vec d) (hf : Measurable f) (hg : Measurable g)
    (c : ℝ) (hc : ∀ a, ‖f a-g a‖^2/2 ≤ c) :
    GaussianPrivacyCertificate (μ ⊗ₘ gaussianShiftKernel f hf)
      (ν ⊗ₘ gaussianShiftKernel g hg) (c0+c) := by
  obtain ⟨L,hL,hd,hm⟩ := hcert
  refine ⟨fun z => L z.1+gaussianPrivacyLoss (f z.1) (g z.1) z.2,
    (by unfold gaussianPrivacyLoss; fun_prop), gaussian_joint_likelihood μ ν L hL hd f g hf hg, ?_⟩
  intro t ht
  have hstep := gaussian_joint_mgf μ L hL f g hf hg c t ht hc (hm t ht).1
  refine ⟨hstep.1,?_⟩
  calc
    _ ≤ Real.exp (c*t*(t+1)) * ∫ a, Real.exp (t*L a) ∂μ := hstep.2
    _ ≤ Real.exp (c*t*(t+1))*Real.exp (c0*t*(t+1)) :=
      mul_le_mul_of_nonneg_left (hm t ht).2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
lemma GaussianPrivacyCertificate.privacy {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : ℝ}
    (hcert : GaussianPrivacyCertificate μ ν c) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (hc : c ≤ ε^2/(16*Real.log (1/δ))) (A : Set X) (hA : MeasurableSet A) :
    μ.real A ≤ Real.exp ε*ν.real A+δ := by
  obtain ⟨L,hL,hd,hm⟩ := hcert
  apply privacy_measure_le_of_likelihood μ ν L hL hd ε δ hδ.1.le _ A hA
  exact likelihood_tail_of_quadratic_mgf μ L c ε δ hε hδ hc
    (fun t ht => (hm t ht).1) (fun t ht => (hm t ht).2)
lemma GaussianPrivacyCertificate.privacy_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : ℝ}
    (hcert : GaussianPrivacyCertificate μ ν c) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (hc : c ≤ ε^2/(16*Real.log (1/δ))) (f : X → Y) (hf : Measurable f)
    (A : Set Y) (hA : MeasurableSet A) :
    (μ.map f).real A ≤ Real.exp ε*(ν.map f).real A+δ := by
  simpa only [measureReal_def, Measure.map_apply hf hA] using
    hcert.privacy ε δ hε hδ hc (f ⁻¹' A) (hf hA)
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianTranscript
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
/-- A finite transcript, represented by successive products in its order of generation. -/
def GaussianHistory (d : ℕ) : ℕ → Type
  | 0 => Unit
  | n+1 => GaussianHistory d n × Vec d
instance gaussianHistoryMeasurable (d n : ℕ) : MeasurableSpace (GaussianHistory d n) := by
  induction n with
  | zero => exact (inferInstance : MeasurableSpace Unit)
  | succ n ih => exact @Prod.instMeasurableSpace (GaussianHistory d n) (Vec d) ih inferInstance
attribute [reducible] GaussianHistory
noncomputable def gaussianTranscriptLaw {d : ℕ}
    (F : ∀ k : ℕ, GaussianHistory d k → Vec d) (hF : ∀ k, Measurable (F k)) :
    ∀ n : ℕ, Measure (GaussianHistory d n)
  | 0 => Measure.dirac ()
  | n+1 => gaussianTranscriptLaw F hF n ⊗ₘ gaussianShiftKernel (F n) (hF n)
instance gaussianTranscript_probability {d : ℕ}
    (F : ∀ k : ℕ, GaussianHistory d k → Vec d) (hF : ∀ k, Measurable (F k)) (n : ℕ) :
    IsProbabilityMeasure (gaussianTranscriptLaw F hF n) := by
  induction n with
  | zero => dsimp [gaussianTranscriptLaw]; infer_instance
  | succ n ih =>
    letI := ih
    change IsProbabilityMeasure (gaussianTranscriptLaw F hF n ⊗ₘ gaussianShiftKernel (F n) (hF n))
    infer_instance
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.PublicGaussianTranscript
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
local instance (d : ℕ) : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
def PublicGaussianHistory (B : Type*) (d : ℕ) : ℕ → Type _
  | 0 => B
  | n+1 => PublicGaussianHistory B d n × Vec d
instance publicGaussianHistoryMeasurable (B : Type*) [MeasurableSpace B] (d n : ℕ) :
    MeasurableSpace (PublicGaussianHistory B d n) := by
  induction n with
  | zero => exact (inferInstance : MeasurableSpace B)
  | succ n ih => exact @Prod.instMeasurableSpace (PublicGaussianHistory B d n) (Vec d) ih inferInstance
attribute [reducible] PublicGaussianHistory
noncomputable def publicGaussianTranscriptLaw {B : Type*} [MeasurableSpace B] {d : ℕ}
    (μ : Measure B) (F : ∀ k : ℕ, PublicGaussianHistory B d k → Vec d) (hF : ∀ k, Measurable (F k)) :
    ∀ n : ℕ, Measure (PublicGaussianHistory B d n)
  | 0 => μ
  | n+1 => publicGaussianTranscriptLaw μ F hF n ⊗ₘ gaussianShiftKernel (F n) (hF n)
instance publicGaussianTranscript_probability {B : Type*} [MeasurableSpace B] {d : ℕ}
    (μ : Measure B) [IsProbabilityMeasure μ]
    (F : ∀ k : ℕ, PublicGaussianHistory B d k → Vec d) (hF : ∀ k, Measurable (F k)) (n : ℕ) :
    IsProbabilityMeasure (publicGaussianTranscriptLaw μ F hF n) := by
  induction n with
  | zero => dsimp [publicGaussianTranscriptLaw]; infer_instance
  | succ n ih =>
    letI := ih
    change IsProbabilityMeasure (publicGaussianTranscriptLaw μ F hF n ⊗ₘ gaussianShiftKernel (F n) (hF n))
    infer_instance
lemma publicGaussianTranscript_certificate {B : Type*} [MeasurableSpace B] {d : ℕ}
    (μ : Measure B) [IsProbabilityMeasure μ]
    (F G : ∀ k : ℕ, PublicGaussianHistory B d k → Vec d)
    (hF : ∀ k, Measurable (F k)) (hG : ∀ k, Measurable (G k))
    (c : ℕ → ℝ) (hc : ∀ k a, ‖F k a-G k a‖^2/2 ≤ c k) (n : ℕ) :
    GaussianPrivacyCertificate (publicGaussianTranscriptLaw μ F hF n) (publicGaussianTranscriptLaw μ G hG n)
      (∑ k ∈ range n, c k) := by
  induction n with
  | zero => exact GaussianPrivacyCertificate.refl μ
  | succ n ih =>
    simpa only [publicGaussianTranscriptLaw,sum_range_succ] using
      ih.gaussian_step (F n) (G n) (hF n) (hG n) (c n) (hc n)
lemma gaussian_shift_push {X : Type*} [MeasurableSpace X] {d : ℕ}
    (μ : Measure X) [SFinite μ] (f : X → Vec d) (hf : Measurable f) :
    (μ.prod (gaussian d)).map (fun q => (q.1,f q.1+q.2)) = μ ⊗ₘ gaussianShiftKernel f hf := by
  have hm : Measurable (fun q : X × Vec d => (q.1,f q.1+q.2)) :=
    measurable_fst.prodMk ((hf.comp measurable_fst).add measurable_snd)
  ext A hA
  rw [Measure.map_apply hm hA,Measure.prod_apply (hA.preimage hm),Measure.compProd_apply hA]
  apply lintegral_congr_ae
  apply ae_of_all
  intro x
  change (gaussian d) {z | (x,f x+z) ∈ A} = (gaussianShiftKernel f hf x) (Prod.mk x ⁻¹' A)
  have hAx : MeasurableSet (Prod.mk x ⁻¹' A) := hA.preimage (measurable_const.prodMk measurable_id)
  rw [gaussianShiftKernel_apply,shiftedGaussian,Measure.map_apply (by fun_prop) hAx]
  rfl
def publicGaussianBase {B : Type*} {d : ℕ} : ∀ n : ℕ, PublicGaussianHistory B d n → B
  | 0, x => x
  | n+1, x => publicGaussianBase n x.1
lemma publicGaussianBase_measurable {B : Type*} [MeasurableSpace B] {d : ℕ} (n : ℕ) :
    Measurable (@publicGaussianBase B d n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp measurable_fst
noncomputable def publicGaussianRawLaw {B : Type*} [MeasurableSpace B] (μ : Measure B) (d : ℕ) :
    ∀ n : ℕ, Measure (PublicGaussianHistory B d n)
  | 0 => μ
  | n+1 => (publicGaussianRawLaw μ d n).prod (gaussian d)
instance publicGaussianRaw_probability {B : Type*} [MeasurableSpace B] (μ : Measure B)
    [IsProbabilityMeasure μ] (d n : ℕ) : IsProbabilityMeasure (publicGaussianRawLaw μ d n) := by
  induction n with
  | zero => dsimp [publicGaussianRawLaw]; infer_instance
  | succ n ih =>
    letI := ih
    change IsProbabilityMeasure ((publicGaussianRawLaw μ d n).prod (gaussian d))
    infer_instance
noncomputable def publicGaussianSampler {B : Type*} {d : ℕ}
    (F : ∀ k : ℕ, PublicGaussianHistory B d k → Vec d) : ∀ n : ℕ,
    PublicGaussianHistory B d n → PublicGaussianHistory B d n
  | 0, x => x
  | n+1, x => let a := publicGaussianSampler F n x.1; (a,F n a+x.2)
lemma publicGaussianSampler_measurable {B : Type*} [MeasurableSpace B] {d : ℕ}
    (F : ∀ k : ℕ, PublicGaussianHistory B d k → Vec d) (hF : ∀ k, Measurable (F k)) (n : ℕ) :
    Measurable (publicGaussianSampler F n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
    have ha := ih.comp (measurable_fst : Measurable (Prod.fst : PublicGaussianHistory B d (n+1) → PublicGaussianHistory B d n))
    exact ha.prodMk (((hF n).comp ha).add measurable_snd)
lemma publicGaussianSampler_law {B : Type*} [MeasurableSpace B] {d : ℕ}
    (μ : Measure B) [IsProbabilityMeasure μ]
    (F : ∀ k : ℕ, PublicGaussianHistory B d k → Vec d) (hF : ∀ k, Measurable (F k)) (n : ℕ) :
    (publicGaussianRawLaw μ d n).map (publicGaussianSampler F n) = publicGaussianTranscriptLaw μ F hF n := by
  induction n with
  | zero => simp [publicGaussianRawLaw,publicGaussianSampler,publicGaussianTranscriptLaw]
  | succ n ih =>
    have hs := publicGaussianSampler_measurable F hF n
    have hm : Measurable (fun q : PublicGaussianHistory B d n × Vec d => (q.1,F n q.1+q.2)) :=
      measurable_fst.prodMk (((hF n).comp measurable_fst).add measurable_snd)
    calc
      _ = (((publicGaussianRawLaw μ d n).map (publicGaussianSampler F n)).prod (gaussian d)).map
          (fun q => (q.1,F n q.1+q.2)) := by
        conv_rhs => rw [← Measure.map_id (μ := gaussian d)]
        rw [Measure.map_prod_map _ _ hs measurable_id,Measure.map_map hm (hs.prodMap measurable_id)]
        rfl
      _ = _ := by rw [ih,gaussian_shift_push]; rfl
lemma publicGaussianSampler_base {B : Type*} {d : ℕ}
    (F : ∀ k : ℕ, PublicGaussianHistory B d k → Vec d) (n : ℕ) (q : PublicGaussianHistory B d n) :
    publicGaussianBase n (publicGaussianSampler F n q) = publicGaussianBase n q := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih q.1
end PrivateAgnosticHalfspace.Gaussian


end

section
-- Solutions.GradientSensitivity
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma neighboring_gradient_average_sensitivity {Z : Type*} {D n : ℕ}
    (g : Z → Vec D → Vec D) (T : ℝ) (hT : 0 ≤ T) (hg : ∀ z v, ‖g z v‖ ≤ T)
    (hn : 0 < n) (S S' : Fin n → Z)
    (hS : PrivateUniformGen.Characterization.Neighbors S S') (v : Fin n → Vec D) :
    ‖(n : ℝ)⁻¹ • (∑ i, g (S i) (v i)) -
      (n : ℝ)⁻¹ • (∑ i, g (S' i) (v i))‖ ≤ 2*T/n := by
  obtain ⟨i,hi,hrest⟩ := hS
  have he : (∑ j : Fin n, (g (S j) (v j)-g (S' j) (v j))) =
      g (S i) (v i)-g (S' i) (v i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [hrest j hji, sub_self]
    · simp
  rw [← smul_sub, ← sum_sub_distrib, he, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  have hb : ‖g (S i) (v i)-g (S' i) (v i)‖ ≤ 2*T := by
    exact (norm_sub_le _ _).trans (by linarith [hg (S i) (v i),hg (S' i) (v i)])
  calc
    _ ≤ (n : ℝ)⁻¹*(2*T) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring
lemma gaussian_gradient_mean_budget (T σ ε δ : ℝ) (n : ℕ) (hn : 0 < n)
    (hT : 0 ≤ T) (hσ : 0 < σ) (hε : 0 < ε) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (hnoise : 32*T^2*Real.log (1/δ) ≤ (n : ℝ)*ε^2*σ^2) :
    (n : ℝ) * ((2*T/n/σ)^2/2) ≤ ε^2/(16*Real.log (1/δ)) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hl : 0 < Real.log (1/δ) := Real.log_pos (by
    rw [one_lt_div hδ.1]; linarith [hδ.2])
  apply (le_div_iff₀ (by positivity : 0 < 16*Real.log (1/δ))).mpr
  have hs : 0 < (n:ℝ)*σ^2 := mul_pos hnR (sq_pos_of_pos hσ)
  have he : (n : ℝ) * ((2*T/n/σ)^2/2) * (16*Real.log (1/δ)) =
      (32*T^2*Real.log (1/δ))/((n : ℝ)*σ^2) := by
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ hs).mpr
  nlinarith [hnoise]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.OptimizerTranscript
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
abbrev OptimizerPublicNoise (n : ℕ) := Fin (n+1) → Fin n → ℝ
noncomputable def optimizerTranscriptState {D n : ℕ} (τ β : ℝ) :
    ∀ k : ℕ, PublicGaussianHistory (OptimizerPublicNoise n) D k → Vec D × Vec D
  | 0, _ => (0,0)
  | k+1, q =>
    let prev := optimizerTranscriptState τ β k q.1
    let md := (1-accelAlpha (k+1)) • prev.2 + accelAlpha (k+1) • prev.1
    let g := τ • q.2
    (unitProjection (prev.1-accelLambda β (k+1) • g),unitProjection (md-β • g))
lemma optimizerTranscriptState_measurable {D n : ℕ} (τ β : ℝ) (k : ℕ) :
    Measurable (@optimizerTranscriptState D n τ β k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hp := ih.comp (measurable_fst : Measurable (Prod.fst :
      PublicGaussianHistory (OptimizerPublicNoise n) D (k+1) → PublicGaussianHistory (OptimizerPublicNoise n) D k))
    have hmd := (hp.snd.const_smul (1-accelAlpha (k+1))).add (hp.fst.const_smul (accelAlpha (k+1)))
    have hg : Measurable (fun q : PublicGaussianHistory (OptimizerPublicNoise n) D (k+1) => τ • q.2) := by
      convert! measurable_snd.const_smul τ using 1 <;> infer_instance
    convert! ((unitProjection_continuous D).measurable.comp (hp.fst.sub (hg.const_smul (accelLambda β (k+1))))).prodMk
      ((unitProjection_continuous D).measurable.comp (hmd.sub (hg.const_smul β))) using 1 <;> infer_instance
lemma optimizerTranscriptState_norm {D n : ℕ} (τ β : ℝ) (k : ℕ)
    (q : PublicGaussianHistory (OptimizerPublicNoise n) D k) :
    ‖(optimizerTranscriptState τ β k q).1‖ ≤ 1 ∧ ‖(optimizerTranscriptState τ β k q).2‖ ≤ 1 := by
  cases k with
  | zero => simp [optimizerTranscriptState]
  | succ k => exact ⟨unitProjection_norm _,unitProjection_norm _⟩
noncomputable def optimizerTranscriptQuery {D n : ℕ} (τ β : ℝ) (k : ℕ)
    (q : PublicGaussianHistory (OptimizerPublicNoise n) D k) : Vec D :=
  (1-accelAlpha (k+1)) • (optimizerTranscriptState τ β k q).2 +
    accelAlpha (k+1) • (optimizerTranscriptState τ β k q).1
lemma optimizerTranscriptQuery_measurable {D n : ℕ} (τ β : ℝ) (k : ℕ) :
    Measurable (@optimizerTranscriptQuery D n τ β k) := by
  convert! ((optimizerTranscriptState_measurable τ β k).snd.const_smul (1-accelAlpha (k+1))).add
    ((optimizerTranscriptState_measurable τ β k).fst.const_smul (accelAlpha (k+1))) using 1 <;> infer_instance
noncomputable def optimizerTranscriptMean (d p n : ℕ) (ε δ : ℝ) (S : Fin n → Example d) (k : ℕ)
    (q : PublicGaussianHistory (OptimizerPublicNoise n) (featureDimension d p) k) : Vec (featureDimension d p) :=
  let τ := regressionTau (radius d p) n ε δ
  τ⁻¹ • batchSmoothedSubgradient ((n : ℝ)⁻¹) (coefficientFeatures d p S) (coefficientLabels S)
    (optimizerTranscriptQuery τ (optimizerStep d p n ε δ) k q)
    (finiteNoiseSequence 0 (publicGaussianBase k q) (k+1))
lemma optimizerTranscriptMean_measurable (d p n : ℕ) (ε δ : ℝ) (S : Fin n → Example d) (k : ℕ) :
    Measurable (optimizerTranscriptMean d p n ε δ S k) := by
  have hq := optimizerTranscriptQuery_measurable (D := featureDimension d p) (n := n)
    (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ) k
  have hz := (finiteNoiseSequence_measurable (N := n) (0 : Fin n → ℝ) (k+1)).comp
    (publicGaussianBase_measurable (B := OptimizerPublicNoise n) (d := featureDimension d p) k)
  have hbatch := (batchSmoothedSubgradient_measurable ((n : ℝ)⁻¹) (coefficientFeatures d p S) (coefficientLabels S)).comp
    (hq.prodMk hz)
  convert! hbatch.const_smul (regressionTau (radius d p) n ε δ)⁻¹ using 1
lemma neighboring_regression_batch_sensitivity (d p n : ℕ) (hn : 0 < n) (r : ℝ)
    (S S' : Fin n → Example d) (hS : PrivateUniformGen.Characterization.Neighbors S S')
    (v : Vec (featureDimension d p)) (z : Fin n → ℝ) :
    ‖batchSmoothedSubgradient r (coefficientFeatures d p S) (coefficientLabels S) v z-
      batchSmoothedSubgradient r (coefficientFeatures d p S') (coefficientLabels S') v z‖ ≤ 2*radius d p/n := by
  let g := fun (q : Example d × ℝ) (v : Vec (featureDimension d p)) =>
    scalarSmoothedSubgradient r (coefficientIsometry d p (clipped d p q.1.1)) (label q.1.2) v q.2
  have hg (q : Example d × ℝ) (w) : ‖g q w‖ ≤ radius d p := by
    rw [scalarSmoothedSubgradient_norm,(coefficientIsometry d p).norm_map]
    exact norm_clipped_le_radius d p q.1.1
  have hpair : PrivateUniformGen.Characterization.Neighbors (fun i => (S i,z i)) (fun i => (S' i,z i)) := by
    obtain ⟨i,hi,hrest⟩ := hS
    refine ⟨i,?_,?_⟩
    · intro he
      exact hi (congrArg Prod.fst he)
    · intro j hji
      exact congrArg (fun x => (x,z j)) (hrest j hji)
  convert! neighboring_gradient_average_sensitivity g (radius d p) (radius_pos d p).le hg hn
    (fun i => (S i,z i)) (fun i => (S' i,z i)) hpair (fun _ => v) using 1
lemma optimizerTranscriptMean_sensitivity (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hτ : 0 < regressionTau (radius d p) n ε δ)
    (S S' : Fin n → Example d) (hS : PrivateUniformGen.Characterization.Neighbors S S')
    (k : ℕ) (q : PublicGaussianHistory (OptimizerPublicNoise n) (featureDimension d p) k) :
    ‖optimizerTranscriptMean d p n ε δ S k q-optimizerTranscriptMean d p n ε δ S' k q‖ ≤
      2*radius d p/n/regressionTau (radius d p) n ε δ := by
  unfold optimizerTranscriptMean
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hτ)]
  have h := neighboring_regression_batch_sensitivity d p n hn ((n : ℝ)⁻¹) S S' hS
    (optimizerTranscriptQuery (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ) k q)
    (finiteNoiseSequence 0 (publicGaussianBase k q) (k+1))
  calc
    _ ≤ (regressionTau (radius d p) n ε δ)⁻¹ * (2*radius d p/n) :=
      mul_le_mul_of_nonneg_left h (inv_pos.mpr hτ).le
    _ = _ := by ring
noncomputable def optimizerTranscriptOutput (d p n : ℕ) (ε δ : ℝ)
    (q : PublicGaussianHistory (OptimizerPublicNoise n) (featureDimension d p) n) : UnitBall d p :=
  ⟨(coefficientIsometry d p).symm
    (optimizerTranscriptState (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ) n q).2,by
    rw [(coefficientIsometry d p).symm.norm_map]
    exact (optimizerTranscriptState_norm _ _ _ _).2⟩
lemma optimizerTranscriptOutput_measurable (d p n : ℕ) (ε δ : ℝ) :
    Measurable (optimizerTranscriptOutput d p n ε δ) :=
  ((coefficientIsometry d p).symm.continuous.measurable.comp
    (optimizerTranscriptState_measurable (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ) n).snd).subtype_mk
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.OptimizerTranscriptPrivacy
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
noncomputable def optimizerPublicNoiseLaw (n : ℕ) : Measure (OptimizerPublicNoise n) :=
  Measure.pi (fun _ : Fin (n+1) => Measure.pi (fun _ : Fin n => gaussianReal 0 1))
instance optimizerPublicNoise_probability (n : ℕ) : IsProbabilityMeasure (optimizerPublicNoiseLaw n) := by
  unfold optimizerPublicNoiseLaw
  infer_instance
noncomputable def optimizerTranscriptOutputLaw (d p n : ℕ) (ε δ : ℝ) (S : Fin n → Example d) :
    Measure (UnitBall d p) :=
  (publicGaussianTranscriptLaw (optimizerPublicNoiseLaw n) (optimizerTranscriptMean d p n ε δ S)
    (optimizerTranscriptMean_measurable d p n ε δ S) n).map (optimizerTranscriptOutput d p n ε δ)
instance optimizerTranscriptOutput_probability (d p n : ℕ) (ε δ : ℝ) (S : Fin n → Example d) :
    IsProbabilityMeasure (optimizerTranscriptOutputLaw d p n ε δ S) := by
  unfold optimizerTranscriptOutputLaw
  exact Measure.isProbabilityMeasure_map (optimizerTranscriptOutput_measurable d p n ε δ).aemeasurable
lemma optimizerTranscriptOutput_privacy (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (S S' : Fin n → Example d) (hS : PrivateUniformGen.Characterization.Neighbors S S')
    (A : Set (UnitBall d p)) (hA : MeasurableSet A) :
    (optimizerTranscriptOutputLaw d p n ε δ S).real A ≤
      Real.exp ε*(optimizerTranscriptOutputLaw d p n ε δ S').real A+δ := by
  let T := radius d p
  let τ := regressionTau T n ε δ
  let c := (2*T/n/τ)^2/2
  have hT : 0 < T := radius_pos d p
  have hτ : 0 < τ := regressionTau_pos T hT n hn ε δ hε.1 hδ
  have hc (k : ℕ) (q : PublicGaussianHistory (OptimizerPublicNoise n) (featureDimension d p) k) :
      ‖optimizerTranscriptMean d p n ε δ S k q-optimizerTranscriptMean d p n ε δ S' k q‖^2/2 ≤ c := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    exact pow_le_pow_left₀ (norm_nonneg _) (optimizerTranscriptMean_sensitivity d p n hn ε δ hτ S S' hS k q) 2
  have hcert := publicGaussianTranscript_certificate (optimizerPublicNoiseLaw n)
    (optimizerTranscriptMean d p n ε δ S) (optimizerTranscriptMean d p n ε δ S')
    (optimizerTranscriptMean_measurable d p n ε δ S) (optimizerTranscriptMean_measurable d p n ε δ S')
    (fun _ => c) hc n
  have hbudget : (∑ k ∈ range n, c) ≤ ε^2/(16*Real.log (1/δ)) := by
    simp only [sum_const,card_range,nsmul_eq_mul]
    exact gaussian_gradient_mean_budget T τ ε δ n hn hT.le hτ hε.1 hδ
      (regression_noise_calibration T n hn ε δ hε.1 hδ)
  exact hcert.privacy_map ε δ hε hδ hbudget (optimizerTranscriptOutput d p n ε δ)
    (optimizerTranscriptOutput_measurable d p n ε δ) A hA
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.PublicGaussianFiniteNoise
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
local instance (d : ℕ) : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
noncomputable def publicGaussianNest {B : Type*} {d : ℕ} : ∀ n : ℕ,
    B × (Fin n → Vec d) → PublicGaussianHistory B d n
  | 0, q => q.1
  | n+1, q => (publicGaussianNest n (q.1,Fin.init q.2),q.2 (Fin.last n))
lemma publicGaussianNest_measurable {B : Type*} [MeasurableSpace B] {d : ℕ} (n : ℕ) :
    Measurable (@publicGaussianNest B d n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hi : Measurable (fun q : B × (Fin (n+1) → Vec d) => (q.1,Fin.init q.2)) :=
      measurable_fst.prodMk (measurable_pi_lambda _ (fun j => (measurable_pi_apply j.castSucc).comp measurable_snd))
    exact (ih.comp hi).prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_snd)
lemma publicGaussianNest_law {B : Type*} [MeasurableSpace B] {d : ℕ}
    (μ : Measure B) [IsProbabilityMeasure μ] (n : ℕ) :
    (μ.prod (Measure.pi (fun _ : Fin n => gaussian d))).map (publicGaussianNest n) = publicGaussianRawLaw μ d n := by
  induction n with
  | zero => exact measurePreserving_fst.map_eq
  | succ n ih =>
    let ν := Measure.pi (fun _ : Fin n => gaussian d)
    have hsplit : MeasurePreserving
        (fun q : B × (Fin (n+1) → Vec d) => (q.1,(q.2 (Fin.last n),Fin.init q.2)))
        (μ.prod (Measure.pi (fun _ : Fin (n+1) => gaussian d))) (μ.prod ((gaussian d).prod ν)) := by
      convert! (MeasurePreserving.id μ).prod
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussian d) (Fin.last n)) using 1
      simp only [MeasurableEquiv.piFinSuccAbove_apply]
      rw [Fin.insertNthEquiv_last]
      rfl
    have hswap : MeasurePreserving
        (fun q : B × (Vec d × (Fin n → Vec d)) => (q.1,(q.2.2,q.2.1)))
        (μ.prod ((gaussian d).prod ν)) (μ.prod (ν.prod (gaussian d))) := by
      convert! (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := gaussian d) (ν := ν)) using 1
    have hassoc : MeasurePreserving
        (fun q : B × ((Fin n → Vec d) × Vec d) => ((q.1,q.2.1),q.2.2))
        (μ.prod (ν.prod (gaussian d))) ((μ.prod ν).prod (gaussian d)) :=
      (measurePreserving_prodAssoc μ ν (gaussian d)).symm
    have hstep : MeasurePreserving
        (fun q : B × (Fin (n+1) → Vec d) => ((q.1,Fin.init q.2),q.2 (Fin.last n)))
        (μ.prod (Measure.pi (fun _ : Fin (n+1) => gaussian d))) ((μ.prod ν).prod (gaussian d)) := by
      convert! hassoc.comp (hswap.comp hsplit) using 1
    have hm : Measurable (fun q : (B × (Fin n → Vec d)) × Vec d => (publicGaussianNest n q.1,q.2)) :=
      ((publicGaussianNest_measurable n).comp measurable_fst).prodMk measurable_snd
    calc
      _ = ((μ.prod ν).prod (gaussian d)).map (fun q => (publicGaussianNest n q.1,q.2)) := by
        rw [← hstep.map_eq,Measure.map_map hm hstep.measurable]
        rfl
      _ = ((μ.prod ν).map (publicGaussianNest n)).prod (gaussian d) := by
        have he := (Measure.map_prod_map (μ.prod ν) (gaussian d) (publicGaussianNest_measurable n) measurable_id).symm
        simp only [Measure.map_id] at he
        convert! he using 1
      _ = _ := by rw [ih]; rfl
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.OptimizerRawNoise
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
local instance (d : ℕ) : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
noncomputable def optimizerRawHistory {D n : ℕ}
    (s : Fin (n+1) → RegressionNoise n D) :
    ∀ k : ℕ, PublicGaussianHistory (OptimizerPublicNoise n) D k
  | 0 => fun j => (s j).1
  | k+1 => (optimizerRawHistory s k,finiteNoiseSequence 0 (fun j => (s j).2) (k+1))
lemma optimizerRawHistory_base {D n : ℕ} (s : Fin (n+1) → RegressionNoise n D) (k : ℕ) :
    publicGaussianBase k (optimizerRawHistory s k) = fun j => (s j).1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih
lemma optimizerRawHistory_measurable {D n : ℕ} (k : ℕ) :
    Measurable (fun s : Fin (n+1) → RegressionNoise n D => optimizerRawHistory s k) := by
  induction k with
  | zero => exact measurable_pi_lambda _ (fun j => (measurable_pi_apply j).fst)
  | succ k ih =>
    exact ih.prodMk ((finiteNoiseSequence_measurable (N := n) (0 : Vec D) (k+1)).comp
      (measurable_pi_lambda _ (fun j => (measurable_pi_apply j).snd)))
lemma optimizerRawHistory_eq_nest {D n : ℕ} (s : Fin (n+1) → RegressionNoise n D)
    (k : ℕ) (hk : k ≤ n) :
    optimizerRawHistory s k = publicGaussianNest k
      ((fun j => (s j).1),(fun j : Fin k => (s ⟨j.val+1,by omega⟩).2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [optimizerRawHistory,publicGaussianNest,ih (by omega),
      finiteNoiseSequence_apply 0 (fun j => (s j).2) (k+1) hk]
    rfl
lemma gaussian_tail_preserving (D n : ℕ) :
    MeasurePreserving (Fin.tail : (Fin (n+1) → Vec D) → Fin n → Vec D)
      (Measure.pi (fun _ : Fin (n+1) => gaussian D)) (Measure.pi (fun _ : Fin n => gaussian D)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussian D) 0
  have ht := (measurePreserving_snd (μ := gaussian D)
    (ν := Measure.pi (fun j : Fin n => gaussian D))).comp h
  convert! ht using 1
lemma optimizerRawHistory_law (D n : ℕ) :
    (Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D)).map (fun s => optimizerRawHistory s n) =
      publicGaussianRawLaw (optimizerPublicNoiseLaw n) D n := by
  let μ := optimizerPublicNoiseLaw n
  let ν := Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D)
  let g := fun s : Fin (n+1) → RegressionNoise n D =>
    ((fun j => (s j).1),Fin.tail (fun j => (s j).2))
  have hs := measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) (Vec D) (Fin (n+1))
    (fun _ => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (fun _ => gaussian D)
  have ht := (MeasurePreserving.id μ).prod (gaussian_tail_preserving D n)
  have hg : MeasurePreserving g ν (μ.prod (Measure.pi (fun _ : Fin n => gaussian D))) := by
    convert! ht.comp hs using 1
  have he (s) : optimizerRawHistory s n = publicGaussianNest n (g s) := by
    have h := optimizerRawHistory_eq_nest s n le_rfl
    convert! h using 1
  calc
    _ = ν.map (publicGaussianNest n ∘ g) := by
      congr 1
      exact funext he
    _ = (ν.map g).map (publicGaussianNest n) := by
      rw [Measure.map_map (publicGaussianNest_measurable n) hg.measurable]
    _ = _ := by rw [hg.map_eq,publicGaussianNest_law]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.OptimizerTranscriptCoupling
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry NonconvexAG.StochComposite
lemma optimizerTranscriptState_coupling (d p n : ℕ) (ε δ : ℝ)
    (hτ : regressionTau (radius d p) n ε δ ≠ 0) (S : Fin n → Example d)
    (s : Fin (n+1) → RegressionNoise n (featureDimension d p)) (k : ℕ) (hk : k ≤ n) :
    optimizerTranscriptState (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ) k
      (publicGaussianSampler (optimizerTranscriptMean d p n ε δ S) k (optimizerRawHistory s k)) =
    rsagPath (noisyRegressionOracle ((n : ℝ)⁻¹) (regressionTau (radius d p) n ε δ)
      (coefficientFeatures d p S) (coefficientLabels S))
      (fun x y c => unitProjection (x-c • y)) accelAlpha (fun _ => optimizerStep d p n ε δ)
      (accelLambda (optimizerStep d p n ε δ)) (fun _ => 1) 0 (finiteNoiseSequence (0,0) s) k := by
  let τ := regressionTau (radius d p) n ε δ
  let β := optimizerStep d p n ε δ
  let a := coefficientFeatures d p S
  let y := coefficientLabels S
  let F := optimizerTranscriptMean d p n ε δ S
  have hgrad (v : Vec (featureDimension d p)) (z : Fin n → ℝ) (w : Vec (featureDimension d p)) :
      τ • (τ⁻¹ • batchSmoothedSubgradient ((n : ℝ)⁻¹) a y v z+w) =
        noisyRegressionOracle ((n : ℝ)⁻¹) τ a y v (z,w) := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ hτ,one_smul]
    rfl
  induction k with
  | zero => rfl
  | succ k ih =>
    let q := publicGaussianSampler F k (optimizerRawHistory s k)
    have hmean : F k q = τ⁻¹ • batchSmoothedSubgradient ((n : ℝ)⁻¹) a y
        (optimizerTranscriptQuery τ β k q) (s ⟨k+1,by omega⟩).1 := by
      dsimp [F,optimizerTranscriptMean]
      rw [publicGaussianSampler_base,optimizerRawHistory_base,
        finiteNoiseSequence_apply 0 (fun j => (s j).1) (k+1) hk]
    have hprev := ih (by omega)
    change optimizerTranscriptState τ β (k+1)
      (q,F k q+finiteNoiseSequence 0 (fun j => (s j).2) (k+1)) = _
    rw [hmean,finiteNoiseSequence_apply 0 (fun j => (s j).2) (k+1) hk]
    simp only [optimizerTranscriptState]
    rw [hgrad]
    simp only [optimizerTranscriptQuery]
    rw [hprev]
    rw [rsagPath,sampleAvg_one _ (k+1) (by omega),
      finiteNoiseSequence_apply (0,0) s (k+1) hk]
lemma optimizerTranscriptOutput_coupling (d p n : ℕ) (ε δ : ℝ)
    (hτ : regressionTau (radius d p) n ε δ ≠ 0) (S : Fin n → Example d)
    (s : Fin (n+1) → RegressionNoise n (featureDimension d p)) :
    optimizerTranscriptOutput d p n ε δ
      (publicGaussianSampler (optimizerTranscriptMean d p n ε δ S) n (optimizerRawHistory s n)) =
      optimizerDraw d p n ε δ S s := by
  apply Subtype.ext
  apply congrArg (coefficientIsometry d p).symm
  exact congrArg Prod.snd (optimizerTranscriptState_coupling d p n ε δ hτ S s n le_rfl)
lemma concreteOptimizer_eq_transcript (d p n : ℕ) (ε δ : ℝ)
    (hτ : regressionTau (radius d p) n ε δ ≠ 0) (S : Fin n → Example d) :
    (concreteOptimizer d p n ε δ S : Measure (UnitBall d p)) = optimizerTranscriptOutputLaw d p n ε δ S := by
  let F := optimizerTranscriptMean d p n ε δ S
  have hF := optimizerTranscriptMean_measurable d p n ε δ S
  have hraw := optimizerRawHistory_measurable (D := featureDimension d p) (n := n) n
  have hsam := publicGaussianSampler_measurable F hF n
  have hout := optimizerTranscriptOutput_measurable d p n ε δ
  unfold concreteOptimizer optimizerTranscriptOutputLaw
  simp only [ProbabilityMeasure.coe_mk]
  rw [← publicGaussianSampler_law (optimizerPublicNoiseLaw n) F hF n,
    ← optimizerRawHistory_law (featureDimension d p) n,
    Measure.map_map hsam hraw,Measure.map_map hout (hsam.comp hraw)]
  congr 1
  funext s
  exact (optimizerTranscriptOutput_coupling d p n ε δ hτ S s).symm
lemma concreteOptimizer_private (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) :
    PrivateUniformGen.Characterization.IsDP (concreteOptimizer d p n ε δ) ε δ := by
  intro S S' hS A hA
  have hτ := regressionTau_pos (radius d p) (radius_pos d p) n hn ε δ hε.1 hδ
  rw [concreteOptimizer_eq_transcript d p n ε δ hτ.ne' S,
    concreteOptimizer_eq_transcript d p n ε δ hτ.ne' S']
  exact optimizerTranscriptOutput_privacy d p n hn ε δ hε hδ S S' hS A hA
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.Schedule
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian

lemma radius_sqrt_mul (d p : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    radius d p * Real.sqrt ((featureDimension d p : ℝ) * l) =
      2 * featureDimension d p * Real.sqrt l := by
  rw [radius, Real.sqrt_mul (Nat.cast_nonneg _)]
  calc
    _ = 2 * (Real.sqrt (featureDimension d p)) ^ 2 * Real.sqrt l := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

lemma block_of_large (C c α ε δ : ℝ) (d p n : ℕ)
    (hC : 0 < C) (hc : 0 < c) (hα : 0 < α) (hε : 0 < ε)
    (hlog : 0 ≤ Real.log (1 / δ)) (hn : 2 ≤ n)
    (hstat : 4 * C ^ 2 * featureDimension d p / (c ^ 2 * α ^ 2) ≤ (n : ℝ))
    (hpriv : 4 * C * featureDimension d p * Real.sqrt (Real.log (1 / δ)) /
      (c * ε * α) ≤ (n : ℝ)) : blockCondition C c α ε δ d p n := by
  refine ⟨hn, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha0 : 0 < c * α / (2 * C) := by positivity
  have hs : Real.sqrt ((featureDimension d p : ℝ) / n) ≤ c * α / (2 * C) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨ha0.le, ?_⟩
    have hh := (div_le_iff₀ (by positivity : 0 < c ^ 2 * α ^ 2)).mp hstat
    apply (div_le_iff₀ hn0).2
    field_simp
    nlinarith
  have hp : radius d p * Real.sqrt ((featureDimension d p : ℝ) * Real.log (1 / δ)) /
      (ε * n) ≤ c * α / (2 * C) := by
    rw [radius_sqrt_mul d p _ hlog]
    have hh := (div_le_iff₀ (by positivity : 0 < c * ε * α)).mp hpriv
    apply (div_le_iff₀ (mul_pos hε hn0)).2
    field_simp
    nlinarith
  calc
    C * (radius d p * Real.sqrt ((featureDimension d p : ℝ) * Real.log (1 / δ)) /
      (ε * n) + Real.sqrt ((featureDimension d p : ℝ) / n))
      ≤ C * (c * α / (2 * C) + c * α / (2 * C)) := by gcongr
    _ = c * α := by field_simp; ring

lemma training_schedule (C c α ε δ : ℝ) (d p : ℕ)
    (hC : 0 < C) (hc : 0 < c) (hα : 0 < α) (hε : 0 < ε)
    (hlog : 0 ≤ Real.log (1 / δ)) :
    blockCondition C c α ε δ d p (trainingSize C c α ε δ d p) ∧
    (∀ r, blockCondition C c α ε δ d p r → trainingSize C c α ε δ d p ≤ r) ∧
    (trainingSize C c α ε δ d p : ℝ) ≤
      3 + 4 * C ^ 2 * featureDimension d p / (c ^ 2 * α ^ 2) +
      4 * C * featureDimension d p * Real.sqrt (Real.log (1 / δ)) / (c * ε * α) := by
  classical
  let a := 4 * C ^ 2 * featureDimension d p / (c ^ 2 * α ^ 2)
  let b := 4 * C * featureDimension d p * Real.sqrt (Real.log (1 / δ)) / (c * ε * α)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let N : ℕ := ⌈2 + a + b⌉₊
  have hN : 2 + a + b ≤ (N : ℝ) := Nat.le_ceil _
  have hn : 2 ≤ N := by exact_mod_cast (show (2 : ℝ) ≤ N by linarith)
  have hgood : blockCondition C c α ε δ d p N :=
    block_of_large C c α ε δ d p N hC hc hα hε hlog hn
      (show a ≤ N by linarith) (show b ≤ N by linarith)
  have hex : ∃ n, blockCondition C c α ε δ d p n := ⟨N, hgood⟩
  have heq : trainingSize C c α ε δ d p = Nat.find hex := by
    simp only [trainingSize, dif_pos hex]
  rw [heq]
  refine ⟨Nat.find_spec hex, (fun r hr => Nat.find_min' hex hr), ?_⟩
  have hmin : Nat.find hex ≤ N := Nat.find_min' hex hgood
  have hceil : (N : ℝ) < (2 + a + b) + 1 := Nat.ceil_lt_add_one (by linarith)
  have hcast : (Nat.find hex : ℝ) ≤ N := by exact_mod_cast hmin
  dsimp [a,b] at hceil
  linarith

end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
lemma log_recip_nonneg (δ : ℝ) (hδ : 0 < δ ∧ δ ≤ 1 / 2) : 0 ≤ Real.log (1 / δ) := by
  apply Real.log_nonneg
  exact (le_div_iff₀ hδ.1).2 (by linarith [hδ.2])

lemma positive_schedule (C α β ε : ℝ) (hC : 0 < C)
    (hα : 0 < α) (hβ : 0 < β ∧ β ≤ 1 / 2) (hε : 0 < ε) :
    0 < repetitions β ∧ 0 < thresholds C α ∧
    0 < validationSize C α β ε (repetitions β) (thresholds C α) := by
  have hk : 0 < repetitions β := by
    apply Nat.ceil_pos.mpr
    apply div_pos
    · apply Real.log_pos
      exact (lt_div_iff₀ hβ.1).2 (by linarith [hβ.2])
    · exact Real.log_pos (by norm_num)
  have hM : 0 < thresholds C α := Nat.ceil_pos.mpr (div_pos hC hα)
  refine ⟨hk, hM, ?_⟩
  apply Nat.ceil_pos.mpr
  apply mul_pos
  · apply mul_pos hC
    exact add_pos (sq_pos_of_pos (inv_pos.mpr hα)) (inv_pos.mpr (mul_pos hε hα))
  · apply Real.log_pos
    have hk' : (1 : ℝ) ≤ repetitions β := by exact_mod_cast hk
    have hM' : (1 : ℝ) ≤ thresholds C α := by exact_mod_cast hM
    apply (lt_div_iff₀ hβ.1).2
    nlinarith [mul_le_mul hk' hM' (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ repetitions β)]

lemma sample_size_bound (C c α β ε δ : ℝ) (d p : ℕ)
    (hC : 0 < C) (hc : 0 < c) (hα : 0 < α)
    (hβ : 0 < β ∧ β ≤ 1 / 2) (hε : 0 < ε) (hδ : 0 < δ ∧ δ ≤ 1 / 2) :
    let k := repetitions β
    let M := thresholds C α
    let n₀ := trainingSize C c α ε δ d p
    let m := validationSize C α β ε k M
    ((k * n₀ + m : ℕ) : ℝ) ≤ (k : ℝ) *
      (3 + 4 * C ^ 2 * featureDimension d p / (c ^ 2 * α ^ 2) +
        4 * C * featureDimension d p * Real.sqrt (Real.log (1 / δ)) / (c * ε * α)) +
      1 + C * (α⁻¹ ^ 2 + (ε * α)⁻¹) * Real.log ((k : ℝ) * M / β) := by
  dsimp only
  have htrain := (training_schedule C c α ε δ d p hC hc hα hε (log_recip_nonneg δ hδ)).2.2
  have hpos := positive_schedule C α β ε hC hα hβ hε
  have hval : (validationSize C α β ε (repetitions β) (thresholds C α) : ℝ) <
      C * (α⁻¹ ^ 2 + (ε * α)⁻¹) *
        Real.log ((repetitions β : ℝ) * thresholds C α / β) + 1 := by
    apply Nat.ceil_lt_add_one
    have hm := (Nat.ceil_pos.mp hpos.2.2)
    exact hm.le
  push_cast
  have hh := mul_le_mul_of_nonneg_left htrain (Nat.cast_nonneg (repetitions β))
  linarith
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma training_dimension_le (C c α ε δ : ℝ) (d p n : ℕ)
    (hC : 1 ≤ C) (hc : 0 < c ∧ c ≤ 1 / 4) (hα : 0 < α ∧ α ≤ 1 / 2)
    (hε : 0 < ε) (hb : blockCondition C c α ε δ d p n) : featureDimension d p ≤ n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hb.1; omega : 0 < n)
  have hnon : 0 ≤ radius d p * Real.sqrt ((featureDimension d p : ℝ) * Real.log (1 / δ)) /
      (ε * n) := by unfold radius; positivity
  have hs0 : 0 ≤ Real.sqrt ((featureDimension d p : ℝ) / n) := Real.sqrt_nonneg _
  have hs : Real.sqrt ((featureDimension d p : ℝ) / n) ≤ 1 := by
    have hh := hb.2
    have hca : c * α ≤ 1 := by nlinarith [hc.2, hα.2]
    nlinarith
  have hsq : (featureDimension d p : ℝ) / n ≤ 1 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (featureDimension d p : ℝ) / n by positivity)]
  have hh := (div_le_iff₀ hn).mp hsq
  exact_mod_cast (show (featureDimension d p : ℝ) ≤ n by linarith)

lemma degree_dimension_le (d p : ℕ) (hd : 1 ≤ d) : p + 1 ≤ featureDimension d p := by
  have hh := Nat.choose_le_choose p (show p + 1 ≤ d + p by omega)
  simpa [featureDimension, Nat.choose_succ_self_right] using hh

lemma thresholds_le_degree (C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α ∧ α ≤ 1 / 2) :
    thresholds C α ≤ scheduledDegree C α := by
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_left hC (sq_pos_of_pos hα.1)
  nlinarith [hα.1, hα.2]

end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.PublicOptimizerBranch
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
noncomputable def zeroOptimizer (d p : ℕ) : ProbabilityMeasure (UnitBall d p) :=
  ⟨Measure.dirac ⟨0,by simp⟩,by infer_instance⟩
noncomputable def operationalOptimizer : Optimizer := fun d p n ε δ S =>
  if featureDimension d p ≤ n then concreteOptimizer d p n ε δ S else zeroOptimizer d p
lemma operationalOptimizer_eq (d p n : ℕ) (h : featureDimension d p ≤ n) (ε δ : ℝ) :
    operationalOptimizer d p n ε δ = concreteOptimizer d p n ε δ := by
  funext S
  simp only [operationalOptimizer,if_pos h]
lemma operationalOptimizer_measurable (d p n : ℕ) (ε δ : ℝ) :
    Measurable (fun S => (operationalOptimizer d p n ε δ S : Measure (UnitBall d p))) := by
  by_cases h : featureDimension d p ≤ n
  · simpa only [operationalOptimizer,if_pos h] using concreteOptimizer_measurable d p n ε δ
  · simp only [operationalOptimizer,if_neg h]
    exact measurable_const
lemma operationalOptimizer_private (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) :
    PrivateUniformGen.Characterization.IsDP (operationalOptimizer d p n ε δ) ε δ := by
  by_cases h : featureDimension d p ≤ n
  · rw [operationalOptimizer_eq d p n h]
    exact concreteOptimizer_private d p n hn ε δ hε hδ
  · intro S S' hS A hA
    simp only [operationalOptimizer,if_neg h]
    have hmass : 0 ≤ (zeroOptimizer d p : Measure (UnitBall d p)).real A := measureReal_nonneg
    have hexp : 1 ≤ Real.exp ε := Real.one_le_exp_iff.mpr hε.1.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hexp) hmass,hδ.1]
lemma empiricalLoss_zero (d p n : ℕ) (hn : 0 < n) (S : Fin n → Example d) : empiricalLoss d p S 0 = 1 := by
  have hi (i : Fin n) : |score d p 0 (S i).1-label (S i).2| = 1 := by
    simp only [score,inner_zero_left,zero_sub,abs_neg,label_abs]
  simp only [empiricalLoss,hi,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (by exact_mod_cast hn.ne')
lemma zero_branch_rate (d p n : ℕ) (hn : 0 < n) (hD : n < featureDimension d p) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) :
    1 ≤ 120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDR : (n : ℝ) < featureDimension d p := by exact_mod_cast hD
  have hlog := privacyLog_lower δ hδ
  have hroot : 1/2 ≤ Real.sqrt (Real.log (1/δ)) := by
    nlinarith [Real.sq_sqrt (log_recip_nonneg δ hδ),Real.sqrt_nonneg (Real.log (1/δ))]
  have hrootmul := mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg (featureDimension d p) : (0 : ℝ) ≤ _)
  rw [show 120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ)) =
    120*(radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))) by ring,
    radius_sqrt_mul d p _ (log_recip_nonneg δ hδ)]
  apply (le_div_iff₀ (mul_pos hnR hε.1)).mpr
  nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hε.2)]
lemma operationalOptimizer_excess (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) (S : Fin n → Example d) :
    Integrable (fun v : UnitBall d p => empiricalLoss d p S v.val-
      sInf (empiricalLoss d p S '' Metric.closedBall 0 1))
      (operationalOptimizer d p n ε δ S : Measure (UnitBall d p)) ∧
    (∫ v : UnitBall d p, empiricalLoss d p S v.val-sInf (empiricalLoss d p S '' Metric.closedBall 0 1)
      ∂(operationalOptimizer d p n ε δ S : Measure (UnitBall d p))) ≤
        120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) := by
  by_cases h : featureDimension d p ≤ n
  · rw [operationalOptimizer_eq d p n h]
    exact concreteOptimizer_excess d p n hn ε δ hε hδ S
  · have he : operationalOptimizer d p n ε δ S = zeroOptimizer d p := if_neg h
    rw [he]
    have hm : (zeroOptimizer d p : Measure (UnitBall d p)) = Measure.dirac (⟨0,by simp⟩ : UnitBall d p) := rfl
    rw [hm]
    refine ⟨integrable_dirac (by simp),?_⟩
    rw [integral_dirac,empiricalLoss_zero d p n hn S]
    obtain ⟨v,hv⟩ := empiricalLoss_minimum_attained d p S
    have hnon : 0 ≤ sInf (empiricalLoss d p S '' Metric.closedBall 0 1) := by
      rw [← hv]
      exact empiricalLoss_nonneg d p S v.val
    exact (sub_le_self 1 hnon).trans (zero_branch_rate d p n hn (by omega) ε δ hε hδ)
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.OptimizerRealizationBridge
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma operationalOptimizer_raw_law (d p n : ℕ) (ε δ : ℝ) (S : Fin n → Example d) :
    (operationalOptimizer d p n ε δ S : Measure (UnitBall d p)).map Subtype.val =
      orderedRegressionRawLaw d p n ε δ (coefficientIndexEquiv d p) S := by
  by_cases h : featureDimension d p ≤ n
  · simp only [operationalOptimizer,if_pos h]
    change ((Measure.pi (fun _ : Fin (n+1) => RegressionGeometry.regressionNoiseLaw n (featureDimension d p))).map
      (optimizerDraw d p n ε δ S)).map Subtype.val = _
    rw [Measure.map_map measurable_subtype_coe (optimizerDraw_measurable d p n ε δ S)]
    simp only [orderedRegressionRawLaw,if_pos h]
    rfl
  · simp only [operationalOptimizer,if_neg h,orderedRegressionRawLaw]
    change (Measure.dirac (⟨0,by simp⟩ : UnitBall d p)).map Subtype.val = _
    simp only [Measure.map_dirac]
lemma operationalOptimizer_realizes : RealizesOrderedRegression operationalOptimizer :=
  ⟨coefficientIndexEquiv,fun _ _ _ => rfl,operationalOptimizer_raw_law⟩
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AlgorithmInfrastructure
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable
namespace PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure

lemma continuous_hermite (d : ℕ) (κ : Fin d → ℕ) : Continuous (hermite d κ) := by
  unfold hermite AMPLowDeg.RankOne.hermNorm
  fun_prop

lemma continuous_features (d p : ℕ) : Continuous (features d p) := by
  unfold features
  apply Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Index d p => ℝ))
  apply continuous_pi
  intro κ
  exact continuous_hermite d (fun i => (κ.val i).val)

lemma radius_pos (d p : ℕ) : 0 < radius d p := by
  unfold radius
  have hD : 0 < featureDimension d p := Nat.choose_pos (by omega)
  have hD' : (0 : ℝ) < featureDimension d p := by exact_mod_cast hD
  positivity

lemma continuous_clipped (d p : ℕ) : Continuous (clipped d p) := by
  unfold clipped clipScale
  have hs : Continuous (fun x : Vec d => radius d p / max (radius d p) ‖features d p x‖) := by
    apply continuous_const.div (continuous_const.max (continuous_features d p).norm)
    intro x
    exact (lt_of_lt_of_le (radius_pos d p) (le_max_left _ _)).ne'
  exact continuous_smul.comp (hs.prodMk (continuous_features d p))

lemma measurable_sign : Measurable (PrivateAgnosticHalfspace.Gaussian.sign : ℝ → Bool) := by
  apply measurable_to_bool
  have heq : PrivateAgnosticHalfspace.Gaussian.sign ⁻¹' {true} = Set.Ici (0 : ℝ) := by
    ext x
    simp [PrivateAgnosticHalfspace.Gaussian.sign]
  rw [heq]
  exact measurableSet_Ici

lemma measurable_candidate (d p M : ℕ) (v : Coeff d p) (l : Fin M) :
    Measurable (candidate d p M v l) := by
  unfold candidate score
  apply measurable_sign.comp
  exact ((continuous_const.inner (continuous_clipped d p)).sub continuous_const).measurable

lemma measurable_pi_measure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Ω → Measure (Y i)) (hκ : ∀ i, Measurable (κ i))
    (hp : ∀ i ω, IsProbabilityMeasure (κ i ω)) :
    Measurable (fun ω => Measure.pi (fun i => κ i ω)) := by
  letI (i : ι) (ω : Ω) := hp i ω
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.univ.pi '' Set.univ.pi (fun i : ι => {s : Set (Y i) | MeasurableSet s}))
  · exact generateFrom_pi.symm
  · exact isPiSystem_pi
  · intro s hs
    rcases hs with ⟨t,ht,rfl⟩
    have ht' : ∀ i, MeasurableSet (t i) := fun i => ht i (Set.mem_univ _)
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (ht' i)).comp (hκ i))
end PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure
namespace PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure
noncomputable def selectionLaw (d p k M m : ℕ) (ε : ℝ)
    (v : Fin k → UnitBall d p) (V : Fin m → Example d) : Measure (Output d p M) :=
  let w := fun jl : Fin k × Fin M =>
    Real.exp (-ε * m * empiricalError V (candidate d p M (v jl.1).val jl.2) / 2)
  ∑ jl : Fin k × Fin M,
    ENNReal.ofReal (w jl / ∑ il : Fin k × Fin M, w il) • Measure.dirac (v jl.1, jl.2)

lemma selectionLaw_probability (d p k M m : ℕ) (hk : 0 < k) (hM : 0 < M)
    (ε : ℝ) (v : Fin k → UnitBall d p) (V : Fin m → Example d) :
    IsProbabilityMeasure (selectionLaw d p k M m ε v V) := by
  classical
  have hne : (Finset.univ : Finset (Fin k × Fin M)).Nonempty :=
    ⟨(⟨0,hk⟩,⟨0,hM⟩), Finset.mem_univ _⟩
  have hw : 0 < ∑ jl : Fin k × Fin M,
      Real.exp (-ε * m * empiricalError V (candidate d p M (v jl.1).val jl.2) / 2) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hne
  constructor
  simp only [selectionLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← Finset.sum_div]
  rw [div_self hw.ne']
  norm_num

lemma measurable_measure_smul {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (f : Ω → ℝ≥0∞) (κ : Ω → Measure Y) (hf : Measurable f) (hκ : Measurable κ) :
    Measurable (fun ω => f ω • κ ω) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.smul_apply, smul_eq_mul]
  exact hf.mul ((Measure.measurable_coe hU).comp hκ)

lemma measurable_selectionLaw (d p k M m : ℕ) (ε : ℝ) :
    Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
      selectionLaw d p k M m ε z.1 z.2) := by
  classical
  have hscore (j : Fin k) (l : Fin M) (i : Fin m) :
      Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        candidate d p M (z.1 j).val l (z.2 i).1) := by
    have hv : Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        (z.1 j).val) :=
      measurable_subtype_coe.comp ((measurable_pi_apply j).comp measurable_fst)
    have hx : Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        (z.2 i).1) :=
      measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
    unfold candidate score
    exact measurable_sign.comp ((hv.inner ((continuous_clipped d p).measurable.comp hx)).sub_const _)

  have her (jl : Fin k × Fin M) :
      Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        empiricalError z.2 (candidate d p M (z.1 jl.1).val jl.2)) := by
    unfold empiricalError
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_eq_fun (hscore jl.1 jl.2 i)
      (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd))
  have hw (jl : Fin k × Fin M) :
      Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        Real.exp (-ε * m * empiricalError z.2 (candidate d p M (z.1 jl.1).val jl.2) / 2)) :=
    (((her jl).const_mul (-ε * m)).div_const 2).exp
  unfold selectionLaw
  apply Finset.measurable_sum
  intro jl _
  apply measurable_measure_smul
  · exact ((hw jl).div (Finset.measurable_sum _ (fun il _ => hw il))).ennreal_ofReal
  · apply Measure.measurable_dirac.comp
    exact ((measurable_pi_apply jl.1).comp measurable_fst).prodMk measurable_const

lemma measurable_prod_measures {Ω Y Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Ω → Measure Y) (η : Ω → Measure Z) (hκ : Measurable κ) (hη : Measurable η)
    (hκp : ∀ ω, IsProbabilityMeasure (κ ω)) (hηp : ∀ ω, IsProbabilityMeasure (η ω)) :
    Measurable (fun ω => (κ ω).prod (η ω)) := by
  letI (ω : Ω) := hκp ω
  letI (ω : Ω) := hηp ω
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm isPiSystem_prod
  intro U hU
  rcases hU with ⟨V,hV,W,hW,rfl⟩
  simp_rw [Measure.prod_prod]
  exact ((Measure.measurable_coe hV).comp hκ).mul ((Measure.measurable_coe hW).comp hη)

lemma bind_map_eq {Ω Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Ω) (f : Ω → Y) (hf : Measurable f) (κ : Y → Measure Z)
    (hκ : Measurable κ) : (μ.map f).bind κ = μ.bind (κ ∘ f) := by
  ext U hU
  rw [Measure.bind_apply hU hκ.aemeasurable, Measure.bind_apply hU (hκ.comp hf).aemeasurable]
  simpa only [Function.comp_apply] using lintegral_map ((Measure.measurable_coe hU).comp hκ) hf
end PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure
namespace PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure
noncomputable def trainingBlocks (d k n₀ m : ℕ)
    (S : Fin (k * n₀ + m) → Example d) : Fin k → Fin n₀ → Example d := fun j i =>
  S ⟨j.val * n₀ + i.val, by
    have hj := Nat.mul_le_mul_right n₀ (Nat.succ_le_of_lt j.isLt)
    have hi := i.isLt
    nlinarith⟩
noncomputable def validationBlock (d k n₀ m : ℕ)
    (S : Fin (k * n₀ + m) → Example d) : Fin m → Example d := fun i =>
  S ⟨k * n₀ + i.val, by omega⟩

lemma algorithmLaw_eq (O : Optimizer) (d p k M n₀ m : ℕ) (ε δ : ℝ)
    (S : Fin (k * n₀ + m) → Example d) :
    algorithmLaw O d p k M n₀ m ε δ S =
      (Measure.pi (fun j : Fin k => (O d p n₀ ε δ (trainingBlocks d k n₀ m S j) : Measure (UnitBall d p)))).bind
        (fun v => selectionLaw d p k M m ε v (validationBlock d k n₀ m S)) := rfl

lemma algorithmLaw_probability (O : Optimizer) (d p k M n₀ m : ℕ)
    (hk : 0 < k) (hM : 0 < M) (ε δ : ℝ) (S : Fin (k * n₀ + m) → Example d) :
    IsProbabilityMeasure (algorithmLaw O d p k M n₀ m ε δ S) := by
  rw [algorithmLaw_eq]
  exact isProbabilityMeasure_bind
    ((measurable_selectionLaw d p k M m ε).comp (measurable_id.prodMk measurable_const)).aemeasurable
    (ae_of_all _ (fun v => selectionLaw_probability d p k M m hk hM ε v _))

lemma measurable_algorithmLaw (O : Optimizer) (d p k M n₀ m : ℕ) (ε δ : ℝ)
    (hOmeas : Measurable (fun S => (O d p n₀ ε δ S : Measure (UnitBall d p)))) :
    Measurable (fun S => algorithmLaw O d p k M n₀ m ε δ S) := by
  let train := fun S : Fin (k * n₀ + m) → Example d =>
    Measure.pi (fun j : Fin k => (O d p n₀ ε δ (trainingBlocks d k n₀ m S j) : Measure (UnitBall d p)))
  have htrain : Measurable train := by
    apply measurable_pi_measure _ _ (fun _ _ => by infer_instance)
    intro j
    apply hOmeas.comp
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply _
  have hv : Measurable (validationBlock d k n₀ m) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply _
  have hpair : Measurable (fun S => (train S).prod (Measure.dirac (validationBlock d k n₀ m S))) :=
    measurable_prod_measures _ _ htrain (Measure.measurable_dirac.comp hv)
      (fun _ => by infer_instance) (fun _ => by infer_instance)
  have hfull := (Measure.measurable_bind' (measurable_selectionLaw d p k M m ε)).comp hpair
  have heq (S : Fin (k * n₀ + m) → Example d) :
      ((train S).prod (Measure.dirac (validationBlock d k n₀ m S))).bind
        (fun z => selectionLaw d p k M m ε z.1 z.2) = algorithmLaw O d p k M n₀ m ε δ S := by
    rw [Measure.prod_dirac]
    have hmap := bind_map_eq (train S)
      (fun x : Fin k → UnitBall d p => (x, validationBlock d k n₀ m S))
      (measurable_id.prodMk measurable_const)
      (fun z => selectionLaw d p k M m ε z.1 z.2) (measurable_selectionLaw d p k M m ε)
    exact hmap.trans (algorithmLaw_eq O d p k M n₀ m ε δ S).symm
  change Measurable (fun S => ((train S).prod (Measure.dirac (validationBlock d k n₀ m S))).bind
    (fun z => selectionLaw d p k M m ε z.1 z.2)) at hfull
  simpa only [heq] using hfull
end PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure

namespace PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure
lemma selectionLaw_reindex (d p k M m : ℕ) (ε : ℝ)
    (v : Fin k → UnitBall d p) (V : Fin m → Example d) :
    let e : Fin (k * M) ≃ Fin k × Fin M := finProdFinEquiv.symm
    (validationLaw (fun j => candidate d p M (v (e j).1).val (e j).2) ε V).map
      (fun j => (v (e j).1, (e j).2)) = selectionLaw d p k M m ε v V := by
  classical
  let e : Fin (k * M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  let out := fun j : Fin (k * M) => (v (e j).1, (e j).2)
  have hout : Measurable out := measurable_of_countable _
  let w := fun jl : Fin k × Fin M => Real.exp (-ε * m * empiricalError V
    (candidate d p M (v jl.1).val jl.2) / 2)
  have hden : ∑ j : Fin (k * M), w (e j) = ∑ jl : Fin k × Fin M, w jl := e.sum_comp w
  change (∑ j : Fin (k * M), ENNReal.ofReal (w (e j) / ∑ i, w (e i)) •
    Measure.dirac j).map out = ∑ jl : Fin k × Fin M,
      ENNReal.ofReal (w jl / ∑ il, w il) • Measure.dirac (v jl.1, jl.2)
  rw [Measure.map_finset_sum' hout.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' hout, hden]
  exact e.sum_comp (fun jl => ENNReal.ofReal (w jl / ∑ il, w il) • Measure.dirac (v jl.1, jl.2))

end PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure
end

section
-- Solutions.FiniteIndependentKernels
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open AlgorithmInfrastructure
lemma finite_pi_bind_eq {ι X Y : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (κ : ι → X → Measure Y)
    (hκ : ∀ i, Measurable (κ i)) (hprob : ∀ i x, IsProbabilityMeasure (κ i x)) :
    (Measure.pi μ).bind (fun s : ι → X => Measure.pi (fun i => κ i (s i))) =
      Measure.pi (fun i => (μ i).bind (κ i)) := by
  letI (i : ι) (x : X) := hprob i x
  letI (i : ι) : IsProbabilityMeasure ((μ i).bind (κ i)) :=
    isProbabilityMeasure_bind (hκ i).aemeasurable (ae_of_all _ (fun x => hprob i x))
  have hk : Measurable (fun s : ι → X => Measure.pi (fun i => κ i (s i))) :=
    measurable_pi_measure (fun i (s : ι → X) => κ i (s i)) (fun i => (hκ i).comp (measurable_pi_apply i))
      (fun i (s : ι → X) => hprob i (s i))
  symm
  apply Measure.pi_eq
  intro A hA
  rw [Measure.bind_apply (MeasurableSet.univ_pi hA) hk.aemeasurable]
  simp_rw [Measure.pi_pi]
  have hi := iIndepFun_pi (μ := μ) (X := fun i x => κ i x (A i))
    (fun i => ((Measure.measurable_coe (hA i)).comp (hκ i)).aemeasurable)
  have hprod : (∫⁻ s : ι → X, ∏ i : ι, κ i (s i) (A i) ∂Measure.pi μ) =
      ∏ i : ι, ∫⁻ s : ι → X, κ i (s i) (A i) ∂Measure.pi μ := by
    exact lintegral_prod_eq_prod_lintegral_of_indepFun univ
      (fun (i : ι) (s : ι → X) => κ i (s i) (A i)) hi
      (fun i => ((Measure.measurable_coe (hA i)).comp ((hκ i).comp (measurable_pi_apply i))))
  rw [hprod]
  apply prod_congr rfl
  intro i hi
  rw [Measure.bind_apply (hA i) (hκ i).aemeasurable]
  have hp := measurePreserving_eval μ i
  have he : (∫⁻ s : ι → X, κ i (s i) (A i) ∂Measure.pi μ) =
      ∫⁻ x : X, κ i x (A i) ∂(Measure.pi μ).map (Function.eval i) := by
    exact (lintegral_map ((Measure.measurable_coe (hA i)).comp (hκ i)) hp.measurable).symm
  rw [he,hp.map_eq]
lemma finite_curry_preserving {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] :
    MeasurePreserving (fun s : (ι × κ) → X => fun i j => s (i,j))
      (Measure.pi (fun _ : ι × κ => P)) (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => P))) := by
  refine ⟨by fun_prop,?_⟩
  have h := Measure.infinitePi_map_curry (fun _ : ι => fun _ : κ => P)
  simp only [Measure.infinitePi_eq_pi] at h
  convert! h using 1
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.SampleBlockLaw
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open AlgorithmInfrastructure
noncomputable def sampleBlockIndex (k n₀ m : ℕ) : (Fin k × Fin n₀) ⊕ Fin m ≃ Fin (k*n₀+m) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin m))).trans finSumFinEquiv
lemma sampleBlocks_preserving {X : Type*} [MeasurableSpace X]
    (k n₀ m : ℕ) (P : Measure X) [IsProbabilityMeasure P] :
    MeasurePreserving
      (fun S : Fin (k*n₀+m) → X =>
        ((fun (j : Fin k) (i : Fin n₀) => S ⟨j.val*n₀+i.val,by nlinarith [j.isLt,i.isLt]⟩),
         (fun i : Fin m => S ⟨k*n₀+i.val,by omega⟩)))
      (Measure.pi (fun _ : Fin (k*n₀+m) => P))
      ((Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin n₀ => P))).prod
        (Measure.pi (fun _ : Fin m => P))) := by
  let I := (Fin k × Fin n₀) ⊕ Fin m
  let e := sampleBlockIndex k n₀ m
  have h1 := measurePreserving_piCongrLeft (fun _ : I => P) e.symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : I => P)
  have h3 := (finite_curry_preserving (ι := Fin k) (κ := Fin n₀) P).prod
    (MeasurePreserving.id (Measure.pi (fun _ : Fin m => P)))
  convert! h3.comp (h2.comp h1) using 1
  funext S
  apply Prod.ext
  · funext j i
    simp [e,sampleBlockIndex,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi,Equiv.sumPiEquivProdPi,Equiv.sumCongr,finProdFinEquiv,
      Function.comp_def,Prod.map_apply,Nat.mul_comm,Nat.add_comm]
  · funext i
    simp [e,sampleBlockIndex,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi,Equiv.sumPiEquivProdPi,Equiv.sumCongr,
      Function.comp_def,Prod.map_apply,Fin.natAdd]
lemma labeled_sampleBlocks_preserving (d k n₀ m : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P] :
    MeasurePreserving (fun S => (trainingBlocks d k n₀ m S,validationBlock d k n₀ m S))
      (Measure.pi (fun _ : Fin (k*n₀+m) => P))
      ((Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin n₀ => P))).prod (Measure.pi (fun _ : Fin m => P))) :=
  sampleBlocks_preserving k n₀ m P
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.BindProductLaw
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open AlgorithmInfrastructure
lemma map_bind_eq {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (κ : X → Measure Y) (hκ : Measurable κ) (f : Y → Z) (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun x => (κ x).map f) := by
  have hmap : Measurable (fun x : X => (κ x).map f) := by
    convert! (Measure.measurable_map f hf).comp hκ using 1
  ext A hA
  rw [Measure.map_apply hf hA,Measure.bind_apply (hA.preimage hf) hκ.aemeasurable,
    Measure.bind_apply hA hmap.aemeasurable]
  simp only [Measure.map_apply hf hA]
lemma prod_bind_eq {X W Z : Type*} [MeasurableSpace X] [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure W) [SFinite ν] (η : X × W → Measure Z) (hη : Measurable η) :
    (μ.prod ν).bind η = μ.bind (fun x => ν.bind (fun w => η (x,w))) := by
  rw [Measure.prod,Measure.bind_bind Measurable.map_prodMk_left.aemeasurable hη.aemeasurable]
  congr 1
  funext x
  exact bind_map_eq ν (Prod.mk x) measurable_prodMk_left η hη
lemma measurable_parameter_bind {X W Z : Type*} [MeasurableSpace X] [MeasurableSpace W] [MeasurableSpace Z]
    (ν : Measure W) [IsProbabilityMeasure ν] (η : X × W → Measure Z) (hη : Measurable η) :
    Measurable (fun x => ν.bind (fun w => η (x,w))) := by
  have hp : Measurable (fun x : X => (Measure.dirac x).prod ν) :=
    measurable_prod_measures _ _ Measure.measurable_dirac measurable_const (fun x => inferInstance) (fun x => inferInstance)
  have hm := (Measure.measurable_bind' hη).comp hp
  convert! hm using 1
  funext x
  change ν.bind (fun w => η (x,w)) = ((Measure.dirac x).prod ν).bind η
  rw [Measure.dirac_prod]
  exact (bind_map_eq ν (Prod.mk x) measurable_prodMk_left η hη).symm
lemma bind_prod_dirac {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (μ : Measure X) (ν : Measure W) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : X → Measure Y) (hκ : Measurable κ) (hprob : ∀ x, IsProbabilityMeasure (κ x)) :
    (μ.prod ν).bind (fun q : X × W => (κ q.1).prod (Measure.dirac q.2)) = (μ.bind κ).prod ν := by
  letI (x : X) := hprob x
  letI : IsProbabilityMeasure (μ.bind κ) := isProbabilityMeasure_bind hκ.aemeasurable (ae_of_all _ hprob)
  have hK : Measurable (fun q : X × W => (κ q.1).prod (Measure.dirac q.2)) :=
    measurable_prod_measures _ _ (hκ.comp measurable_fst) (Measure.measurable_dirac.comp measurable_snd)
      (fun q => hprob q.1) (fun q => inferInstance)
  symm
  apply Measure.prod_eq
  intro A B hA hB
  rw [Measure.bind_apply (hA.prod hB) hK.aemeasurable]
  simp_rw [Measure.prod_prod,Measure.dirac_apply' _ hB]
  have hf : AEMeasurable (fun x : X => κ x A) μ := by
    convert! ((Measure.measurable_coe hA).comp hκ).aemeasurable using 1
  have hg : AEMeasurable (B.indicator (fun _ : W => (1 : ℝ≥0∞))) ν := (measurable_const.indicator hB).aemeasurable
  have he : (∫⁻ q : X × W, κ q.1 A*B.indicator (fun _ => (1 : ℝ≥0∞)) q.2 ∂μ.prod ν) =
      (∫⁻ x, κ x A ∂μ)*(∫⁻ w, B.indicator (fun _ => (1 : ℝ≥0∞)) w ∂ν) :=
    lintegral_prod_mul hf hg
  have hInd : (∫⁻ w, B.indicator (fun _ : W => (1 : ℝ≥0∞)) w ∂ν) = ν B := by
    convert! lintegral_indicator_one (μ := ν) hB using 1
  calc
    _ = (∫⁻ x, κ x A ∂μ)*(∫⁻ w, B.indicator (fun _ => (1 : ℝ≥0∞)) w ∂ν) := by convert! he using 1
    _ = _ := by rw [hInd,Measure.bind_apply hA hκ.aemeasurable]
lemma measurable_bind_param {X Y W Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W] [MeasurableSpace Z]
    (κ : X → Measure Y) (hκ : Measurable κ) (hprob : ∀ x, IsProbabilityMeasure (κ x))
    (η : Y × W → Measure Z) (hη : Measurable η) :
    Measurable (fun q : X × W => (κ q.1).bind (fun y => η (y,q.2))) := by
  have hK : Measurable (fun q : X × W => (κ q.1).prod (Measure.dirac q.2)) :=
    measurable_prod_measures _ _ (hκ.comp measurable_fst) (Measure.measurable_dirac.comp measurable_snd)
      (fun q => hprob q.1) (fun q => inferInstance)
  have hm := (Measure.measurable_bind' hη).comp hK
  convert! hm using 1
  funext q
  change (κ q.1).bind (fun y => η (y,q.2)) = ((κ q.1).prod (Measure.dirac q.2)).bind η
  rw [Measure.prod_dirac]
  exact (bind_map_eq (κ q.1) (fun y => (y,q.2)) (measurable_id.prodMk measurable_const) η hη).symm
lemma bind_prod_swap {X Y W Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure W) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : X → Measure Y) (hκ : Measurable κ) (hprob : ∀ x, IsProbabilityMeasure (κ x))
    (η : Y × W → Measure Z) (hη : Measurable η) :
    (μ.prod ν).bind (fun q : X × W => (κ q.1).bind (fun y => η (y,q.2))) =
      ((μ.bind κ).prod ν).bind η := by
  have hK : Measurable (fun q : X × W => (κ q.1).prod (Measure.dirac q.2)) :=
    measurable_prod_measures _ _ (hκ.comp measurable_fst) (Measure.measurable_dirac.comp measurable_snd)
      (fun q => hprob q.1) (fun q => inferInstance)
  have hEq (q : X × W) : ((κ q.1).prod (Measure.dirac q.2)).bind η =
      (κ q.1).bind (fun y => η (y,q.2)) := by
    rw [Measure.prod_dirac]
    exact bind_map_eq (κ q.1) (fun y => (y,q.2)) (measurable_id.prodMk measurable_const) η hη
  rw [← bind_prod_dirac μ ν κ hκ hprob,Measure.bind_bind hK.aemeasurable hη.aemeasurable]
  congr 1
  funext q
  exact (hEq q).symm
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianMarginal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_marginal_integrable {d : ℕ} (P : Measure (Example d))
    (hP : P.map Prod.fst = gaussian d) (f : Vec d → ℝ) (hf : Integrable f (gaussian d)) :
    Integrable (fun z : Example d => f z.1) P := by
  have hfm : Integrable f (P.map Prod.fst) := by rw [hP]; exact hf
  convert! hfm.comp_measurable measurable_fst using 1
lemma gaussian_marginal_integral {d : ℕ} (P : Measure (Example d))
    (hP : P.map Prod.fst = gaussian d) (f : Vec d → ℝ) (hf : Integrable f (gaussian d)) :
    (∫ z : Example d, f z.1 ∂P) = ∫ x, f x ∂gaussian d := by
  rw [← hP,integral_map measurable_fst.aemeasurable (by rw [hP]; exact hf.aestronglyMeasurable)]
lemma label_difference (a b : Bool) : |label a-label b| = 2*(if a ≠ b then (1 : ℝ) else 0) := by
  cases a <;> cases b <;> norm_num [label]
lemma label_error_integral {X : Type*} [MeasurableSpace X] (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (h : X → Bool) (hh : Measurable h) :
    (∫ z, |label (h z.1)-label z.2| ∂P) = 2*error P h := by
  simp_rw [label_difference]
  rw [integral_const_mul,classification_error_integral P h hh]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RegressionDeviationBridge
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
noncomputable def coefficientFeatureMap (d p : ℕ) (x : Vec d) : Vec (featureDimension d p) :=
  coefficientIsometry d p (clipped d p x)
lemma coefficientFeatureMap_measurable (d p : ℕ) : Measurable (coefficientFeatureMap d p) :=
  (coefficientIsometry d p).continuous.measurable.comp (continuous_clipped d p).measurable
lemma risk_coefficient (d p : ℕ) (P : Measure (Example d)) (v : Coeff d p) :
    risk (featureDimension d p) (coefficientFeatureMap d p) P (coefficientIsometry d p v) =
      populationLoss d p P v := by
  unfold risk coefficientFeatureMap populationLoss score
  simp only [(coefficientIsometry d p).inner_map_map]
lemma empiricalRisk_coefficient (d p : ℕ) {n : ℕ} (S : Fin n → Example d) (v : Coeff d p) :
    empiricalRisk (featureDimension d p) (coefficientFeatureMap d p) S (coefficientIsometry d p v) =
      empiricalLoss d p S v := by
  unfold empiricalRisk coefficientFeatureMap empiricalLoss score
  simp only [(coefficientIsometry d p).inner_map_map]
noncomputable def coefficientDeviation (d p : ℕ) (P : Measure (Example d)) {n : ℕ} (S : Fin n → Example d) : ℝ :=
  deviation (featureDimension d p) (coefficientFeatureMap d p) P 1 S
lemma coefficientDeviation_bound (d p n : ℕ) (hn : 0 < n) (P : Measure (Example d)) [IsProbabilityMeasure P]
    (hP : P.map Prod.fst = gaussian d) :
    Integrable (coefficientDeviation d p P (n := n)) (Measure.pi (fun _ : Fin n => P)) ∧
    (∫ S, coefficientDeviation d p P S ∂Measure.pi (fun _ : Fin n => P)) ≤ 2*Real.sqrt ((featureDimension d p : ℝ)/n) ∧
    ∀ (S : Fin n → Example d) (v : UnitBall d p),
      populationLoss d p P v.val ≤ coefficientDeviation d p P S+empiricalLoss d p S v.val := by
  have hfG : Integrable (fun x : Vec d => ‖clipped d p x‖^2) (gaussian d) :=
    (memLp_two_iff_integrable_sq_norm (clipped_memLp_two d p).aestronglyMeasurable).mp (clipped_memLp_two d p)
  have hf : Integrable (fun z : Example d => ‖coefficientFeatureMap d p z.1‖^2) P := by
    simpa only [coefficientFeatureMap,(coefficientIsometry d p).norm_map] using
      gaussian_marginal_integrable P hP _ hfG
  have hmoment : (∫ z : Example d, ‖coefficientFeatureMap d p z.1‖^2 ∂P) ≤ featureDimension d p := by
    simp only [coefficientFeatureMap,(coefficientIsometry d p).norm_map]
    rw [gaussian_marginal_integral P hP _ hfG]
    exact clipped_second_moment d p
  have h := lemma_B_7 (featureDimension d p) n hn P (coefficientFeatureMap d p)
    (coefficientFeatureMap_measurable d p) hf hmoment 1 (by norm_num)
  refine ⟨h.2.2.1,by simpa only [coefficientDeviation,mul_one,one_mul] using h.2.2.2,?_⟩
  intro S v
  have he : risk (featureDimension d p) (coefficientFeatureMap d p) P (coefficientIsometry d p v.val)-
      empiricalRisk (featureDimension d p) (coefficientFeatureMap d p) S (coefficientIsometry d p v.val) ≤
        coefficientDeviation d p P S := by
    apply le_csSup (h.2.1 S)
    refine ⟨coefficientIsometry d p v.val,?_,rfl⟩
    simpa only [Metric.mem_closedBall,dist_zero_right,(coefficientIsometry d p).norm_map] using v.property
  rw [risk_coefficient,empiricalRisk_coefficient] at he
  linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.HermitePredictorNorm
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma polynomialPredictor_norm_sq (d p : ℕ) (v : Coeff d p) :
    (∫ x, (polynomialPredictor d p v x)^2 ∂gaussian d) = ‖v‖^2 := by
  let h : Index d p → Vec d → ℝ := fun κ => hermite d (fun i => (κ.val i).val)
  have horth := ((lemma_B_8 d).2.2.2 p).2.2
  have hi (κ ξ : Index d p) : Integrable
      (fun x => (v κ*v ξ)*(h κ x*h ξ x)) (gaussian d) :=
    ((horth κ ξ).1).const_mul _
  have he (x : Vec d) : (polynomialPredictor d p v x)^2 =
      ∑ κ : Index d p, ∑ ξ : Index d p, (v κ*v ξ)*(h κ x*h ξ x) := by
    change (inner ℝ v (features d p x))^2 = _
    have hin : inner ℝ v (features d p x) = ∑ κ : Index d p, v κ*h κ x := by
      simp [PiLp.inner_apply, RCLike.inner_apply, features, h, mul_comm]
    rw [hin]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro κ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun κ _ => integrable_finsetSum Finset.univ (fun ξ _ => hi κ ξ))]
  simp_rw [integral_finsetSum Finset.univ (fun ξ _ => hi _ ξ), integral_const_mul]
  have ho (κ ξ : Index d p) : (∫ x, h κ x*h ξ x ∂gaussian d) = if κ=ξ then 1 else 0 :=
    (horth κ ξ).2
  simp_rw [ho]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [mul_ite, pow_two]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.HalfspacePadding
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma polynomialPredictor_padding (d p q : ℕ) (hpq : p ≤ q) (v : Coeff d p) :
    ∃ w : Coeff d q, polynomialPredictor d q w = polynomialPredictor d p v ∧ ‖w‖ = ‖v‖ := by
  have hp : polynomialPredictor d p v ∈ polynomialFunctions d p := by
    rw [((lemma_B_8 d).2.2.2 p).1]
    exact ⟨v,rfl⟩
  obtain ⟨Q,hQ,hEval⟩ := hp
  have hq : polynomialPredictor d p v ∈ polynomialFunctions d q :=
    ⟨Q,hQ.trans hpq,hEval⟩
  rw [((lemma_B_8 d).2.2.2 q).1] at hq
  obtain ⟨w,hw⟩ := hq
  refine ⟨w,hw,?_⟩
  have hn : ‖w‖^2 = ‖v‖^2 := by
    rw [← polynomialPredictor_norm_sq d q w,← polynomialPredictor_norm_sq d p v,hw]
  nlinarith [norm_nonneg w,norm_nonneg v]
lemma halfspace_approximation_fixed_degree :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (α : ℝ), 0 < α ∧ α < 1 →
      ∀ (p : ℕ), C/α^2 ≤ (p : ℝ) → ∀ (w : Vec d) (t : ℝ), ∃ v : UnitBall d p,
        Integrable (fun x => |label (affine d w t x)-polynomialPredictor d p v.val x|) (gaussian d) ∧
        (∫ x, |label (affine d w t x)-polynomialPredictor d p v.val x| ∂gaussian d) ≤ α := by
  obtain ⟨C,hC,happ⟩ := lemma_B_10
  refine ⟨C,hC,?_⟩
  intro d hd α hα p hp w t
  obtain ⟨q,v,hq,hv,hint,herr⟩ := happ d hd α hα w t
  have hqp : q ≤ p := by exact_mod_cast hq.trans hp
  obtain ⟨u,hu,hnorm⟩ := polynomialPredictor_padding d q p hqp v
  refine ⟨⟨u,by simpa only [hnorm] using hv⟩,?_⟩
  simpa only [hu] using And.intro hint herr
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ClippedHalfspaceApproximation
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
local instance (d : ℕ) : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
lemma minimumLoss_le (d p : ℕ) (P : Measure (Example d)) (v : UnitBall d p) :
    minimumLoss d p P ≤ populationLoss d p P v.val := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro z ⟨w,hw,rfl⟩
    exact populationLoss_nonneg d p P w
  · refine ⟨v.val,?_,rfl⟩
    simpa only [Metric.mem_closedBall,dist_zero_right] using v.property
lemma clipped_halfspace_loss (d p : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P]
    (hP : P.map Prod.fst = gaussian d) (w : Vec d) (t : ℝ) (v : Coeff d p)
    (hint : Integrable (fun x => |label (affine d w t x)-polynomialPredictor d p v x|) (gaussian d)) :
    populationLoss d p P v ≤ 2*error P (affine d w t) +
      (∫ x, |label (affine d w t x)-polynomialPredictor d p v x| ∂gaussian d) +
      (gaussian d).real {x | radius d p < ‖features d p x‖} := by
  let E := fun z : Example d => |label (affine d w t z.1)-polynomialPredictor d p v z.1|
  let B := fun z : Example d => |label (affine d w t z.1)-label z.2|
  let A := {x : Vec d | radius d p < ‖features d p x‖}
  let H := fun z : Example d => A.indicator (fun _ => (1 : ℝ)) z.1
  have hA : MeasurableSet A := measurableSet_lt measurable_const (continuous_features d p).norm.measurable
  have hE : Integrable E P := gaussian_marginal_integrable P hP _ hint
  have hc : Measurable (affine d w t) := sign_measurable_grid.comp (by fun_prop)
  have hB : Integrable B P := by
    unfold B
    simp_rw [label_difference]
    exact (classification_error_integrable P (affine d w t) hc).const_mul 2
  have hHgauss : Integrable (A.indicator (fun _ => (1 : ℝ))) (gaussian d) := (integrable_const _).indicator hA
  have hH : Integrable H P := gaussian_marginal_integrable P hP _ hHgauss
  have hpoint (z : Example d) : |score d p v z.1-label z.2| ≤ E z+B z+H z := by
    have h := clipping_loss_bound (clipScale d p z.1) (polynomialPredictor d p v z.1)
      (label (affine d w t z.1)) (label z.2) (clipScale_bounds d p z.1)
      (label_abs _) (label_abs _)
    have hs : score d p v z.1 = clipScale d p z.1*polynomialPredictor d p v z.1 := by
      simp only [score,clipped,polynomialPredictor,inner_smul_right]
    rw [hs]
    rw [abs_sub_comm (polynomialPredictor d p v z.1) (label (affine d w t z.1))] at h
    exact h.trans (add_le_add le_rfl (clipping_scale_loss_indicator d p z.1))
  have hR : Integrable (fun z => E z+B z+H z) P := by convert! (hE.add hB).add hH using 1
  have hm := integral_mono (loss_integrable d p P v) hR hpoint
  have hsum : (∫ z, E z+B z+H z ∂P) =
      (∫ z, E z ∂P)+(∫ z, B z ∂P)+(∫ z, H z ∂P) := by
    rw [integral_add (f := fun z => E z+B z) (g := H) (hE.add hB) hH,
      integral_add hE hB]
  rw [hsum,gaussian_marginal_integral P hP _ hint,label_error_integral P (affine d w t) hc,
    gaussian_marginal_integral P hP _ hHgauss] at hm
  have htail : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂gaussian d) = (gaussian d).real A := by
    rw [integral_indicator hA,integral_const]
    simp
  rw [htail] at hm
  change populationLoss d p P v ≤ _ at hm
  dsimp [A] at hm
  linarith
lemma minimumLoss_halfspace_bound (d p : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P]
    (hP : P.map Prod.fst = gaussian d) (a : ℝ)
    (htail : (gaussian d).real {x | radius d p < ‖features d p x‖} ≤ a)
    (happ : ∀ (w : Vec d) (t : ℝ), ∃ v : UnitBall d p,
      Integrable (fun x => |label (affine d w t x)-polynomialPredictor d p v.val x|) (gaussian d) ∧
      (∫ x, |label (affine d w t x)-polynomialPredictor d p v.val x| ∂gaussian d) ≤ a) :
    minimumLoss d p P ≤ 2*opt d P+2*a := by
  have hbound (w : Vec d) (t : ℝ) : minimumLoss d p P ≤ 2*error P (affine d w t)+2*a := by
    obtain ⟨v,hv,herr⟩ := happ w t
    have h := (minimumLoss_le d p P v).trans (clipped_halfspace_loss d p P hP w t v.val hv)
    linarith
  have hlow : (minimumLoss d p P-2*a)/2 ≤ opt d P := by
    apply le_csInf (Set.range_nonempty _)
    rintro z ⟨⟨w,t⟩,rfl⟩
    have h := hbound w t
    linarith
  linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.OneBlockRegression
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
noncomputable def concreteOptimizerKernel (d p n : ℕ) (ε δ : ℝ) :
    Kernel (Fin n → Example d) (UnitBall d p) :=
  ⟨fun S => (concreteOptimizer d p n ε δ S : Measure (UnitBall d p)),concreteOptimizer_measurable d p n ε δ⟩
instance concreteOptimizerKernel_markov (d p n : ℕ) (ε δ : ℝ) : IsMarkovKernel (concreteOptimizerKernel d p n ε δ) := by
  constructor
  intro S
  change IsProbabilityMeasure (concreteOptimizer d p n ε δ S : Measure (UnitBall d p))
  infer_instance
noncomputable def oneBlockLaw (d p n : ℕ) (ε δ : ℝ) (P : Measure (Example d)) : Measure (UnitBall d p) :=
  (Measure.pi (fun _ : Fin n => P)).bind (fun S => (concreteOptimizer d p n ε δ S : Measure (UnitBall d p)))
instance oneBlockLaw_probability (d p n : ℕ) (ε δ : ℝ) (P : Measure (Example d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (oneBlockLaw d p n ε δ P) :=
  isProbabilityMeasure_bind (concreteOptimizer_measurable d p n ε δ).aemeasurable (ae_of_all _ (fun S => inferInstance))
lemma unit_population_integrable (d p : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P]
    (μ : Measure (UnitBall d p)) [IsProbabilityMeasure μ] :
    Integrable (fun v : UnitBall d p => populationLoss d p P v.val) μ := by
  apply (integrable_const (radius d p+1)).mono'
    (((populationLoss_lipschitz d p P).continuous.measurable).comp measurable_subtype_coe).aestronglyMeasurable
  apply ae_of_all
  intro v
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (populationLoss_nonneg d p P v.val)]
  exact populationLoss_unit_bound d p P v.val v.property
lemma unit_empirical_integrable (d p n : ℕ) (hn : 0 < n) (S : Fin n → Example d)
    (μ : Measure (UnitBall d p)) [IsProbabilityMeasure μ] :
    Integrable (fun v : UnitBall d p => empiricalLoss d p S v.val) μ := by
  apply (integrable_const (radius d p+1)).mono'
    (((empiricalLoss_continuous d p S).measurable).comp measurable_subtype_coe).aestronglyMeasurable
  apply ae_of_all
  intro v
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (empiricalLoss_nonneg d p S v.val)]
  exact empiricalLoss_unit_bound d p n hn S v
lemma integral_oneBlock_population (d p n : ℕ) (ε δ : ℝ) (P : Measure (Example d)) [IsProbabilityMeasure P] :
    (∫ v : UnitBall d p, populationLoss d p P v.val ∂oneBlockLaw d p n ε δ P) =
      ∫ S, ∫ v : UnitBall d p, populationLoss d p P v.val
        ∂(concreteOptimizer d p n ε δ S : Measure (UnitBall d p)) ∂Measure.pi (fun _ : Fin n => P) := by
  let μ := Measure.pi (fun _ : Fin n => P)
  let κ := concreteOptimizerKernel d p n ε δ
  have hm : oneBlockLaw d p n ε δ P = (μ ⊗ₘ κ).map Prod.snd := (Measure.snd_compProd μ κ).symm
  have hf : Measurable (fun v : UnitBall d p => populationLoss d p P v.val) :=
    (populationLoss_lipschitz d p P).continuous.measurable.comp measurable_subtype_coe
  have hi : Integrable (fun q : (Fin n → Example d) × UnitBall d p => populationLoss d p P q.2.val) (μ ⊗ₘ κ) := by
    apply (integrable_const (radius d p+1)).mono' (hf.comp measurable_snd).aestronglyMeasurable
    apply ae_of_all
    intro q
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (populationLoss_nonneg d p P q.2.val)]
    exact populationLoss_unit_bound d p P q.2.val q.2.property
  rw [hm,integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,Measure.integral_compProd hi]
  rfl
lemma oneBlock_expected_excess (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (P : Measure (Example d)) [IsProbabilityMeasure P] (hP : P.map Prod.fst = gaussian d) :
    Integrable (fun v : UnitBall d p => populationLoss d p P v.val-minimumLoss d p P) (oneBlockLaw d p n ε δ P) ∧
    (∫ v : UnitBall d p, populationLoss d p P v.val-minimumLoss d p P ∂oneBlockLaw d p n ε δ P) ≤
      120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)+
        2*Real.sqrt ((featureDimension d p : ℝ)/n) := by
  let μ := Measure.pi (fun _ : Fin n => P)
  let κ := concreteOptimizerKernel d p n ε δ
  let B := 120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)
  obtain ⟨vstar,hstar⟩ := populationLoss_minimum_attained d p P
  have hdev := coefficientDeviation_bound d p n hn P hP
  have hpoint (S : Fin n → Example d) :
      (∫ v : UnitBall d p, populationLoss d p P v.val ∂(concreteOptimizer d p n ε δ S : Measure (UnitBall d p))) ≤
        coefficientDeviation d p P S+empiricalLoss d p S vstar.val+B := by
    have hp := unit_population_integrable d p P (concreteOptimizer d p n ε δ S)
    have he := unit_empirical_integrable d p n hn S (concreteOptimizer d p n ε δ S)
    have hg : Integrable (fun v : UnitBall d p => coefficientDeviation d p P S+empiricalLoss d p S v.val)
        (concreteOptimizer d p n ε δ S : Measure (UnitBall d p)) := by
      convert! (integrable_const (coefficientDeviation d p P S)).add he using 1
    have hm := integral_mono hp hg (hdev.2.2 S)
    rw [integral_add (f := fun _ : UnitBall d p => coefficientDeviation d p P S)
      (g := fun v => empiricalLoss d p S v.val) (integrable_const _) he,
      integral_const,probReal_univ,one_smul] at hm
    have hr := (concreteOptimizer_regret d p n hn ε δ hε hδ S vstar).2
    rw [integral_sub he (integrable_const _),integral_const,probReal_univ,one_smul] at hr
    change (∫ v : UnitBall d p, empiricalLoss d p S v.val ∂(concreteOptimizer d p n ε δ S : Measure (UnitBall d p)))-
      empiricalLoss d p S vstar.val ≤ B at hr
    linarith
  have hf : Measurable (fun v : UnitBall d p => populationLoss d p P v.val) :=
    (populationLoss_lipschitz d p P).continuous.measurable.comp measurable_subtype_coe
  have hleft : Integrable (fun S : Fin n → Example d => ∫ v : UnitBall d p, populationLoss d p P v.val ∂κ S) μ := by
    apply (integrable_const (radius d p+1)).mono' (hf.stronglyMeasurable.integral_kernel (κ := κ)).aestronglyMeasurable
    apply ae_of_all
    intro S
    have hbound (v : UnitBall d p) : ‖populationLoss d p P v.val‖ ≤ radius d p+1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (populationLoss_nonneg d p P v.val)]
      exact populationLoss_unit_bound d p P v.val v.property
    have h := norm_integral_le_of_norm_le_const (μ := κ S) (C := radius d p+1)
      (f := fun v : UnitBall d p => populationLoss d p P v.val) (ae_of_all _ hbound)
    simpa only [probReal_univ,mul_one] using h
  have hright : Integrable (fun S : Fin n → Example d => coefficientDeviation d p P S+empiricalLoss d p S vstar.val+B) μ := by
    convert! (hdev.1.add (empiricalLoss_iid_integrable d p n P vstar.val)).add (integrable_const B) using 1
  have hm := integral_mono hleft hright hpoint
  rw [integral_add (f := fun S => coefficientDeviation d p P S+empiricalLoss d p S vstar.val)
    (g := fun _ => B) (hdev.1.add (empiricalLoss_iid_integrable d p n P vstar.val)) (integrable_const B),
    integral_add hdev.1 (empiricalLoss_iid_integrable d p n P vstar.val),
    integral_const,probReal_univ,one_smul,empiricalLoss_iid_mean d p n hn P vstar.val,hstar] at hm
  have hi := unit_population_integrable d p P (oneBlockLaw d p n ε δ P)
  refine ⟨hi.sub (integrable_const _),?_⟩
  rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul,integral_oneBlock_population]
  have hdb : (∫ S, coefficientDeviation d p P S ∂μ) ≤ 2*Real.sqrt ((featureDimension d p : ℝ)/n) := hdev.2.1
  change (∫ S, ∫ v : UnitBall d p, populationLoss d p P v.val ∂κ S ∂μ)-minimumLoss d p P ≤ _
  linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AveragedAlgorithmLaw
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open AlgorithmInfrastructure
lemma averaged_algorithm_law (d p k M n₀ m : ℕ) (ε δ : ℝ)
    (P : Measure (Example d)) [IsProbabilityMeasure P] :
    (Measure.pi (fun _ : Fin (k*n₀+m) => P)).bind
      (fun S => algorithmLaw concreteOptimizer d p k M n₀ m ε δ S) =
    ((Measure.pi (fun _ : Fin k => oneBlockLaw d p n₀ ε δ P)).prod (Measure.pi (fun _ : Fin m => P))).bind
      (fun q => selectionLaw d p k M m ε q.1 q.2) := by
  let μ := Measure.pi (fun _ : Fin (k*n₀+m) => P)
  let μ₀ := Measure.pi (fun _ : Fin n₀ => P)
  let μB := Measure.pi (fun _ : Fin k => μ₀)
  let ν := Measure.pi (fun _ : Fin m => P)
  let κ := fun B : Fin k → Fin n₀ → Example d =>
    Measure.pi (fun j : Fin k => (concreteOptimizer d p n₀ ε δ (B j) : Measure (UnitBall d p)))
  let η := fun q : (Fin k → UnitBall d p) × (Fin m → Example d) => selectionLaw d p k M m ε q.1 q.2
  let F := fun q : (Fin k → Fin n₀ → Example d) × (Fin m → Example d) =>
    (κ q.1).bind (fun v => η (v,q.2))
  let b := fun S : Fin (k*n₀+m) → Example d => (trainingBlocks d k n₀ m S,validationBlock d k n₀ m S)
  have hκ : Measurable κ :=
    measurable_pi_measure (fun j (B : Fin k → Fin n₀ → Example d) =>
      (concreteOptimizer d p n₀ ε δ (B j) : Measure (UnitBall d p)))
      (fun j => (concreteOptimizer_measurable d p n₀ ε δ).comp (measurable_pi_apply j))
      (fun j B => inferInstance)
  have hκp (B) : IsProbabilityMeasure (κ B) := by dsimp [κ]; infer_instance
  have hη : Measurable η := measurable_selectionLaw d p k M m ε
  have hF : Measurable F := measurable_bind_param κ hκ hκp η hη
  have hb := labeled_sampleBlocks_preserving d k n₀ m P
  have htrain : μB.bind κ = Measure.pi (fun _ : Fin k => oneBlockLaw d p n₀ ε δ P) :=
    finite_pi_bind_eq (fun _ : Fin k => μ₀)
      (fun _ S => (concreteOptimizer d p n₀ ε δ S : Measure (UnitBall d p)))
      (fun _ => concreteOptimizer_measurable d p n₀ ε δ) (fun _ S => inferInstance)
  calc
    _ = μ.bind (F ∘ b) := rfl
    _ = (μ.map b).bind F := (bind_map_eq μ b hb.measurable F hF).symm
    _ = (μB.prod ν).bind F := by rw [hb.map_eq]
    _ = ((μB.bind κ).prod ν).bind η := bind_prod_swap μB ν κ hκ hκp η hη
    _ = _ := by rw [htrain]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RegressionBoosting
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma oneBlock_good_probability (d p n : ℕ) (hn : 0 < n) (ε δ η : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) (hη : 0 < η)
    (P : Measure (Example d)) [IsProbabilityMeasure P] (hP : P.map Prod.fst = gaussian d)
    (hrate : 120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)+
      2*Real.sqrt ((featureDimension d p : ℝ)/n) ≤ η) :
    (oneBlockLaw d p n ε δ P).real {v : UnitBall d p | populationLoss d p P v.val ≤ minimumLoss d p P+2*η} ≥ 1/2 := by
  let ν := oneBlockLaw d p n ε δ P
  let f := fun v : UnitBall d p => populationLoss d p P v.val-minimumLoss d p P
  have hf : Measurable f :=
    ((populationLoss_lipschitz d p P).continuous.measurable.comp measurable_subtype_coe).sub_const _
  have hex := oneBlock_expected_excess d p n hn ε δ hε hδ P hP
  have hnn : 0 ≤ᵐ[ν] f := ae_of_all _ (fun v => sub_nonneg.mpr (minimumLoss_le d p P v))
  have hm := mul_meas_ge_le_integral_of_nonneg hnn hex.1 (2*η)
  have he : (∫ v, f v ∂ν) ≤ η := hex.2.trans hrate
  have hlarge : ν.real {v | 2*η ≤ f v} ≤ 1/2 := by nlinarith
  have hbad : ν.real {v | minimumLoss d p P+2*η < populationLoss d p P v.val} ≤ 1/2 := by
    apply (measureReal_mono _).trans hlarge
    intro v hv
    change minimumLoss d p P+2*η < populationLoss d p P v.val at hv
    dsimp [f]
    linarith
  have hs : MeasurableSet {v : UnitBall d p | minimumLoss d p P+2*η < populationLoss d p P v.val} :=
    measurableSet_lt measurable_const ((populationLoss_lipschitz d p P).continuous.measurable.comp measurable_subtype_coe)
  have hcomp : {v : UnitBall d p | populationLoss d p P v.val ≤ minimumLoss d p P+2*η} =
      {v : UnitBall d p | minimumLoss d p P+2*η < populationLoss d p P v.val}ᶜ := by ext v; simp
  rw [hcomp,probReal_compl_eq_one_sub hs]
  linarith
lemma independent_boosting {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (G : Set X) (hG : MeasurableSet G)
    (hgood : ∀ i, 1/2 ≤ (μ i).real G) :
    (Measure.pi μ).real {v | ∃ i : ι, v i ∈ G} ≥ 1-(1/2 : ℝ)^(Fintype.card ι) := by
  classical
  have hbad (i) : (μ i).real Gᶜ ≤ 1/2 := by rw [probReal_compl_eq_one_sub hG]; linarith [hgood i]
  have hs : MeasurableSet (Set.univ.pi (fun _ : ι => Gᶜ)) := MeasurableSet.univ_pi (fun _ => hG.compl)
  have hfail : (Measure.pi μ).real (Set.univ.pi (fun _ : ι => Gᶜ)) = ∏ i : ι, (μ i).real Gᶜ := by
    rw [measureReal_def,Measure.pi_pi]
    simp only [ENNReal.toReal_prod,measureReal_def]
  have hb : (Measure.pi μ).real (Set.univ.pi (fun _ : ι => Gᶜ)) ≤ (1/2 : ℝ)^Fintype.card ι := by
    rw [hfail]
    calc
      _ ≤ ∏ _i : ι, (1/2 : ℝ) := prod_le_prod (fun i _ => measureReal_nonneg) (fun i _ => hbad i)
      _ = _ := by simp
  have he : {v | ∃ i : ι, v i ∈ G} = (Set.univ.pi (fun _ : ι => Gᶜ))ᶜ := by
    ext v
    simp
  rw [he,probReal_compl_eq_one_sub hs]
  linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ClassifierMeasurability
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
lemma decode_measurable_joint (d p M : ℕ) :
    Measurable (fun q : Output d p M × Vec d => decode d p M q.1 q.2) := by
  have hv : Measurable (fun q : Output d p M × Vec d => q.1.1.val) :=
    measurable_subtype_coe.comp measurable_fst.fst
  have hs : Measurable (fun q : Output d p M × Vec d => score d p q.1.1.val q.2) := by
    convert! (score_measurable_joint d p).comp (hv.prodMk measurable_snd) using 1
  have ht : Measurable (fun q : Output d p M × Vec d => gridThreshold M q.1.2) :=
    (measurable_of_countable (gridThreshold M)).comp measurable_fst.snd
  convert! sign_measurable_grid.comp (hs.sub ht) using 1
lemma error_parametric_measurable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (h : Z × X → Bool) (hh : Measurable h) :
    Measurable (fun z => error P (fun x => h (z,x))) := by
  have hm : Measurable (fun q : Z × (X × Bool) => if h (q.1,q.2.1) ≠ q.2.2 then (1 : ℝ) else 0) := by
    have hs : MeasurableSet {q : Z × (X × Bool) | h (q.1,q.2.1) ≠ q.2.2} :=
      (measurableSet_eq_fun (hh.comp (measurable_fst.prodMk measurable_snd.fst)) measurable_snd.snd).compl
    exact measurable_const.ite hs measurable_const
  have hi : Measurable (fun z : Z => ∫ x, if h (z,x.1) ≠ x.2 then (1 : ℝ) else 0 ∂P) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  convert! hi using 1
  funext z
  symm
  have hz : Measurable (fun x : X => h (z,x)) := by
    convert! hh.comp (measurable_const.prodMk measurable_id) using 1
  exact classification_error_integral P (fun x : X => h (z,x)) hz
lemma decode_error_measurable (d p M : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P] :
    Measurable (fun o : Output d p M => error P (decode d p M o)) :=
  error_parametric_measurable P (fun q => decode d p M q.1 q.2) (decode_measurable_joint d p M)
lemma exists_candidate_error_le_loss (d p M : ℕ) (hM : 0 < M)
    (P : Measure (Example d)) [IsProbabilityMeasure P] (v : Coeff d p) :
    ∃ l : Fin M, error P (candidate d p M v l) ≤ populationLoss d p P v/2+1/(2*M) := by
  classical
  have hne : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0,hM⟩,mem_univ _⟩
  obtain ⟨l,hl,hmin⟩ := Finset.exists_min_image univ (fun l : Fin M => error P (candidate d p M v l)) hne
  refine ⟨l,?_⟩
  have hs : (∑ _i : Fin M, error P (candidate d p M v l)) ≤
      ∑ i : Fin M, error P (candidate d p M v i) := sum_le_sum (fun i hi => hmin i hi)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hav : error P (candidate d p M v l) ≤ (∑ i : Fin M, error P (candidate d p M v i))/(M : ℝ) := by
    apply (le_div_iff₀ hMr).mpr
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hs
  have hscore : Measurable (score d p v) := by
    convert! (score_measurable_joint d p).comp (measurable_const.prodMk measurable_id) using 1
  exact hav.trans (midpoint_grid_population_average P (score d p v) hscore M hM (loss_integrable d p P v))
end PrivateAgnosticHalfspace.Gaussian

end

section
-- Solutions.ValidationSchedule
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def validationSlack (k M m : ℕ) (ε η : ℝ) : ℝ :=
  2*Real.sqrt (Real.log (4*(k : ℝ)*M/η)/(2*m))+2*Real.log (2*(k : ℝ)*M/η)/(ε*m)
lemma repetition_failure_bound (β : ℝ) (hβ : 0 < β ∧ β ≤ 1/2) :
    (1/2 : ℝ)^(repetitions β) ≤ β/2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : Real.log (2/β) ≤ (repetitions β : ℝ)*Real.log 2 :=
    (div_le_iff₀ hl).mp (Nat.le_ceil (Real.log (2/β)/Real.log 2))
  have he := Real.exp_le_exp.mpr (neg_le_neg hk)
  have hleft : Real.exp (-((repetitions β : ℝ)*Real.log 2)) = (1/2 : ℝ)^(repetitions β) := by
    rw [show -((repetitions β : ℝ)*Real.log 2) = (repetitions β : ℝ)*(-Real.log 2) by ring,
      Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hright : Real.exp (-Real.log (2/β)) = β/2 := by
    rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) hβ.1)]
    field_simp
  rw [hleft,hright] at he
  exact he
lemma validation_schedule_slack (C c α β ε : ℝ) (k M : ℕ)
    (hc : 0 < c) (hC32 : 32/c^2 ≤ C) (hC12 : 12/c ≤ C)
    (hα : 0 < α) (hβ : 0 < β ∧ β ≤ 1/2) (hε : 0 < ε) (hk : 0 < k) (hM : 0 < M) :
    validationSlack k M (validationSize C α β ε k M) ε (β/2) ≤ c*α := by
  let x := (k : ℝ)*M/β
  let q := Real.log x
  let m := validationSize C α β ε k M
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hKM : (1 : ℝ) ≤ (k : ℝ)*M := by nlinarith
  have hx : 2 ≤ x := by dsimp [x]; apply (le_div_iff₀ hβ.1).mpr; nlinarith [hβ.2]
  have hxp : 0 < x := by linarith
  have hq2 : Real.log 2 ≤ q := Real.log_le_log (by norm_num) hx
  have hq : 0 < q := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hq2
  have h8 : Real.log (8*x) ≤ 4*q := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hxp.ne',
      show (8 : ℝ) = 2^3 by norm_num,Real.log_pow]
    norm_num
    linarith
  have h4 : Real.log (4*x) ≤ 3*q := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hxp.ne',
      show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
    linarith
  have hCp : 0 < C := lt_of_lt_of_le (div_pos (by norm_num) (sq_pos_of_pos hc)) hC32
  have hinv : 0 < (ε*α)⁻¹ := inv_pos.mpr (mul_pos hε hα)
  have hceil : C*(α⁻¹^2+(ε*α)⁻¹)*q ≤ (m : ℝ) := Nat.le_ceil _
  have hm : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hceil
  have ht1 : C*α⁻¹^2*q ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCp.le hinv.le] : C*α⁻¹^2 ≤ C*(α⁻¹^2+(ε*α)⁻¹)) hq.le).trans hceil
  have ht2 : C*(ε*α)⁻¹*q ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCp.le (sq_nonneg α⁻¹)] : C*(ε*α)⁻¹ ≤ C*(α⁻¹^2+(ε*α)⁻¹)) hq.le).trans hceil
  have hmα : C*q ≤ α^2*(m : ℝ) := by
    calc
      _ = α^2*(C*α⁻¹^2*q) := by field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht1 (sq_nonneg α)
  have hmεα : C*q ≤ ε*α*(m : ℝ) := by
    calc
      _ = (ε*α)*(C*(ε*α)⁻¹*q) := by field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht2 (mul_pos hε hα).le
  have h32 : 32 ≤ c^2*C := by have h := (div_le_iff₀ (sq_pos_of_pos hc)).mp hC32; nlinarith only [h]
  have h12 : 12 ≤ c*C := by have h := (div_le_iff₀ hc).mp hC12; nlinarith only [h]
  have hms : 32*q ≤ c^2*α^2*(m : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right h32 hq.le
    have h2 := mul_le_mul_of_nonneg_left hmα (sq_nonneg c)
    nlinarith only [h1,h2]
  have hme : 12*q ≤ c*ε*α*(m : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right h12 hq.le
    have h2 := mul_le_mul_of_nonneg_left hmεα hc.le
    nlinarith only [h1,h2]
  have hsq : Real.log (8*x)/(2*(m : ℝ)) ≤ (c*α/4)^2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*m)).mpr
    nlinarith only [h8,hms]
  have hsqrt : Real.sqrt (Real.log (8*x)/(2*(m : ℝ))) ≤ c*α/4 :=
    (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))
  have hlinear : 2*Real.log (4*x)/(ε*(m : ℝ)) ≤ c*α/2 := by
    apply (div_le_iff₀ (mul_pos hε hm)).mpr
    nlinarith only [h4,hme]
  have he8 : 4*(k : ℝ)*M/(β/2) = 8*x := by dsimp [x]; field_simp <;> ring
  have he4 : 2*(k : ℝ)*M/(β/2) = 4*x := by dsimp [x]; field_simp <;> ring
  unfold validationSlack
  rw [he8,he4]
  change 2*Real.sqrt (Real.log (8*x)/(2*(m : ℝ)))+2*Real.log (4*x)/(ε*(m : ℝ)) ≤ c*α
  linarith only [hsqrt,hlinear]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ValidationAccuracy
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open AlgorithmInfrastructure
lemma selection_validation_accuracy (d p k M m : ℕ) (hk : 0 < k) (hM : 0 < M) (hm : 0 < m)
    (P : Measure (Example d)) [IsProbabilityMeasure P] (v : Fin k → UnitBall d p)
    (ε η b : ℝ) (hε : 0 < ε) (hη : 0 < η ∧ η < 1)
    (j₀ : Fin k) (l₀ : Fin M) (hb : error P (candidate d p M (v j₀).val l₀) ≤ b) :
    ((Measure.pi (fun _ : Fin m => P)).bind (fun V => selectionLaw d p k M m ε v V)).real
      {o | error P (decode d p M o) ≤ b+validationSlack k M m ε η} ≥ 1-η := by
  let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  let h := fun i : Fin (k*M) => candidate d p M (v (e i).1).val (e i).2
  have hh (i) : Measurable (h i) := measurable_candidate d p M _ _
  have hK := Nat.mul_pos hk hM
  let hne : (univ : Finset (Fin (k*M))).Nonempty := ⟨⟨0,hK⟩,mem_univ _⟩
  let a := univ.inf' hne (fun i => error P (h i))
  obtain ⟨A,hAlaw,hAmeas,hApriv,hrest⟩ := lemma_B_5 (k*M) m hK hm P h hh ε η hε hη
  let ν := (Measure.pi (fun _ : Fin m => P)).bind (fun V => (A V : Measure (Fin (k*M))))
  have hν : IsProbabilityMeasure ν := hrest.1
  letI := hν
  have hs : 2*Real.sqrt (Real.log (4*((k*M : ℕ) : ℝ)/η)/(2*m))+
      2*Real.log (2*((k*M : ℕ) : ℝ)/η)/(ε*m) = validationSlack k M m ε η := by
    simp only [validationSlack,Nat.cast_mul,mul_assoc]
  have hgood : ν.real {i | error P (h i) ≤ a+validationSlack k M m ε η} ≥ 1-η := by
    simpa only [add_assoc,hs] using hrest.2
  have hab : a ≤ b := by
    have hl : a ≤ error P (h (e.symm (j₀,l₀))) := inf'_le _ (mem_univ _)
    have he : h (e.symm (j₀,l₀)) = candidate d p M (v j₀).val l₀ := by simp [h]
    rw [he] at hl
    exact hl.trans hb
  let out := fun i : Fin (k*M) => (v (e i).1,(e i).2)
  have hout : Measurable out := measurable_of_countable _
  have hlaw : ((Measure.pi (fun _ : Fin m => P)).bind (fun V => selectionLaw d p k M m ε v V)) = ν.map out := by
    rw [map_bind_eq _ _ hAmeas out hout]
    congr 1
    funext V
    rw [hAlaw V,selectionLaw_reindex]
  have hG : MeasurableSet {o : Output d p M | error P (decode d p M o) ≤ b+validationSlack k M m ε η} :=
    measurableSet_le (decode_error_measurable d p M P) measurable_const
  rw [hlaw,map_measureReal_apply hout hG]
  have hsub : {i : Fin (k*M) | error P (h i) ≤ a+validationSlack k M m ε η} ⊆
      out ⁻¹' {o | error P (decode d p M o) ≤ b+validationSlack k M m ε η} := by
    intro i hi
    change error P (h i) ≤ b+validationSlack k M m ε η
    change error P (h i) ≤ a+validationSlack k M m ε η at hi
    linarith
  exact hgood.trans (measureReal_mono hsub)
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ProbabilityBind
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma probability_bind_real_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) (hκ : Measurable κ) (hprob : ∀ x, IsProbabilityMeasure (κ x))
    (A : Set Y) (hA : MeasurableSet A) :
    (μ.bind κ).real A = ∫ x, (κ x).real A ∂μ := by
  letI (x : X) := hprob x
  rw [measureReal_def,Measure.bind_apply hA hκ.aemeasurable]
  symm
  exact integral_toReal ((Measure.measurable_coe hA).comp hκ).aemeasurable (ae_of_all _ (fun x => measure_lt_top _ _))
lemma probability_bind_real_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : X → Measure Y) (hκ : Measurable κ) (A : Set Y) (hA : MeasurableSet A) :
    Measurable (fun x => (κ x).real A) := ((Measure.measurable_coe hA).comp hκ).ennreal_toReal
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.TwoStageSuccess
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma two_stage_success {X W Z : Type*} [MeasurableSpace X] [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure W) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (η : X × W → Measure Z) (hη : Measurable η) (hprob : ∀ q, IsProbabilityMeasure (η q))
    (G : Set X) (hG : MeasurableSet G) (A : Set Z) (hA : MeasurableSet A)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b ∧ b ≤ 1)
    (htrain : 1-a ≤ μ.real G)
    (hval : ∀ x ∈ G, 1-b ≤ (ν.bind (fun w => η (x,w))).real A) :
    ((μ.prod ν).bind η).real A ≥ 1-a-b := by
  let κ := fun x : X => ν.bind (fun w => η (x,w))
  have hκ : Measurable κ := measurable_parameter_bind ν η hη
  have hκp (x : X) : IsProbabilityMeasure (κ x) :=
    isProbabilityMeasure_bind (hη.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (ae_of_all _ (fun w => hprob (x,w)))
  let g := fun x : X => (κ x).real A
  have hg : Measurable g := probability_bind_real_measurable κ hκ A hA
  have hgi : Integrable g μ := by
    apply (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    apply ae_of_all
    intro x
    letI := hκp x
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hI := (integrable_const (μ := μ) (1-b)).indicator hG
  have hpoint (x : X) : G.indicator (fun _ => 1-b) x ≤ g x := by
    by_cases hx : x ∈ G
    · rw [indicator_of_mem hx]
      exact hval x hx
    · rw [indicator_of_notMem hx]
      exact measureReal_nonneg
  have hm := integral_mono hI hgi hpoint
  rw [integral_indicator hG,integral_const] at hm
  simp only [smul_eq_mul,measureReal_restrict_apply_univ] at hm
  have hmul := mul_le_mul_of_nonneg_right htrain (by linarith : 0 ≤ 1-b)
  rw [prod_bind_eq μ ν η hη,probability_bind_real_apply μ κ hκ hκp A hA]
  change 1-a-b ≤ ∫ x, g x ∂μ
  nlinarith [mul_nonneg ha hb.1]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AlgorithmAccuracy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open AlgorithmInfrastructure
lemma algorithm_accuracy_from_bounds (d p k M n₀ m : ℕ)
    (hk : 0 < k) (hM : 0 < M) (hn : 0 < n₀) (hm : 0 < m)
    (α β ε δ η : ℝ) (hβ : 0 < β ∧ β ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1/2)
    (hδ : 0 < δ ∧ δ ≤ 1/2) (hη : 0 < η)
    (P : Measure (Example d)) [IsProbabilityMeasure P] (hP : P.map Prod.fst = gaussian d)
    (hopt : minimumLoss d p P ≤ 2*opt d P+2*η)
    (hrate : 120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n₀ : ℝ)*ε)+
      2*Real.sqrt ((featureDimension d p : ℝ)/n₀) ≤ η)
    (hgrid : 1/(2*(M : ℝ)) ≤ η) (hval : validationSlack k M m ε (β/2) ≤ η)
    (hboost : (1/2 : ℝ)^k ≤ β/2) (hfinal : 4*η ≤ α) :
    let ν := (Measure.pi (fun _ : Fin (k*n₀+m) => P)).bind
      (fun S => algorithmLaw concreteOptimizer d p k M n₀ m ε δ S)
    IsProbabilityMeasure ν ∧ ν.real {o | error P (decode d p M o) ≤ opt d P+α} ≥ 1-β := by
  let ν := (Measure.pi (fun _ : Fin (k*n₀+m) => P)).bind
    (fun S => algorithmLaw concreteOptimizer d p k M n₀ m ε δ S)
  have hν : IsProbabilityMeasure ν := isProbabilityMeasure_bind
    (measurable_algorithmLaw concreteOptimizer d p k M n₀ m ε δ (concreteOptimizer_measurable d p n₀ ε δ)).aemeasurable
    (ae_of_all _ (fun S => algorithmLaw_probability concreteOptimizer d p k M n₀ m hk hM ε δ S))
  refine ⟨hν,?_⟩
  let μ := Measure.pi (fun _ : Fin k => oneBlockLaw d p n₀ ε δ P)
  let V := Measure.pi (fun _ : Fin m => P)
  let G := {v : Fin k → UnitBall d p | ∃ j : Fin k, populationLoss d p P (v j).val ≤ minimumLoss d p P+2*η}
  let A := {o : Output d p M | error P (decode d p M o) ≤ opt d P+α}
  let sel := fun q : (Fin k → UnitBall d p) × (Fin m → Example d) => selectionLaw d p k M m ε q.1 q.2
  have hsingle : MeasurableSet {v : UnitBall d p | populationLoss d p P v.val ≤ minimumLoss d p P+2*η} :=
    measurableSet_le ((populationLoss_lipschitz d p P).continuous.measurable.comp measurable_subtype_coe) measurable_const
  have hG : MeasurableSet G := by
    simp only [G,setOf_exists]
    exact MeasurableSet.iUnion (fun j => hsingle.preimage (measurable_pi_apply j))
  have hA : MeasurableSet A := measurableSet_le (decode_error_measurable d p M P) measurable_const
  have htrain : 1-β/2 ≤ μ.real G := by
    have h := independent_boosting (fun _ : Fin k => oneBlockLaw d p n₀ ε δ P) _ hsingle
      (fun _ => oneBlock_good_probability d p n₀ hn ε δ η hε hδ hη P hP hrate)
    simp only [Fintype.card_fin] at h
    change 1-(1/2 : ℝ)^k ≤ μ.real G at h
    change 1-β/2 ≤ μ.real G
    linarith
  have hsel : Measurable sel := measurable_selectionLaw d p k M m ε
  have hselp (q) : IsProbabilityMeasure (sel q) := selectionLaw_probability d p k M m hk hM ε q.1 q.2
  have hconditional (v : Fin k → UnitBall d p) (hv : v ∈ G) :
      1-β/2 ≤ (V.bind (fun W => sel (v,W))).real A := by
    obtain ⟨j,hj⟩ := hv
    obtain ⟨l,hl⟩ := exists_candidate_error_le_loss d p M hM P (v j).val
    have hbest : error P (candidate d p M (v j).val l) ≤ opt d P+3*η := by linarith
    have h := selection_validation_accuracy d p k M m hk hM hm P v ε (β/2) (opt d P+3*η)
      hε.1 ⟨by linarith [hβ.1],by linarith [hβ.2]⟩ j l hbest
    have hcp : IsProbabilityMeasure (V.bind (fun W => sel (v,W))) :=
      isProbabilityMeasure_bind (hsel.comp (measurable_const.prodMk measurable_id)).aemeasurable
        (ae_of_all _ (fun W => hselp (v,W)))
    letI := hcp
    have hsub : {o : Output d p M | error P (decode d p M o) ≤ opt d P+3*η+validationSlack k M m ε (β/2)} ⊆ A := by
      intro o ho
      change error P (decode d p M o) ≤ opt d P+α
      change error P (decode d p M o) ≤ opt d P+3*η+validationSlack k M m ε (β/2) at ho
      linarith
    exact h.trans (measureReal_mono hsub)
  have htwo := two_stage_success μ V sel hsel hselp G hG A hA (β/2) (β/2)
    (by linarith [hβ.1]) ⟨by linarith [hβ.1],by linarith [hβ.2]⟩ htrain hconditional
  rw [averaged_algorithm_law]
  change 1-β ≤ ((μ.prod V).bind sel).real A
  linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ScheduleStatistics
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
lemma scheduled_degree_positive (C α : ℝ) (hC : 0 < C) (hα : 0 < α) : 1 ≤ scheduledDegree C α := by
  exact Nat.ceil_pos.mpr (div_pos hC (sq_pos_of_pos hα))
lemma scheduled_degree_approximation (C C₀ c α : ℝ) (hc : 0 < c) (hα : 0 < α)
    (hC : C₀/c^2 ≤ C) : C₀/(c*α)^2 ≤ (scheduledDegree C α : ℝ) := by
  have h := div_le_div_of_nonneg_right hC (sq_nonneg α)
  have he : (C₀/c^2)/α^2 = C₀/(c*α)^2 := by ring
  rw [he] at h
  exact h.trans (Nat.le_ceil _)
lemma scheduled_feature_tail_dimension (C c Cdim α : ℝ) (d : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hα : 0 < α ∧ α ≤ 1/2)
    (hCdim : 2*(C+1)^2/c ≤ Cdim) (hd : Cdim/α^5 ≤ (d : ℝ)) :
    2*(scheduledDegree C α : ℝ)^2/(c*α) ≤ (d : ℝ) := by
  let p := scheduledDegree C α
  have hα2 : α^2 ≤ 1 := by nlinarith [hα.1,hα.2]
  have hpceil : (p : ℝ) ≤ C/α^2+1 := (Nat.ceil_lt_add_one (div_nonneg hC (sq_nonneg α))).le
  have hpα : (p : ℝ)*α^2 ≤ C+1 := by
    have h := mul_le_mul_of_nonneg_right hpceil (sq_nonneg α)
    have he : (C/α^2+1)*α^2 = C+α^2 := by field_simp [hα.1.ne'] <;> ring
    rw [he] at h
    linarith
  have hpsq := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg p) (sq_nonneg α)) hpα 2
  have hd1 := (div_le_iff₀ (pow_pos hα.1 5)).mp hd
  have hd2 := (div_le_iff₀ hc).mp hCdim
  have hd3 := mul_le_mul_of_nonneg_right hd1 hc.le
  have hfinal : 2*(p : ℝ)^2*α^4 ≤ ((d : ℝ)*c*α)*α^4 := by nlinarith only [hpsq,hd2,hd3]
  have hcancel := mul_le_mul_of_nonneg_right hfinal (inv_nonneg.mpr (pow_nonneg hα.1.le 4))
  simp only [mul_assoc,mul_inv_cancel₀ (pow_ne_zero 4 hα.1.ne'),mul_one] at hcancel
  apply (div_le_iff₀ (mul_pos hc hα.1)).mpr
  nlinarith only [hcancel]
lemma scheduled_grid_error (C c α : ℝ) (hc : 0 < c) (hα : 0 < α) (hC : 1/(2*c) ≤ C) :
    1/(2*(thresholds C α : ℝ)) ≤ c*α := by
  have hCp : 0 < C := lt_of_lt_of_le (div_pos (by norm_num) (by positivity)) hC
  have hM : 0 < thresholds C α := Nat.ceil_pos.mpr (div_pos hCp hα)
  have hMr : (0 : ℝ) < thresholds C α := by exact_mod_cast hM
  have hm := (div_le_iff₀ hα).mp (Nat.le_ceil (C/α))
  have hcc := (div_le_iff₀ (by positivity : (0 : ℝ) < 2*c)).mp hC
  have hh := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2*c)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(thresholds C α : ℝ))).mpr
  change 1 ≤ c*α*(2*(⌈C/α⌉₊ : ℝ))
  nlinarith only [hcc,hh]
lemma blockCondition_regression_rate (C c α ε δ : ℝ) (d p n : ℕ)
    (hC : 120 ≤ C) (hε : 0 < ε) (hb : blockCondition C c α ε δ d p n) :
    120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)+
      2*Real.sqrt ((featureDimension d p : ℝ)/n) ≤ c*α := by
  let Q := radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/(ε*n)
  let R := Real.sqrt ((featureDimension d p : ℝ)/n)
  have hQ : 0 ≤ Q := by dsimp [Q]; unfold radius; positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hrate : 120*Q+2*R ≤ C*(Q+R) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) hQ,
      mul_nonneg (show 0 ≤ C-2 by linarith) hR]
  have he : 120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)+
      2*Real.sqrt ((featureDimension d p : ℝ)/n) = 120*Q+2*R := by dsimp [Q,R]; ring
  rw [he]
  exact hrate.trans hb.2
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ScheduledAccuracyOperational
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
lemma scheduled_accuracy_operational_constants :
    ∃ (C c Cdim : ℝ), 1 ≤ C ∧ 0 < c ∧ c ≤ 1/4 ∧ 0 < Cdim ∧
      2*(C+1)^2/c ≤ Cdim ∧ 131072 ≤ C ∧ c ≤ 1/64 ∧
      ∀ (α β ε δ : ℝ), 0 < α ∧ α ≤ 1/2 → 0 < β ∧ β ≤ 1/2 →
        0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
      ∀ (d : ℕ), Cdim/α^5 ≤ (d : ℝ) →
      let p := scheduledDegree C α
      let k := repetitions β
      let M := thresholds C α
      let n₀ := trainingSize C c α ε δ d p
      let m := validationSize C α β ε k M
      blockCondition C c α ε δ d p n₀ ∧
      (∀ r, blockCondition C c α ε δ d p r → n₀ ≤ r) ∧
      0 < k ∧ 0 < M ∧ 0 < m ∧ 1 ≤ d ∧ 1 ≤ p ∧
      ∀ P : Measure (Example d), IsProbabilityMeasure P → P.map Prod.fst = gaussian d →
      let ν := (Measure.pi (fun _ : Fin (k*n₀+m) => P)).bind
        (fun S => algorithmLaw concreteOptimizer d p k M n₀ m ε δ S)
      IsProbabilityMeasure ν ∧ ν.real {o | error P (decode d p M o) ≤ opt d P+α} ≥ 1-β := by
  obtain ⟨C₀,hC₀,happrox⟩ := halfspace_approximation_fixed_degree
  let c : ℝ := 1/64
  let C : ℝ := max 131072 (C₀/c^2)
  let Cdim : ℝ := 2*(C+1)^2/c
  have hc : 0 < c := by norm_num [c]
  have hC120 : 120 ≤ C := (by norm_num : (120 : ℝ) ≤ 131072).trans (le_max_left _ _)
  have hC1 : 1 ≤ C := by linarith
  have hCp : 0 < C := by linarith
  have hCapp : C₀/c^2 ≤ C := le_max_right _ _
  have hC32 : 32/c^2 ≤ C := by change (32 : ℝ)/(1/64)^2 ≤ max 131072 (C₀/c^2); norm_num <;> exact le_max_left _ _
  have hC12 : 12/c ≤ C := by change (12 : ℝ)/(1/64) ≤ C; norm_num; linarith
  have hCgrid : 1/(2*c) ≤ C := by change (1 : ℝ)/(2*(1/64)) ≤ C; norm_num; linarith
  have hCdim : 0 < Cdim := by dsimp [Cdim]; positivity
  refine ⟨C,c,Cdim,hC1,hc,by norm_num [c],hCdim,le_rfl,le_max_left _ _,by norm_num [c],?_⟩
  intro α β ε δ hα hβ hε hδ d hd
  dsimp only
  let p := scheduledDegree C α
  let k := repetitions β
  let M := thresholds C α
  let n₀ := trainingSize C c α ε δ d p
  let m := validationSize C α β ε k M
  have hs := training_schedule C c α ε δ d p hCp hc hα.1 hε.1 (log_recip_nonneg δ hδ)
  have hpos := positive_schedule C α β ε hCp hα.1 hβ hε.1
  have hdp : 1 ≤ d := by
    have hα5 : α^5 ≤ 1 := pow_le_one₀ hα.1.le (by linarith)
    have hdim1 : 1 ≤ Cdim := by dsimp [Cdim,c]; nlinarith [sq_nonneg C]
    have hh := (div_le_iff₀ (pow_pos hα.1 5)).mp hd
    have hd0 : 0 < (d : ℝ) := by nlinarith [mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hα5)]
    exact_mod_cast hd0
  have hpp : 1 ≤ p := scheduled_degree_positive C α hCp hα.1
  refine ⟨hs.1,hs.2.1,hpos.1,hpos.2.1,hpos.2.2,hdp,hpp,?_⟩
  intro P hprob hP
  letI := hprob
  have hη : 0 < c*α := mul_pos hc hα.1
  have hη1 : c*α < 1 := by dsimp [c]; linarith [hα.2]
  have htaildim := scheduled_feature_tail_dimension C c Cdim α d hc hCp.le hα le_rfl hd
  have htail : (gaussian d).real {x | radius d p < ‖features d p x‖} ≤ c*α :=
    lemma_C_2 d p hdp hpp (c*α) ⟨hη,hη1⟩ htaildim
  have happ := happrox d hdp (c*α) ⟨hη,hη1⟩ p
    (scheduled_degree_approximation C C₀ c α hc hα.1 hCapp)
  have hopt := minimumLoss_halfspace_bound d p P hP (c*α) htail happ
  exact algorithm_accuracy_from_bounds d p k M n₀ m hpos.1 hpos.2.1 (by have := hs.1.1; omega)
    hpos.2.2 α β ε δ (c*α) hβ hε hδ hη P hP hopt
    (blockCondition_regression_rate C c α ε δ d p n₀ hC120 hε.1 hs.1)
    (scheduled_grid_error C c α hc hα.1 hCgrid)
    (validation_schedule_slack C c α β ε k M hc hC32 hC12 hα.1 hβ hε.1 hpos.1 hpos.2.1)
    (repetition_failure_bound β hβ) (by dsimp [c]; linarith [hα.1])
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.OperationalScheduleBounds
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
lemma repetition_log_bound (β : ℝ) (hβ : 0 < β ∧ β ≤ 1/2) (M : ℕ) (hM : 0 < M) :
    Real.log ((repetitions β : ℝ)*M/β) ≤ 3*(repetitions β : ℝ)*M := by
  let k := repetitions β
  have hk : 0 < k := (positive_schedule 1 1 β 1 (by norm_num) (by norm_num) hβ (by norm_num)).1
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hceil := (div_le_iff₀ hl2).mp (Nat.le_ceil (Real.log (2/β)/Real.log 2))
  have hlogβ : -Real.log β ≤ k := by
    change Real.log (2/β) ≤ (k : ℝ)*Real.log 2 at hceil
    rw [Real.log_div (by norm_num) hβ.1.ne'] at hceil
    have hmul := mul_le_mul_of_nonneg_left hl21 (Nat.cast_nonneg k : (0 : ℝ) ≤ _)
    linarith
  have hlk := Real.log_le_sub_one_of_pos hkr
  have hlM := Real.log_le_sub_one_of_pos hMr
  rw [Real.log_div (mul_pos hkr hMr).ne' hβ.1.ne',Real.log_mul hkr.ne' hMr.ne']
  have hprod1 := mul_le_mul_of_nonneg_left hM1 hkr.le
  have hprod2 := mul_le_mul_of_nonneg_right hk1 hMr.le
  change Real.log (k : ℝ)+Real.log (M : ℝ)-Real.log β ≤ 3*(k : ℝ)*M
  nlinarith only [hlogβ,hlk,hlM,hprod1,hprod2]
lemma block_statistical_lower (C c α ε δ : ℝ) (d p n : ℕ)
    (hC : 0 < C) (hc : 0 < c) (hα : 0 < α) (hε : 0 < ε)
    (hb : blockCondition C c α ε δ d p n) :
    C^2*(featureDimension d p : ℝ) ≤ c^2*α^2*n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hb.1; omega : 0 < n)
  have hQ : 0 ≤ radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/(ε*n) := by unfold radius; positivity
  let R := Real.sqrt ((featureDimension d p : ℝ)/n)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hh : C*R ≤ c*α := by have := hb.2; nlinarith [mul_nonneg hC.le hQ]
  have hs : (C*R)^2 ≤ (c*α)^2 := pow_le_pow_left₀ (mul_nonneg hC.le hR) hh 2
  have he : R^2=(featureDimension d p : ℝ)/n := Real.sq_sqrt (by positivity)
  have hquot : C^2*((featureDimension d p : ℝ)/n) ≤ c^2*α^2 := by nlinarith only [hs,he]
  have hmul := mul_le_mul_of_nonneg_right hquot hn.le
  have hcancel : C^2*((featureDimension d p : ℝ)/n)*(n : ℝ)=C^2*featureDimension d p := by field_simp
  rw [hcancel] at hmul
  exact hmul
lemma block_private_lower (C c α ε δ : ℝ) (d p n : ℕ)
    (hC : 0 < C) (hε : 0 < ε) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (hb : blockCondition C c α ε δ d p n) :
    C*(featureDimension d p : ℝ) ≤ c*ε*α*n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hb.1; omega : 0 < n)
  have hR : 0 ≤ Real.sqrt ((featureDimension d p : ℝ)/n) := Real.sqrt_nonneg _
  have hh : C*(radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/(ε*n)) ≤ c*α := by
    have := hb.2
    nlinarith [mul_nonneg hC.le hR]
  rw [radius_sqrt_mul d p _ (log_recip_nonneg δ hδ)] at hh
  have hmul := (div_le_iff₀ (mul_pos hε hn)).mp (show C*(2*featureDimension d p*Real.sqrt (Real.log (1/δ)))/(ε*n) ≤ c*α by convert hh using 1 <;> ring)
  have hroot : 1/2 ≤ Real.sqrt (Real.log (1/δ)) := by
    nlinarith [privacyLog_lower δ hδ,Real.sq_sqrt (log_recip_nonneg δ hδ),Real.sqrt_nonneg (Real.log (1/δ))]
  have hr := mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 2*C*featureDimension d p by positivity)
  nlinarith only [hmul,hr]
end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
lemma validation_le_training_blocks (C c α β ε δ : ℝ) (d p n M : ℕ)
    (hC : 1 ≤ C) (hc : 0 < c ∧ c ≤ 1/64) (hα : 0 < α)
    (hβ : 0 < β ∧ β ≤ 1/2) (hε : 0 < ε) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (hM : 0 < M) (hMD : M ≤ featureDimension d p)
    (hb : blockCondition C c α ε δ d p n) :
    validationSize C α β ε (repetitions β) M ≤ repetitions β*n := by
  let k := repetitions β
  let D := featureDimension d p
  have hCp : 0 < C := by linarith
  have hαsq : 0 < α^2 := sq_pos_of_pos hα
  have hcsq : 0 < c^2 := sq_pos_of_pos hc.1
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hb.1
  have hk : 0 < k := (positive_schedule C α β ε hCp hα hβ hε).1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsmall : 12*c^2 ≤ C := by nlinarith [hc.1,hc.2]
  have hs := block_statistical_lower C c α ε δ d p n hCp hc.1 hα hε hb
  have hprod := mul_le_mul_of_nonneg_right hsmall (show (0 : ℝ) ≤ C*D by positivity)
  have hscaled : c^2*(12*C*D) ≤ c^2*(α^2*n) := by nlinarith only [hprod,hs]
  have hstat : 12*C*D ≤ α^2*n := (mul_le_mul_iff_right₀ hcsq).mp hscaled
  have hp := block_private_lower C c α ε δ d p n hCp hε hδ hb
  have hpriv : 12*C*D ≤ ε*α*n := by
    have hcc : 12*c ≤ 1 := by linarith [hc.2]
    have hh := mul_le_mul_of_nonneg_right hcc (show (0 : ℝ) ≤ ε*α*n by positivity)
    nlinarith only [hp,hh]
  have hstatpart : 3*C*D/α^2 ≤ (n : ℝ)/4 := by
    apply (div_le_iff₀ hαsq).mpr
    nlinarith only [hstat]
  have hprivpart : 3*C*D/(ε*α) ≤ (n : ℝ)/4 := by
    apply (div_le_iff₀ (mul_pos hε hα)).mpr
    nlinarith only [hpriv]
  have htotal : 1+3*C*D*(α⁻¹^2+(ε*α)⁻¹) ≤ (n : ℝ) := by
    have he : 3*C*D*(α⁻¹^2+(ε*α)⁻¹)=3*C*D/α^2+3*C*D/(ε*α) := by ring
    rw [he]
    linarith only [hstatpart,hprivpart,hn]
  let q := C*(α⁻¹^2+(ε*α)⁻¹)*Real.log ((k : ℝ)*M/β)
  have hq : 0 ≤ q := by
    dsimp [q]
    have hx : 1 ≤ (k : ℝ)*M/β := by
      apply (le_div_iff₀ hβ.1).mpr
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith [mul_le_mul hk1 hM1 (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg k)]
    exact mul_nonneg (by positivity) (Real.log_nonneg hx)
  have hceil : (validationSize C α β ε k M : ℝ) ≤ q+1 := (Nat.ceil_lt_add_one hq).le
  have hlog := repetition_log_bound β hβ M hM
  have hmD : (M : ℝ) ≤ D := by exact_mod_cast hMD
  have hqbound : q ≤ (k : ℝ)*(3*C*D*(α⁻¹^2+(ε*α)⁻¹)) := by
    dsimp [q]
    calc
      _ ≤ C*(α⁻¹^2+(ε*α)⁻¹)*(3*(k : ℝ)*M) := by gcongr
      _ ≤ C*(α⁻¹^2+(ε*α)⁻¹)*(3*(k : ℝ)*D) := by gcongr
      _ = _ := by ring
  have ht := mul_le_mul_of_nonneg_left htotal (Nat.cast_nonneg k : (0 : ℝ) ≤ _)
  have hfinal : (validationSize C α β ε k M : ℝ) ≤ (k : ℝ)*n := by nlinarith only [hceil,hqbound,ht,hk1]
  exact_mod_cast hfinal
end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.Sol_ordered_regression_learning
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian

theorem solution :
    ∃ O : Optimizer, RealizesOrderedRegression O ∧
      (∀ d p n : ℕ, 0 < n → ∀ ε δ : ℝ,
        0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
        Measurable (fun S => (O d p n ε δ S : Measure (UnitBall d p))) ∧
        PrivateUniformGen.Characterization.IsDP (O d p n ε δ) ε δ ∧
        ∀ S : Fin n → Example d,
          Integrable (fun v : UnitBall d p => empiricalLoss d p S v.val-
            sInf (empiricalLoss d p S '' Metric.closedBall 0 1))
            (O d p n ε δ S : Measure (UnitBall d p)) ∧
          (∫ v : UnitBall d p, empiricalLoss d p S v.val-
            sInf (empiricalLoss d p S '' Metric.closedBall 0 1)
            ∂(O d p n ε δ S : Measure (UnitBall d p))) ≤
              120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)) ∧
      ∃ C c Cdim : ℝ, 1 ≤ C ∧ 0 < c ∧ c ≤ 1/4 ∧ 0 < Cdim ∧ 2*(C+1)^2/c ≤ Cdim ∧
      ∀ α β ε δ : ℝ, 0 < α ∧ α ≤ 1/2 → 0 < β ∧ β ≤ 1/2 →
        0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
      ∀ d : ℕ, Cdim/α^5 ≤ (d : ℝ) →
      let p := scheduledDegree C α
      let D := featureDimension d p
      let k := repetitions β
      let M := thresholds C α
      let n₀ := trainingSize C c α ε δ d p
      let m := validationSize C α β ε k M
      let n := k*n₀+m
      blockCondition C c α ε δ d p n₀ ∧
      (∀ r, blockCondition C c α ε δ d p r → n₀ ≤ r) ∧
      0 < k ∧ 0 < M ∧ 0 < m ∧ 1 ≤ p ∧ D ≤ n₀ ∧ p ≤ D ∧ M ≤ p ∧ m ≤ k*n₀ ∧
      (n : ℝ) ≤ (k : ℝ)*(3+4*C^2*D/(c^2*α^2)+4*C*D*Real.sqrt (Real.log (1/δ))/(c*ε*α))+1+
        C*(α⁻¹^2+(ε*α)⁻¹)*Real.log ((k : ℝ)*M/β) ∧
      ∀ P : Measure (Example d), IsProbabilityMeasure P → P.map Prod.fst=gaussian d →
      let ν := (Measure.pi (fun _ : Fin n => P)).bind (fun S => algorithmLaw O d p k M n₀ m ε δ S)
      IsProbabilityMeasure ν ∧ ν.real {o | error P (decode d p M o) ≤ opt d P+α} ≥ 1-β := by
  refine ⟨operationalOptimizer,operationalOptimizer_realizes,?_,?_⟩
  · intro d p n hn ε δ hε hδ
    exact ⟨operationalOptimizer_measurable d p n ε δ,
      operationalOptimizer_private d p n hn ε δ hε hδ,
      fun S => operationalOptimizer_excess d p n hn ε δ hε hδ S⟩
  · obtain ⟨C,c,Cdim,hC,hc,hc4,hCdim,hCdimBound,hCbig,hc64,hStat⟩ := scheduled_accuracy_operational_constants
    refine ⟨C,c,Cdim,hC,hc,hc4,hCdim,hCdimBound,?_⟩
    intro α β ε δ hα hβ hε hδ d hd
    dsimp only
    let p := scheduledDegree C α
    let D := featureDimension d p
    let k := repetitions β
    let M := thresholds C α
    let n₀ := trainingSize C c α ε δ d p
    let m := validationSize C α β ε k M
    obtain ⟨hBlock,hMinimal,hk,hM,hm,hd1,hp,hAccuracy⟩ := hStat α β ε δ hα hβ hε hδ d hd
    have hDn : D ≤ n₀ := training_dimension_le C c α ε δ d p n₀ hC ⟨hc,hc4⟩ hα hε.1 hBlock
    have hpD : p ≤ D := by have hh := degree_dimension_le d p hd1; omega
    have hMp : M ≤ p := thresholds_le_degree C α (by linarith) hα
    have hmBlock : m ≤ k*n₀ := validation_le_training_blocks C c α β ε δ d p n₀ M hC ⟨hc,hc64⟩ hα.1 hβ hε.1 hδ hM (hMp.trans hpD) hBlock
    have hSample := sample_size_bound C c α β ε δ d p (by linarith) hc hα.1 hβ hε.1 hδ
    refine ⟨hBlock,hMinimal,hk,hM,hm,hp,hDn,hpD,hMp,hmBlock,hSample,?_⟩
    intro P hProb hGaussian
    have hOeq := operationalOptimizer_eq d p n₀ hDn ε δ
    have hLaw (S : Fin (k*n₀+m) → Example d) : algorithmLaw operationalOptimizer d p k M n₀ m ε δ S=
        algorithmLaw concreteOptimizer d p k M n₀ m ε δ S := by
      unfold algorithmLaw
      rw [hOeq]
    have hν := congrArg (fun F : (Fin (k*n₀+m) → Example d) → Measure (Output d p M) =>
      (Measure.pi (fun _ : Fin (k*n₀+m) => P)).bind F) (funext hLaw)
    have hResult := hAccuracy P hProb hGaussian
    rw [← hν] at hResult
    exact hResult
end
