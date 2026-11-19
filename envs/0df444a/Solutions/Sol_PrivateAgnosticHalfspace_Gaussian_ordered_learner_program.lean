-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.ordered_learner_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:03:50.27073+00:00
-- url     : https://prove2.me/submissions/f6ec106b-7fe2-439b-aa6c-0fbe58bcc38d

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_OptimizerRealization
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Definitions.Def_NonconvexAG_StochComposite_RSAG
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Computation
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_3
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_5
import Mathlib.Data.Nat.ModEq
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Dirac
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
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def momentHermiteR (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)
noncomputable def momentHermiteFactor {d : ℕ} (i : Fin d) (n : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ k ∈ Finset.range (n+1), MvPolynomial.C ((momentHermiteR n).coeff k / Real.sqrt (n.factorial : ℝ)) *
    MvPolynomial.X i ^ k
noncomputable def momentHermiteTensor (d : ℕ) (κ : Fin d → ℕ) : MvPolynomial (Fin d) ℝ :=
  ∏ i, momentHermiteFactor i (κ i)
noncomputable def cutoffPolynomial (d p : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ κ : Index d p, momentHermiteTensor d (fun i => (κ.val i).val) ^ 2
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
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
-- Solutions.ThresholdTranslation
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def thresholdStep (θ x : ℝ) : ℝ := if θ ≤ x then 1 else -1
lemma thresholdStep_measurable (θ : ℝ) : Measurable (thresholdStep θ) := by
  unfold thresholdStep
  exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.SmoothedRegressionOracle
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry

noncomputable def scalarSmoothedSubgradient {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ)
    (v : Vec D) (z : ℝ) : Vec D :=
  thresholdStep 0 (inner ℝ v a-y+r*‖a‖*z) • a

lemma scalarSmoothedSubgradient_measurable {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ) :
    Measurable (fun q : Vec D × ℝ => scalarSmoothedSubgradient r a y q.1 q.2) := by
  exact ((thresholdStep_measurable 0).comp (by fun_prop)).smul measurable_const

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
-- Solutions.NoisyRegressionOracle
open MeasureTheory ProbabilityTheory Set Finset
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

lemma noisyRegressionOracle_measurable {D n : ℕ} (r τ : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) :
    Measurable (Function.uncurry (noisyRegressionOracle r τ a y)) := by
  have hbatch : Measurable (fun q : Vec D × RegressionNoise n D =>
      batchSmoothedSubgradient r a y q.1 q.2.1) := by
    convert! (batchSmoothedSubgradient_measurable r a y).comp
      (measurable_fst.prodMk measurable_snd.fst) using 1
  exact hbatch.add (measurable_snd.snd.const_smul τ)
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.SmoothedRegressionOptimization
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
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

lemma regressionVectorOutput_measurable {D n : ℕ} (r τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) : Measurable (regressionVectorOutput r τ β a y) := by
  have hP : Measurable (fun q : (Vec D × Vec D) × ℝ => unitProjection (q.1.1-q.2 • q.1.2)) :=
    (unitProjection_continuous D).measurable.comp (by fun_prop)
  have h := rsagPath_one_measurable (noisyRegressionOracle r τ a y) (noisyRegressionOracle_measurable r τ a y)
    (fun x z c => unitProjection (x-c • z)) hP accelAlpha (fun _ => β) (accelLambda β) 0
    (fun k (s : Fin (n+1) → RegressionNoise n D) => finiteNoiseSequence (0,0) s k)
    (fun k => finiteNoiseSequence_measurable (N := n) (0,0) k) n
  exact h.snd
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
lemma coefficientIsometry_symm_coordinate (d p : ℕ) (v : Vec (featureDimension d p)) (κ : Index d p) :
    (coefficientIsometry d p).symm v κ = v (coefficientIndexEquiv d p κ) := by
  simp [coefficientIsometry,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
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
-- Solutions.PublicOptimizerBranch
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian

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
lemma realizesOrderedRegression_unique (O : Optimizer) (hO : RealizesOrderedRegression O) :
    O=operationalOptimizer := by
  obtain ⟨e,he,hm⟩ := hO
  have heq (d p : ℕ) : e d p=coefficientIndexEquiv d p := by
    ext κ
    exact he d p κ
  funext d p n ε δ S
  apply Subtype.ext
  apply (MeasurableEmbedding.subtype_coe (isClosed_le continuous_norm continuous_const).measurableSet).map_injective
  change (O d p n ε δ S : Measure (UnitBall d p)).map Subtype.val =
    (operationalOptimizer d p n ε δ S : Measure (UnitBall d p)).map Subtype.val
  rw [hm,heq,operationalOptimizer_raw_law]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.StructuredRAM
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
structure Store where
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ
  gc : ℕ
  ec : ℕ
noncomputable def frame (s : Store) (pc work : ℕ) : PolySampIso.State :=
  ⟨⟨pc,s.regs,s.ptrs,s.mem⟩,s.gc,s.ec,false,work⟩
inductive Op where
  | literal (r : ℕ) (q : ℚ)
  | add (r i j : ℕ)
  | sub (r i j : ℕ)
  | mul (r i j : ℕ)
  | div (r i j : ℕ)
  | load (r q : ℕ)
  | store (q r : ℕ)
  | pset (q : ℕ) (z : ℤ)
  | pcopy (q r : ℕ)
  | pinc (q : ℕ)
  | pdec (q : ℕ)
  | pointerReal (r q : ℕ)
  | sqrt (r i : ℕ)
  | exp (r i : ℕ)
  | log (r i : ℕ)
  | gauss (r : ℕ)
  | expo (r : ℕ)
def Op.instr : Op → PolySampIso.Instr
  | .literal r q => .core (.const r q)
  | .add r i j => .core (.add r i j)
  | .sub r i j => .core (.sub r i j)
  | .mul r i j => .core (.mul r i j)
  | .div r i j => .core (.div r i j)
  | .load r q => .core (.load r q)
  | .store q r => .core (.store q r)
  | .pset q z => .core (.pset q z)
  | .pcopy q r => .core (.pcopy q r)
  | .pinc q => .core (.pinc q)
  | .pdec q => .core (.pdec q)
  | .pointerReal r q => .pointerReal r q
  | .sqrt r i => .sqrt r i
  | .exp r i => .exp r i
  | .log r i => .log r i
  | .gauss r => .gauss r
  | .expo r => .expo r
noncomputable def Op.act (ω : PolySampIso.Streams) (s : Store) : Op → Store
  | .literal r q => {s with regs := Function.update s.regs r q}
  | .add r i j => {s with regs := Function.update s.regs r (s.regs i+s.regs j)}
  | .sub r i j => {s with regs := Function.update s.regs r (s.regs i-s.regs j)}
  | .mul r i j => {s with regs := Function.update s.regs r (s.regs i*s.regs j)}
  | .div r i j => {s with regs := Function.update s.regs r (s.regs i/s.regs j)}
  | .load r q => {s with regs := Function.update s.regs r (s.mem (s.ptrs q))}
  | .store q r => {s with mem := Function.update s.mem (s.ptrs q) (s.regs r)}
  | .pset q z => {s with ptrs := Function.update s.ptrs q z}
  | .pcopy q r => {s with ptrs := Function.update s.ptrs q (s.ptrs r)}
  | .pinc q => {s with ptrs := Function.update s.ptrs q (s.ptrs q+1)}
  | .pdec q => {s with ptrs := Function.update s.ptrs q (s.ptrs q-1)}
  | .pointerReal r q => {s with regs := Function.update s.regs r (s.ptrs q : ℝ)}
  | .sqrt r i => {s with regs := Function.update s.regs r (Real.sqrt (s.regs i))}
  | .exp r i => {s with regs := Function.update s.regs r (Real.exp (s.regs i))}
  | .log r i => {s with regs := Function.update s.regs r (Real.log (s.regs i))}
  | .gauss r => {s with regs := Function.update s.regs r (ω.1 s.gc), gc := s.gc+1}
  | .expo r => {s with regs := Function.update s.regs r (ω.2 s.ec), ec := s.ec+1}
inductive Test where
  | real (i : ℕ)
  | pointer (q r : ℕ)
def Test.holds (s : Store) : Test → Prop
  | .real i => s.regs i ≤ 0
  | .pointer q r => s.ptrs q ≤ s.ptrs r
noncomputable instance (s : Store) (t : Test) : Decidable (t.holds s) := by
  cases t <;> unfold Test.holds <;> infer_instance
def Test.instr (t : Test) (target : ℕ) : PolySampIso.Instr :=
  match t with
  | .real i => .core (.jle i target)
  | .pointer q r => .core (.pjle q r target)
inductive Cmd where
  | skip
  | atom (o : Op)
  | seq (a b : Cmd)
  | cond (t : Test) (yes no : Cmd)
  | loop (t : Test) (body : Cmd)
def Cmd.size : Cmd → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq a b => a.size+b.size
  | .cond _ a b => 2+b.size+a.size
  | .loop _ b => 3+b.size
def jump (target : ℕ) : PolySampIso.Instr := .core (.pjle 0 0 target)
def Cmd.compile : Cmd → ℕ → PolySampIso.Program
  | .skip,_ => []
  | .atom o,_ => [o.instr]
  | .seq a b,pc => a.compile pc++b.compile (pc+a.size)
  | .cond t yes no,pc => [t.instr (pc+no.size+2)]++no.compile (pc+1)++
      [jump (pc+2+no.size+yes.size)]++yes.compile (pc+no.size+2)
  | .loop t body,pc => [t.instr (pc+2),jump (pc+3+body.size)]++body.compile (pc+2)++[jump pc]
@[simp] lemma compile_length (c : Cmd) (pc : ℕ) : (c.compile pc).length = c.size := by
  induction c generalizing pc <;> simp_all [Cmd.compile,Cmd.size] <;> omega
inductive Eval (ω : PolySampIso.Streams) : Cmd → Store → Store → ℕ → Prop
  | skip (s) : Eval ω .skip s s 0
  | atom (s) (o) : Eval ω (.atom o) s (o.act ω s) 1
  | seq {a b s t u k l} : Eval ω a s t k → Eval ω b t u l → Eval ω (.seq a b) s u (k+l)
  | cond_yes {test yes no s t k} : test.holds s → Eval ω yes s t k →
      Eval ω (.cond test yes no) s t (1+k)
  | cond_no {test yes no s t k} : ¬test.holds s → Eval ω no s t k →
      Eval ω (.cond test yes no) s t (2+k)
  | loop_done {test body s} : ¬test.holds s → Eval ω (.loop test body) s s 2
  | loop_step {test body s t u k l} : test.holds s → Eval ω body s t k →
      Eval ω (.loop test body) t u l → Eval ω (.loop test body) s u (2+k+l)
def Fits (code : PolySampIso.Program) (pc : ℕ) (block : PolySampIso.Program) : Prop :=
  ∀ i, i < block.length → code[pc+i]? = block[i]?
lemma fits_append_left {code a b : PolySampIso.Program} {pc : ℕ} (h : Fits code pc (a++b)) : Fits code pc a := by
  intro i hi
  rw [h i (by simpa using lt_of_lt_of_le hi (Nat.le_add_right a.length b.length))]
  exact List.getElem?_append_left hi
lemma fits_append_right {code a b : PolySampIso.Program} {pc : ℕ} (h : Fits code pc (a++b)) : Fits code (pc+a.length) b := by
  intro i hi
  rw [show pc+a.length+i = pc+(a.length+i) by omega,h (a.length+i) (by simp; omega)]
  rw [List.getElem?_append_right (by omega)]
  simp
lemma fits_singleton {code : PolySampIso.Program} {pc : ℕ} {op : PolySampIso.Instr} (h : Fits code pc [op]) : code[pc]? = some op := by
  simpa using h 0 (by simp)
lemma coreProgram_at {code : PolySampIso.Program} {pc : ℕ} {op : SmaleNinth.RAMInstr}
    (h : code[pc]? = some (.core op)) : (PolySampIso.coreProgram code)[pc]? = some op := by
  simp [PolySampIso.coreProgram,List.getElem?_map,h]
lemma step_atom (code : PolySampIso.Program) (ω : PolySampIso.Streams) (s : Store) (pc w : ℕ) (o : Op)
    (h : code[pc]? = some o.instr) :
    PolySampIso.step code ω (frame s pc w) = frame (o.act ω s) (pc+1) (w+1) := by
  cases o <;> simp_all [PolySampIso.step,frame,Op.instr,Op.act,SmaleNinth.RAMStep,coreProgram_at]
lemma step_test (code : PolySampIso.Program) (ω : PolySampIso.Streams) (s : Store) (pc w target : ℕ) (t : Test)
    (h : code[pc]? = some (t.instr target)) :
    PolySampIso.step code ω (frame s pc w) = frame s (if t.holds s then target else pc+1) (w+1) := by
  cases t with
  | real i =>
    by_cases hi : s.regs i ≤ 0 <;>
      simp [PolySampIso.step,frame,Test.instr,Test.holds,SmaleNinth.RAMStep,coreProgram_at,h,hi]
  | pointer q r =>
    by_cases hi : s.ptrs q ≤ s.ptrs r <;>
      simp [PolySampIso.step,frame,Test.instr,Test.holds,SmaleNinth.RAMStep,coreProgram_at,h,hi]
lemma step_jump (code : PolySampIso.Program) (ω : PolySampIso.Streams) (s : Store) (pc w target : ℕ)
    (h : code[pc]? = some (jump target)) :
    PolySampIso.step code ω (frame s pc w) = frame s target (w+1) := by
  simpa [jump,Test.holds] using step_test code ω s pc w target (.pointer 0 0) h
lemma run_add (code : PolySampIso.Program) (ω : PolySampIso.Streams) (s : PolySampIso.State) (k l : ℕ) :
    PolySampIso.run code s ω (k+l) = PolySampIso.run code (PolySampIso.run code s ω k) ω l := by
  simpa only [PolySampIso.run,Nat.add_comm] using (Function.iterate_add_apply (PolySampIso.step code ω) l k s)
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.StructuredRAMCompiler
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
@[simp] lemma run_zero (P : PolySampIso.Program) (s : PolySampIso.State) (ω : PolySampIso.Streams) : PolySampIso.run P s ω 0 = s := rfl
@[simp] lemma run_one (P : PolySampIso.Program) (s : PolySampIso.State) (ω : PolySampIso.Streams) : PolySampIso.run P s ω 1 = PolySampIso.step P ω s := rfl
lemma run_cons (P : PolySampIso.Program) (s : PolySampIso.State) (ω : PolySampIso.Streams) (k : ℕ) :
    PolySampIso.run P s ω (1+k) = PolySampIso.run P (PolySampIso.step P ω s) ω k := by rw [run_add,run_one]
lemma fits_append_three₁ {P a b c : PolySampIso.Program} {pc : ℕ} (h : Fits P pc (a++b++c)) : Fits P pc a :=
  fits_append_left (fits_append_left h)
lemma fits_append_three₂ {P a b c : PolySampIso.Program} {pc : ℕ} (h : Fits P pc (a++b++c)) : Fits P (pc+a.length) b :=
  fits_append_right (fits_append_left h)
lemma fits_append_three₃ {P a b c : PolySampIso.Program} {pc : ℕ} (h : Fits P pc (a++b++c)) : Fits P (pc+a.length+b.length) c := by
  simpa [Nat.add_assoc] using fits_append_right h
lemma cond_fits {P : PolySampIso.Program} {pc : ℕ} {t : Test} {yes no : Cmd}
    (h : Fits P pc ((Cmd.cond t yes no).compile pc)) :
    P[pc]? = some (t.instr (pc+no.size+2)) ∧
    Fits P (pc+1) (no.compile (pc+1)) ∧
    P[pc+1+no.size]? = some (jump (pc+2+no.size+yes.size)) ∧
    Fits P (pc+no.size+2) (yes.compile (pc+no.size+2)) := by
  change Fits P pc (([t.instr (pc+no.size+2)]++no.compile (pc+1)++[jump (pc+2+no.size+yes.size)])++yes.compile (pc+no.size+2)) at h
  have hpre := fits_append_left h
  have hy := fits_append_right h
  refine ⟨fits_singleton (fits_append_three₁ hpre),?_,?_,?_⟩
  · simpa using fits_append_three₂ hpre
  · simpa using fits_singleton (fits_append_three₃ hpre)
  · convert hy using 1 <;> simp <;> omega
lemma loop_fits {P : PolySampIso.Program} {pc : ℕ} {t : Test} {body : Cmd}
    (h : Fits P pc ((Cmd.loop t body).compile pc)) :
    P[pc]? = some (t.instr (pc+2)) ∧
    P[pc+1]? = some (jump (pc+3+body.size)) ∧
    Fits P (pc+2) (body.compile (pc+2)) ∧
    P[pc+2+body.size]? = some (jump pc) := by
  change Fits P pc (([t.instr (pc+2)]++[jump (pc+3+body.size)])++body.compile (pc+2)++[jump pc]) at h
  have hpre := fits_append_three₁ h
  refine ⟨fits_singleton (fits_append_left hpre),?_,?_,?_⟩
  · simpa using fits_singleton (fits_append_right hpre)
  · simpa using fits_append_three₂ h
  · simpa using fits_singleton (fits_append_three₃ h)
lemma Eval.run {ω : PolySampIso.Streams} {c : Cmd} {s t : Store} {k : ℕ} (h : Eval ω c s t k)
    (P : PolySampIso.Program) (pc w : ℕ) (hc : Fits P pc (c.compile pc)) :
    PolySampIso.run P (frame s pc w) ω k = frame t (pc+c.size) (w+k) := by
  induction h generalizing P pc w with
  | skip => simp [Cmd.size]
  | atom s o => simpa [Cmd.compile,Cmd.size] using step_atom P ω s pc w o (fits_singleton hc)
  | @seq a b s t u k l ha hb iha ihb =>
    change Fits P pc (a.compile pc++b.compile (pc+a.size)) at hc
    have hca := fits_append_left hc
    have hcb : Fits P (pc+a.size) (b.compile (pc+a.size)) := by simpa using fits_append_right hc
    rw [run_add,iha P pc w hca,ihb P (pc+a.size) (w+k) hcb]
    simp [Cmd.size,Nat.add_assoc]
  | @cond_yes test yes no s t k ht he ih =>
    obtain ⟨hhead,hno,hjump,hyes⟩ := cond_fits hc
    rw [run_cons,step_test P ω s pc w _ test hhead,if_pos ht,ih P _ (w+1) hyes]
    simp [Cmd.size] <;> congr 1 <;> omega
  | @cond_no test yes no s t k ht he ih =>
    obtain ⟨hhead,hno,hjump,hyes⟩ := cond_fits hc
    rw [show 2+k = 1+(k+1) by omega,run_cons,step_test P ω s pc w _ test hhead,if_neg ht,
      run_add,ih P _ (w+1) hno,run_one,step_jump P ω t _ _ _ hjump]
    simp [Cmd.size] <;> congr 1 <;> omega
  | @loop_done test body s ht =>
    obtain ⟨hhead,hjump,hbody,hback⟩ := loop_fits hc
    rw [show 2 = 1+1 by omega,run_cons,step_test P ω s pc w _ test hhead,if_neg ht,
      run_one,step_jump P ω s _ _ _ hjump]
    simp [Cmd.size] <;> congr 1 <;> omega
  | @loop_step test body s t u k l ht hb hl ihb ihl =>
    obtain ⟨hhead,hjump,hbody,hback⟩ := loop_fits hc
    rw [show 2+k+l = 1+(k+(1+l)) by omega,run_cons,
      step_test P ω s pc w _ test hhead,if_pos ht,run_add,ihb P _ (w+1) hbody,
      run_cons,step_jump P ω t _ _ _ hback,ihl P pc _ hc]
    simp [Cmd.size] <;> congr 1 <;> omega
lemma compile_admissible (c : Cmd) (pc : ℕ) : PolySampIso.Admissible (c.compile pc) := by
  intro op hop
  induction c generalizing pc with
  | skip => simp [Cmd.compile] at hop
  | atom o =>
    simp only [Cmd.compile,List.mem_singleton] at hop
    subst op
    cases o <;> simp [Op.instr,PolySampIso.Admissible]
  | seq a b iha ihb =>
    simp only [Cmd.compile,List.mem_append] at hop
    exact hop.elim (iha pc) (ihb (pc+a.size))
  | cond test yes no ihy ihn =>
    simp only [Cmd.compile,List.mem_append,List.mem_singleton] at hop
    rcases hop with ((rfl|hn)|rfl)|hy
    · cases test <;> trivial
    · exact ihn _ hn
    · trivial
    · exact ihy _ hy
  | loop test body ih =>
    simp only [Cmd.compile,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hop
    rcases hop with ((rfl|rfl)|hb)|rfl
    · cases test <;> trivial
    · trivial
    · exact ih _ hb
    · trivial
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.StructuredRAMImplementation
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
noncomputable def initialStore (d p M : ℕ) (input : ℕ → ℝ) : Store :=
  ⟨fun _ => 0,fun q => if q=0 then (d : ℤ) else if q=1 then (p : ℤ) else if q=2 then (M : ℤ) else 0,
    fun z => if 0 ≤ z then input z.toNat else 0,0,0⟩
lemma initialState_frame (d p M : ℕ) (input : ℕ → ℝ) : initialState d p M input = frame (initialStore d p M input) 0 0 := rfl
def Cmd.program (c : Cmd) : LearnerProgram := c.compile 0++[.halt]
lemma program_admissible (c : Cmd) : PolySampIso.Admissible c.program := by
  intro op hop
  simp only [Cmd.program,List.mem_append,List.mem_singleton] at hop
  rcases hop with h|rfl
  · exact compile_admissible c 0 op h
  · trivial
lemma program_fits (c : Cmd) : Fits c.program 0 (c.compile 0) := by
  intro i hi
  simpa [Cmd.program] using List.getElem?_append_left (l₂ := [PolySampIso.Instr.halt]) hi
lemma step_halted (P : PolySampIso.Program) (ω : PolySampIso.Streams) (s : PolySampIso.State) (hs : s.halted = true) :
    PolySampIso.step P ω s = s := by simp [PolySampIso.step,hs]
lemma run_halted (P : PolySampIso.Program) (ω : PolySampIso.Streams) (s : PolySampIso.State) (hs : s.halted = true) (k : ℕ) :
    PolySampIso.run P s ω k = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show k+1 = k+1 by rfl,run_add,ih,run_one,step_halted P ω s hs]
lemma run_pad {P : PolySampIso.Program} {ω : PolySampIso.Streams} {s t : PolySampIso.State} {k K : ℕ}
    (h : PolySampIso.run P s ω k = t) (ht : t.halted = true) (hk : k ≤ K) : PolySampIso.run P s ω K = t := by
  rw [← Nat.add_sub_of_le hk,run_add,h,run_halted P ω t ht]
noncomputable def stopped (s : Store) (pc w : ℕ) : PolySampIso.State :=
  {frame s (pc+1) w with halted := true}
lemma eval_program {ω : PolySampIso.Streams} {c : Cmd} {s t : Store} {k : ℕ} (h : Eval ω c s t k) :
    PolySampIso.run c.program (frame s 0 0) ω (k+1) = stopped t c.size (k+1) := by
  rw [run_add,h.run c.program 0 0 (program_fits c),run_one]
  have hhalt : c.program[c.size]? = some .halt := by
    simp [Cmd.program,List.getElem?_append_right,compile_length]
  simp only [Nat.zero_add] at *
  simp [PolySampIso.step,frame,stopped,hhalt]
lemma implements_of_eval (c : Cmd) (d p M K : ℕ) (input : ℕ → ℝ) (ν : Measure (Output d p M))
    (result : PolySampIso.Streams → Store) (steps : PolySampIso.Streams → ℕ)
    (he : ∀ ω, Eval ω c (initialStore d p M input) (result ω) (steps ω))
    (hk : ∀ ω, steps ω+1 ≤ K)
    (hw : ∀ ω, let r := fun i : ℕ => (result ω).mem (-1-(i : ℤ))
      ‖(rawOutput d p r).1‖ ≤ 1 ∧ (rawOutput d p r).2 < M ∧
        r (Fintype.card (Index d p)) = ((rawOutput d p r).2 : ℝ))
    (hm : Measurable (fun ω => rawOutput d p (fun i => (result ω).mem (-1-(i : ℤ)))))
    (hl : PolySampIso.tape.map (fun ω => rawOutput d p (fun i => (result ω).mem (-1-(i : ℤ)))) =
      ν.map (fun v => (v.1.val,v.2.val))) : Implements c.program K K d p M input ν := by
  have hr (ω) : PolySampIso.run c.program (initialState d p M input) ω K = stopped (result ω) c.size (steps ω+1) := by
    rw [initialState_frame]
    exact run_pad (eval_program (he ω)) rfl (hk ω)
  refine ⟨program_admissible c,?_,?_,?_⟩
  · intro ω
    rw [hr ω]
    exact ⟨rfl,hk ω,(hw ω).1,(hw ω).2.1,(hw ω).2.2⟩
  · simp only [hr]
    convert! hm using 1
  · simp only [hr]
    convert! hl using 1
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.StructuredRAMLoops
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def Cmd.block (ops : List Op) : Cmd := (ops.map Cmd.atom).foldr Cmd.seq .skip
noncomputable def blockAct (ω : PolySampIso.Streams) (ops : List Op) (s : Store) : Store :=
  ops.foldl (fun t o => o.act ω t) s
lemma eval_block (ω : PolySampIso.Streams) (ops : List Op) (s : Store) :
    Eval ω (Cmd.block ops) s (blockAct ω ops s) ops.length := by
  induction ops generalizing s with
  | nil => exact Eval.skip s
  | cons o ops ih =>
    simpa [Cmd.block,blockAct,Nat.add_comm] using Eval.seq (Eval.atom s o) (ih (o.act ω s))
lemma eval_loop_range (ω : PolySampIso.Streams) (test : Test) (body : Cmd)
    (N : ℕ) (states : ℕ → Store) (cost : ℕ → ℕ)
    (htrue : ∀ i, i < N → test.holds (states i)) (hfalse : ¬test.holds (states N))
    (hbody : ∀ i, i < N → Eval ω body (states i) (states (i+1)) (cost i)) :
    Eval ω (.loop test body) (states 0) (states N) (2+∑ i ∈ Finset.range N, (2+cost i)) := by
  induction N generalizing states cost with
  | zero => simpa using Eval.loop_done hfalse
  | succ N ih =>
    have htail := ih (fun i => states (i+1)) (fun i => cost (i+1))
      (fun i hi => htrue (i+1) (by omega)) hfalse (fun i hi => hbody (i+1) (by omega))
    have he := Eval.loop_step (htrue 0 (by omega)) (hbody 0 (by omega)) htail
    convert he using 1
    rw [Finset.sum_range_succ']
    omega
end PrivateAgnosticHalfspace.Gaussian.RAM

namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma eval_loop_invariant (ω : PolySampIso.Streams) (test : Test) (body : Cmd) (N B : ℕ)
    (Inv : ℕ → Store → Prop)
    (htrue : ∀ i, i < N → ∀ s, Inv i s → test.holds s)
    (hfalse : ∀ s, Inv N s → ¬test.holds s)
    (hbody : ∀ i, i < N → ∀ s, Inv i s → ∃ t k, k ≤ B ∧ Eval ω body s t k ∧ Inv (i+1) t)
    (s : Store) (hinit : Inv 0 s) :
    ∃ t k, k ≤ 2+N*(2+B) ∧ Eval ω (.loop test body) s t k ∧ Inv N t := by
  induction N generalizing Inv s with
  | zero => exact ⟨s,2,by simp,Eval.loop_done (hfalse s hinit),hinit⟩
  | succ N ih =>
    obtain ⟨u,k,hk,he,hu⟩ := hbody 0 (by omega) s hinit
    obtain ⟨t,l,hl,hr,ht⟩ := ih (fun i s => Inv (i+1) s)
      (fun i hi s hs => htrue (i+1) (by omega) s hs) hfalse
      (fun i hi s hs => hbody (i+1) (by omega) s hs) u hu
    refine ⟨t,2+k+l,?_,Eval.loop_step (htrue 0 (by omega) s hinit) he hr,ht⟩
    nlinarith only [hk,hl]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.StructuredRAMFootprint
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def Op.registers : Op → Finset ℕ
  | .literal r _ | .add r _ _ | .sub r _ _ | .mul r _ _ | .div r _ _ | .load r _ |
    .pointerReal r _ | .sqrt r _ | .exp r _ | .log r _ | .gauss r | .expo r => {r}
  | _ => ∅
def Op.pointers : Op → Finset ℕ
  | .pset q _ | .pcopy q _ | .pinc q | .pdec q => {q}
  | _ => ∅
def Op.stores : Op → Bool
  | .store _ _ => true
  | _ => false
def Cmd.registers : Cmd → Finset ℕ
  | .skip => ∅
  | .atom o => o.registers
  | .seq a b | .cond _ a b => a.registers∪b.registers
  | .loop _ b => b.registers
def Cmd.pointers : Cmd → Finset ℕ
  | .skip => ∅
  | .atom o => o.pointers
  | .seq a b | .cond _ a b => a.pointers∪b.pointers
  | .loop _ b => b.pointers
def Cmd.stores : Cmd → Bool
  | .skip => false
  | .atom o => o.stores
  | .seq a b | .cond _ a b => a.stores||b.stores
  | .loop _ b => b.stores
lemma Eval.register_preserved {ω : PolySampIso.Streams} {c : Cmd} {s t : Store} {k r : ℕ}
    (h : Eval ω c s t k) (hr : r ∉ c.registers) : t.regs r=s.regs r := by
  induction h with
  | skip => rfl
  | atom s o => cases o <;> simp_all [Cmd.registers,Op.registers,Op.act,Function.update_apply]
  | seq ha hb iha ihb => simp only [Cmd.registers,Finset.mem_union,not_or] at hr; exact (ihb hr.2).trans (iha hr.1)
  | cond_yes ht he ih => exact ih (by simp_all [Cmd.registers])
  | cond_no ht he ih => exact ih (by simp_all [Cmd.registers])
  | loop_done => rfl
  | loop_step ht hb hl ihb ihl => exact (ihl hr).trans (ihb hr)
lemma Eval.pointer_preserved {ω : PolySampIso.Streams} {c : Cmd} {s t : Store} {k q : ℕ}
    (h : Eval ω c s t k) (hq : q ∉ c.pointers) : t.ptrs q=s.ptrs q := by
  induction h with
  | skip => rfl
  | atom s o => cases o <;> simp_all [Cmd.pointers,Op.pointers,Op.act,Function.update_apply]
  | seq ha hb iha ihb => simp only [Cmd.pointers,Finset.mem_union,not_or] at hq; exact (ihb hq.2).trans (iha hq.1)
  | cond_yes ht he ih => exact ih (by simp_all [Cmd.pointers])
  | cond_no ht he ih => exact ih (by simp_all [Cmd.pointers])
  | loop_done => rfl
  | loop_step ht hb hl ihb ihl => exact (ihl hq).trans (ihb hq)
lemma Eval.memory_preserved {ω : PolySampIso.Streams} {c : Cmd} {s t : Store} {k : ℕ}
    (h : Eval ω c s t k) (hc : c.stores=false) : t.mem=s.mem := by
  induction h with
  | skip => rfl
  | atom s o => cases o <;> simp_all [Cmd.stores,Op.stores,Op.act]
  | seq ha hb iha ihb => simp only [Cmd.stores,Bool.or_eq_false_iff] at hc; exact (ihb hc.2).trans (iha hc.1)
  | cond_yes ht he ih => exact ih (by simp_all [Cmd.stores])
  | cond_no ht he ih => exact ih (by simp_all [Cmd.stores])
  | loop_done => rfl
  | loop_step ht hb hl ihb ihl => exact (ihl hc).trans (ihb hc)
def Op.samples : Op → Bool
  | .gauss _ | .expo _ => true
  | _ => false
def Cmd.samples : Cmd → Bool
  | .skip => false
  | .atom o => o.samples
  | .seq a b | .cond _ a b => a.samples||b.samples
  | .loop _ b => b.samples
lemma Eval.cursors_preserved {ω : PolySampIso.Streams} {c : Cmd} {s t : Store} {k : ℕ}
    (h : Eval ω c s t k) (hc : c.samples=false) : t.gc=s.gc ∧ t.ec=s.ec := by
  induction h with
  | skip => exact ⟨rfl,rfl⟩
  | atom s o => cases o <;> simp_all [Cmd.samples,Op.samples,Op.act]
  | seq ha hb iha ihb =>
    simp only [Cmd.samples,Bool.or_eq_false_iff] at hc
    exact ⟨(ihb hc.2).1.trans (iha hc.1).1,(ihb hc.2).2.trans (iha hc.1).2⟩
  | cond_yes ht he ih => exact ih (by simp_all [Cmd.samples])
  | cond_no ht he ih => exact ih (by simp_all [Cmd.samples])
  | loop_done => exact ⟨rfl,rfl⟩
  | loop_step ht hb hl ihb ihl => exact ⟨(ihl hc).1.trans (ihb hc).1,(ihl hc).2.trans (ihb hc).2⟩
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMReadNatural
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def naturalInit (q : ℕ) : List Op := [.pset q 0,.literal 43 1,.pointerReal 44 q,.add 41 44 43,.sub 41 41 40]
def naturalStep (q : ℕ) : List Op := [.pinc q,.pointerReal 44 q,.add 41 44 43,.sub 41 41 40]
def naturalLoop (q : ℕ) : Cmd := .loop (.real 41) (.block (naturalStep q))
def naturalCommand (q : ℕ) : Cmd := .seq (.block (naturalInit q)) (naturalLoop q)
def NaturalInvariant (n q i : ℕ) (s : Store) : Prop :=
  s.ptrs q=(i : ℤ) ∧ s.regs 41=(i : ℝ)+1-n ∧ s.regs 40=n ∧ s.regs 43=1
lemma natural_command_correct (ω : PolySampIso.Streams) (n q : ℕ) (s : Store) (hn : s.regs 40=n) :
    ∃ t, Eval ω (naturalCommand q) s t (7+6*n) ∧ t.ptrs q=n ∧ t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({41,43,44} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ j, j ≠ q → t.ptrs j=s.ptrs j) := by
  let u := blockAct ω (naturalInit q) s
  have hu : Eval ω (.block (naturalInit q)) s u 5 := eval_block ω _ s
  have hi : NaturalInvariant n q 0 u := by simp [NaturalInvariant,u,blockAct,naturalInit,Op.act,hn]
  have hstep (i : ℕ) (v : Store) (hv : NaturalInvariant n q i v) :
      NaturalInvariant n q (i+1) (blockAct ω (naturalStep q) v) := by
    rcases hv with ⟨hp,h41,h40,h43⟩
    simp [NaturalInvariant,blockAct,naturalStep,Op.act,hp,h40,h43,Nat.cast_add]
  let states := fun i => (blockAct ω (naturalStep q))^[i] u
  have hinv (i : ℕ) : NaturalInvariant n q i (states i) := by
    induction i with
    | zero => exact hi
    | succ i ih =>
      change NaturalInvariant n q (i+1) ((blockAct ω (naturalStep q))^[i+1] u)
      rw [Function.iterate_succ_apply']
      exact hstep i _ ih
  have htrue (i : ℕ) (hi : i < n) : Test.holds (states i) (.real 41) := by
    change (states i).regs 41 ≤ 0
    rw [(hinv i).2.1]
    have hh : (i : ℝ)+1 ≤ n := by exact_mod_cast (show i+1 ≤ n by omega)
    linarith
  have hfalse : ¬Test.holds (states n) (.real 41) := by
    change ¬(states n).regs 41 ≤ 0
    rw [(hinv n).2.1]
    linarith
  have he := eval_loop_range ω (.real 41) (.block (naturalStep q)) n states (fun _ => 4) htrue hfalse
    (fun i hi => by
      have hh : Eval ω (.block (naturalStep q)) (states i) (blockAct ω (naturalStep q) (states i)) 4 := eval_block ω _ _
      convert! hh using 1
      exact Function.iterate_succ_apply' _ i _)
  have hall : Eval ω (naturalCommand q) s (states n) (7+6*n) := by
    convert! Eval.seq hu he using 1 <;> simp <;> omega
  have hc := hall.cursors_preserved (by simp [naturalCommand,naturalLoop,naturalInit,naturalStep,Cmd.block,Cmd.samples,Op.samples])
  refine ⟨states n,hall,(hinv n).1,hall.memory_preserved (by simp [naturalCommand,naturalLoop,naturalInit,naturalStep,Cmd.block,Cmd.stores,Op.stores]),hc.1,hc.2,?_,?_⟩
  · intro r hr
    apply hall.register_preserved
    simp [naturalCommand,naturalLoop,naturalInit,naturalStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro j hj
    apply hall.pointer_preserved
    simp [naturalCommand,naturalLoop,naturalInit,naturalStep,Cmd.block,Cmd.pointers,Op.pointers,hj]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMHeaderNatural
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def headerPrefix (i : ℕ) : List Op := [.pset 30 (i : ℤ),.load 40 30]
def headerNaturalCommand (q i : ℕ) : Cmd := .seq (.block (headerPrefix i)) (naturalCommand q)
lemma header_natural_command_correct (ω : PolySampIso.Streams) (q i n : ℕ) (s : Store)
    (hn : s.mem (i : ℤ)=n) :
    ∃ t, Eval ω (headerNaturalCommand q i) s t (9+6*n) ∧ t.ptrs q=n ∧ t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({40,41,43,44} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ j, j ≠ q → j ≠ 30 → t.ptrs j=s.ptrs j) := by
  let u := blockAct ω (headerPrefix i) s
  have hu : Eval ω (.block (headerPrefix i)) s u 2 := eval_block ω _ s
  have hu40 : u.regs 40=n := by simpa [u,blockAct,headerPrefix,Op.act] using hn
  obtain ⟨t,he,hq,hm,hgc,hec,hreg,hptr⟩ := natural_command_correct ω n q u hu40
  have hall : Eval ω (headerNaturalCommand q i) s t (9+6*n) := by convert! Eval.seq hu he using 1 <;> omega
  refine ⟨t,hall,hq,hm,hgc,hec,?_,?_⟩
  · intro r hr
    apply hall.register_preserved
    simp [headerNaturalCommand,headerPrefix,naturalCommand,naturalLoop,naturalInit,naturalStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro j hjq hj30
    apply hall.pointer_preserved
    simp [headerNaturalCommand,headerPrefix,naturalCommand,naturalLoop,naturalInit,naturalStep,Cmd.block,Cmd.pointers,Op.pointers,hjq,hj30]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMAdvancePointer
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def advanceStep (q : ℕ) : List Op := [.pinc q,.pinc 12]
def advanceLoop (q b : ℕ) : Cmd := .loop (.pointer 12 b) (.block (advanceStep q))
def advanceCommand (q b : ℕ) : Cmd := .seq (.atom (.pset 12 1)) (advanceLoop q b)
lemma advance_loop_correct (ω : PolySampIso.Streams) (q b n : ℕ) (hq : q ≠ 12) (hb : b ≠ 12) (hbq : b ≠ q)
    (s : Store) (hbound : s.ptrs 12+(n : ℤ)=s.ptrs b+1) :
    ∃ t, Eval ω (advanceLoop q b) s t (2+4*n) ∧ t.ptrs q=s.ptrs q+n := by
  induction n generalizing s with
  | zero =>
    refine ⟨s,Eval.loop_done ?_,by simp⟩
    change ¬s.ptrs 12 ≤ s.ptrs b
    simp only [Nat.cast_zero,add_zero] at hbound
    omega
  | succ n ih =>
    have hhead : Test.holds s (.pointer 12 b) := by
      change s.ptrs 12 ≤ s.ptrs b
      push_cast at hbound
      omega
    let u := blockAct ω (advanceStep q) s
    have hu : Eval ω (.block (advanceStep q)) s u 2 := eval_block ω _ s
    have huq : u.ptrs q=s.ptrs q+1 := by simp [u,blockAct,advanceStep,Op.act,hq]
    have hu12 : u.ptrs 12=s.ptrs 12+1 := by simp [u,blockAct,advanceStep,Op.act,Ne.symm hq]
    have hub : u.ptrs b=s.ptrs b := by simp [u,blockAct,advanceStep,Op.act,hb,hbq]
    obtain ⟨t,he,htq⟩ := ih u (by rw [hu12,hub]; push_cast at hbound; omega)
    have hall := Eval.loop_step hhead hu he
    refine ⟨t,?_,?_⟩
    · convert! hall using 1 <;> omega
    · rw [htq,huq]
      push_cast
      ring
lemma advance_command_correct (ω : PolySampIso.Streams) (q b n : ℕ)
    (hq : q ≠ 12) (hb : b ≠ 12) (hbq : b ≠ q) (s : Store) (hn : s.ptrs b=n) :
    ∃ t, Eval ω (advanceCommand q b) s t (3+4*n) ∧ t.ptrs q=s.ptrs q+n ∧
      t.mem=s.mem ∧ t.regs=s.regs ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ≠ q → j ≠ 12 → t.ptrs j=s.ptrs j) := by
  let u := Op.act ω s (.pset 12 1)
  have hu : Eval ω (.atom (.pset 12 1)) s u 1 := Eval.atom s _
  have hub : u.ptrs 12+(n : ℤ)=u.ptrs b+1 := by simp [u,Op.act,hn,hb,add_comm]
  obtain ⟨t,he,htq⟩ := advance_loop_correct ω q b n hq hb hbq u hub
  have hall : Eval ω (advanceCommand q b) s t (3+4*n) := by convert! Eval.seq hu he using 1 <;> omega
  have hc := hall.cursors_preserved (by simp [advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.samples,Op.samples])
  refine ⟨t,hall,?_,hall.memory_preserved (by simp [advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.stores,Op.stores]),?_,hc.1,hc.2,?_⟩
  · simpa [u,Op.act,hq] using htq
  · funext r
    exact hall.register_preserved (by simp [advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.registers,Op.registers])
  · intro j hjq hj12
    apply hall.pointer_preserved
    simp [advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers,hjq,hj12]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMInputEnd
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def inputEndInit : List Op := [.pcopy 9 7,.pset 16 1]
def inputEndTail : List Op := [.pinc 9,.pinc 16]
def inputEndBody : Cmd := .seq (advanceCommand 9 0) (.block inputEndTail)
def inputEndLoop : Cmd := .loop (.pointer 16 17) inputEndBody
def inputEndCommand : Cmd := .seq (.block inputEndInit) inputEndLoop
def InputEndInvariant (d N : ℕ) (A : ℤ) (r : ℕ) (s : Store) : Prop :=
  s.ptrs 0=d ∧ s.ptrs 17=N ∧ s.ptrs 16=(r : ℤ)+1 ∧ s.ptrs 9=A+(r : ℤ)*((d : ℤ)+1)
lemma input_end_command_correct (ω : PolySampIso.Streams) (d N : ℕ) (s : Store)
    (hd : s.ptrs 0=d) (hN : s.ptrs 17=N) :
    ∃ t k, k ≤ 4+N*(7+4*d) ∧ Eval ω inputEndCommand s t k ∧ t.ptrs 9=s.ptrs 7+(N : ℤ)*((d : ℤ)+1) ∧
      t.mem=s.mem ∧ t.regs=s.regs ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ q, q ∉ ({9,12,16} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω inputEndInit s
  have hu : Eval ω (.block inputEndInit) s u 2 := eval_block ω inputEndInit s
  let Inv := InputEndInvariant d N (s.ptrs 7)
  have hinit : Inv 0 u := by simp [Inv,InputEndInvariant,u,blockAct,inputEndInit,Op.act,hd,hN]
  have htrue (i : ℕ) (hi : i < N) (v : Store) (hv : Inv i v) : Test.holds v (.pointer 16 17) := by
    change v.ptrs 16 ≤ v.ptrs 17
    rw [hv.2.2.1,hv.2.1]
    omega
  have hfalse (v : Store) (hv : Inv N v) : ¬Test.holds v (.pointer 16 17) := by
    change ¬v.ptrs 16 ≤ v.ptrs 17
    rw [hv.2.2.1,hv.2.1]
    omega
  have hbody (i : ℕ) (hi : i < N) (v : Store) (hv : Inv i v) :
      ∃ w k, k ≤ 5+4*d ∧ Eval ω inputEndBody v w k ∧ Inv (i+1) w := by
    obtain ⟨a,ha,ha9,ham,har,hagc,haec,hptr⟩ := advance_command_correct ω 9 0 d (by omega) (by omega) (by omega) v hv.1
    let w := blockAct ω inputEndTail a
    have hw : Eval ω (.block inputEndTail) a w 2 := eval_block ω inputEndTail a
    have he : Eval ω inputEndBody v w (5+4*d) := by convert! Eval.seq ha hw using 1 <;> omega
    refine ⟨w,5+4*d,by omega,he,?_,?_,?_,?_⟩
    · simpa [w,blockAct,inputEndTail,Op.act,hptr 0 (by omega) (by omega)] using hv.1
    · simpa [w,blockAct,inputEndTail,Op.act,hptr 17 (by omega) (by omega)] using hv.2.1
    · simp [w,blockAct,inputEndTail,Op.act,hptr 16 (by omega) (by omega),hv.2.2.1,Nat.cast_add]
    · simp [w,blockAct,inputEndTail,Op.act,ha9,hv.2.2.2,Nat.cast_add]
      ring
  obtain ⟨t,k,hk,he,ht⟩ := eval_loop_invariant ω (.pointer 16 17) inputEndBody N (5+4*d) Inv htrue hfalse hbody u hinit
  have hall : Eval ω inputEndCommand s t (2+k) := Eval.seq hu he
  have hcg := hall.cursors_preserved (by simp [inputEndCommand,inputEndInit,inputEndLoop,inputEndBody,inputEndTail,
    advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.samples,Op.samples])
  refine ⟨t,2+k,by nlinarith only [hk],hall,ht.2.2.2,?_,?_,hcg.1,hcg.2,?_⟩
  · exact hall.memory_preserved (by simp [inputEndCommand,inputEndInit,inputEndLoop,inputEndBody,inputEndTail,
      advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.stores,Op.stores])
  · funext r
    exact hall.register_preserved (by simp [inputEndCommand,inputEndInit,inputEndLoop,inputEndBody,inputEndTail,
      advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.registers,Op.registers])
  · intro q hq
    apply hall.pointer_preserved
    simp [inputEndCommand,inputEndInit,inputEndLoop,inputEndBody,inputEndTail,
      advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMArrays
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
noncomputable def writeArray (mem : ℤ → ℝ) (base : ℤ) : List ℝ → ℤ → ℝ
  | [] => mem
  | x::xs => Function.update (writeArray mem (base+1) xs) base x
noncomputable def readArray (mem : ℤ → ℝ) (base : ℤ) (n : ℕ) : List ℝ :=
  List.ofFn (fun i : Fin n => mem (base+i.val))
@[simp] lemma writeArray_nil (mem : ℤ → ℝ) (base : ℤ) : writeArray mem base []=mem := rfl
lemma writeArray_at (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ) (i : ℕ) (hi : i < xs.length) :
    writeArray mem base xs (base+i)=xs[i] := by
  induction xs generalizing base i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [writeArray]
    | succ i =>
      have hne : base+(i+1 : ℕ) ≠ base := by omega
      rw [writeArray,Function.update_of_ne hne]
      have he : base+((i+1 : ℕ) : ℤ)=(base+1)+(i : ℤ) := by push_cast; ring
      rw [he,ih (base+1) i (by simpa using hi)]
      rfl
lemma writeArray_outside (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ) (z : ℤ)
    (hz : z < base ∨ base+(xs.length : ℤ) ≤ z) : writeArray mem base xs z=mem z := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih =>
    have hne : z ≠ base := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hz; omega
    rw [writeArray,Function.update_of_ne hne]
    apply ih
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hz
    omega
@[simp] lemma readArray_writeArray (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ) :
    readArray (writeArray mem base xs) base xs.length=xs := by
  apply List.ext_getElem
  · simp [readArray]
  · intro i hi hj
    simp only [readArray,List.getElem_ofFn]
    exact writeArray_at mem base xs i hj
lemma writeArray_congr_inside (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ)
    (h : ∀ i (hi : i < xs.length), mem (base+i)=xs[i]'hi) : writeArray mem base xs=mem := by
  funext z
  by_cases hz : base ≤ z ∧ z < base+(xs.length : ℤ)
  · have hi : (z-base).toNat < xs.length := by omega
    have he : base+((z-base).toNat : ℤ)=z := by omega
    rw [← he,writeArray_at mem base xs _ hi,h _ hi]
  · apply writeArray_outside
    omega
lemma writeArray_update_before (mem : ℤ → ℝ) (base z : ℤ) (xs : List ℝ) (a : ℝ) (hz : z < base) :
    writeArray (Function.update mem z a) base xs=Function.update (writeArray mem base xs) z a := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih =>
    rw [writeArray,ih (base+1) (by omega),writeArray]
    exact Function.update_comm (by omega : z ≠ base) a x (writeArray mem (base+1) xs)
lemma writeArray_cons_sequential (mem : ℤ → ℝ) (base : ℤ) (a : ℝ) (xs : List ℝ) :
    writeArray (Function.update mem base a) (base+1) xs=writeArray mem base (a::xs) := by
  rw [writeArray_update_before mem (base+1) base xs a (by omega)]
  rfl
lemma readArray_cons (mem : ℤ → ℝ) (base : ℤ) (n : ℕ) :
    readArray mem base (n+1)=mem base::readArray mem (base+1) n := by
  simp only [readArray,List.ofFn_succ,Fin.val_zero,Nat.cast_zero,add_zero,Fin.val_succ,Nat.cast_add,Nat.cast_one]
  congr 2
  funext i
  congr 1
  ring
lemma readArray_update_before (mem : ℤ → ℝ) (base z : ℤ) (n : ℕ) (a : ℝ) (hz : z < base) :
    readArray (Function.update mem z a) base n=readArray mem base n := by
  apply List.ext_getElem
  · simp [readArray]
  · intro i hi hj
    simp only [readArray,List.getElem_ofFn]
    apply Function.update_of_ne
    omega
lemma readArray_eq_iff (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ) :
    readArray mem base xs.length=xs ↔ ∀ i (hi : i < xs.length), mem (base+i)=xs[i]'hi := by
  constructor
  · intro h i hi
    have hh := congrArg (fun v : List ℝ => v[i]?) h
    simpa [readArray,hi] using hh
  · intro h
    apply List.ext_getElem
    · simp [readArray]
    · intro i hi hj
      simpa only [readArray,List.getElem_ofFn] using h i hj
lemma readArray_write_after (mem : ℤ → ℝ) (a b : ℤ) (n : ℕ) (ys : List ℝ) (h : a+(n : ℤ) ≤ b) :
    readArray (writeArray mem b ys) a n=readArray mem a n := by
  apply List.ext_getElem
  · simp [readArray]
  · intro i hi hj
    simp only [readArray,List.getElem_ofFn]
    apply writeArray_outside
    left
    have hi' : i < n := by simpa [readArray] using hi
    omega
lemma readArray_write_before (mem : ℤ → ℝ) (a b : ℤ) (n : ℕ) (xs : List ℝ) (h : a+(xs.length : ℤ) ≤ b) :
    readArray (writeArray mem a xs) b n=readArray mem b n := by
  apply List.ext_getElem
  · simp [readArray]
  · intro i hi hj
    simp only [readArray,List.getElem_ofFn]
    apply writeArray_outside
    right
    omega
lemma readArray_update_after (mem : ℤ → ℝ) (base z : ℤ) (n : ℕ) (a : ℝ) (hz : base+(n : ℤ) ≤ z) :
    readArray (Function.update mem z a) base n=readArray mem base n := by
  apply List.ext_getElem
  · simp [readArray]
  · intro i hi hj
    simp only [readArray,List.getElem_ofFn]
    apply Function.update_of_ne
    have hi' : i < n := by simpa [readArray] using hi
    omega
lemma writeArray_overwrite (mem : ℤ → ℝ) (base : ℤ) (xs ys : List ℝ) (hlen : xs.length=ys.length) :
    writeArray (writeArray mem base xs) base ys=writeArray mem base ys := by
  funext z
  by_cases hz : base ≤ z ∧ z < base+(ys.length : ℤ)
  · have hi : (z-base).toNat < ys.length := by omega
    have he : base+((z-base).toNat : ℤ)=z := by omega
    rw [← he,writeArray_at _ base ys _ hi,writeArray_at mem base ys _ hi]
  · rw [writeArray_outside _ base ys z (by omega),writeArray_outside mem base xs z (by omega),
      writeArray_outside mem base ys z (by omega)]
lemma readArray_append (mem : ℤ → ℝ) (base : ℤ) (n m : ℕ) :
    readArray mem base (n+m)=readArray mem base n++readArray mem (base+(n : ℤ)) m := by
  simp [readArray,List.ofFn_add,Nat.cast_add,add_assoc]
@[simp] lemma readArray_write_ofFn (mem : ℤ → ℝ) (base : ℤ) {D : ℕ} (f : Fin D → ℝ) :
    readArray (writeArray mem base (List.ofFn f)) base D=List.ofFn f := by
  simpa only [List.length_ofFn] using readArray_writeArray mem base (List.ofFn f)
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMFillArray
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def fillStep : List Op := [.store 5 32,.pinc 5,.pinc 12]
def fillLoop : Cmd := .loop (.pointer 12 15) (.block fillStep)
def fillCommand : Cmd := .seq (.atom (.pset 12 1)) fillLoop
lemma fill_loop_correct (ω : PolySampIso.Streams) (n : ℕ) (s : Store)
    (hbound : s.ptrs 12+(n : ℤ)=s.ptrs 15+1) :
    ∃ t, Eval ω fillLoop s t (2+5*n) ∧
      t.mem=writeArray s.mem (s.ptrs 5) (List.replicate n (s.regs 32)) ∧
      t.ptrs 5=s.ptrs 5+n ∧ t.regs 32=s.regs 32 := by
  induction n generalizing s with
  | zero =>
    refine ⟨s,Eval.loop_done ?_,rfl,by simp,rfl⟩
    change ¬s.ptrs 12 ≤ s.ptrs 15
    simp only [Nat.cast_zero,add_zero] at hbound
    omega
  | succ n ih =>
    have hhead : Test.holds s (.pointer 12 15) := by
      change s.ptrs 12 ≤ s.ptrs 15
      push_cast at hbound
      omega
    let u := blockAct ω fillStep s
    have hu : Eval ω (.block fillStep) s u 3 := eval_block ω fillStep s
    have humem : u.mem=Function.update s.mem (s.ptrs 5) (s.regs 32) := rfl
    have huptr : u.ptrs=Function.update (Function.update s.ptrs 5 (s.ptrs 5+1)) 12 (s.ptrs 12+1) := by
      simp [u,blockAct,fillStep,Op.act]
    have hub : u.ptrs 12+(n : ℤ)=u.ptrs 15+1 := by
      simp only [huptr,Function.update_apply]
      norm_num
      push_cast at hbound
      omega
    obtain ⟨t,he,hm,h5,h32⟩ := ih u hub
    have hall := Eval.loop_step hhead hu he
    refine ⟨t,?_,?_,?_,h32⟩
    · convert! hall using 1 <;> omega
    · rw [hm,humem,huptr]
      norm_num
      rw [writeArray_cons_sequential]
      rfl
    · rw [h5,huptr]
      norm_num
      push_cast
      ring
lemma fill_command_correct (ω : PolySampIso.Streams) (n : ℕ) (s : Store) (hn : s.ptrs 15=n) :
    ∃ t, Eval ω fillCommand s t (3+5*n) ∧
      t.mem=writeArray s.mem (s.ptrs 5) (List.replicate n (s.regs 32)) ∧
      t.ptrs 5=s.ptrs 5+n ∧ t.regs=s.regs ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ q, q ≠ 5 → q ≠ 12 → t.ptrs q=s.ptrs q) := by
  let u := Op.act ω s (.pset 12 1)
  have hu : Eval ω (.atom (.pset 12 1)) s u 1 := Eval.atom s _
  have hub : u.ptrs 12+(n : ℤ)=u.ptrs 15+1 := by simp [u,Op.act,hn,add_comm]
  obtain ⟨t,he,hm,h5,h32⟩ := fill_loop_correct ω n u hub
  have hall : Eval ω fillCommand s t (3+5*n) := by convert! Eval.seq hu he using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,?_,?_,?_,hc.1,hc.2,?_⟩
  · simpa [u,Op.act] using hm
  · simpa [u,Op.act] using h5
  · funext r
    apply hall.register_preserved
    simp [fillCommand,fillLoop,fillStep,Cmd.block,Cmd.registers,Op.registers]
  · intro q hq5 hq12
    apply hall.pointer_preserved
    simp [fillCommand,fillLoop,fillStep,Cmd.block,Cmd.pointers,Op.pointers,hq5,hq12]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMWorkspace
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def workspacePrefix : List Op := [.pcopy 5 9,.pcopy 15 0,.literal 32 0]
def workspaceCommand : Cmd := .seq inputEndCommand (.seq (.block workspacePrefix)
  (.seq fillCommand (.atom (.pcopy 13 5))))
lemma workspace_command_correct (ω : PolySampIso.Streams) (d N : ℕ) (s : Store)
    (hd : s.ptrs 0=d) (hN : s.ptrs 17=N) :
    let B := s.ptrs 7+(N : ℤ)*((d : ℤ)+1)
    ∃ t k, k ≤ 11+5*d+N*(7+4*d) ∧ Eval ω workspaceCommand s t k ∧
      t.mem=writeArray s.mem B (List.replicate d 0) ∧
      t.ptrs 9=B ∧ t.ptrs 13=B+d ∧ t.ptrs 15=d ∧ t.regs 32=0 ∧
      (∀ r, r ≠ 32 → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({5,9,12,13,15,16} : Finset ℕ) → t.ptrs q=s.ptrs q) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  dsimp only
  let B := s.ptrs 7+(N : ℤ)*((d : ℤ)+1)
  obtain ⟨u,k,hk,hu,hu9,hum,hur,hugc,huec,huptr⟩ := input_end_command_correct ω d N s hd hN
  let v := blockAct ω workspacePrefix u
  have hv : Eval ω (.block workspacePrefix) u v 3 := eval_block ω workspacePrefix u
  have hv15 : v.ptrs 15=d := by
    simp [v,blockAct,workspacePrefix,Op.act,huptr 0 (by simp),hd]
  have hv5 : v.ptrs 5=B := by simp [v,blockAct,workspacePrefix,Op.act,hu9,B]
  have hv32 : v.regs 32=0 := by simp [v,blockAct,workspacePrefix,Op.act]
  obtain ⟨w,hw,hm,h5,hwreg,hwgc,hwec,hwptr⟩ := fill_command_correct ω d v hv15
  let t := Op.act ω w (.pcopy 13 5)
  have ht : Eval ω (.atom (.pcopy 13 5)) w t 1 := Eval.atom w _
  have hall : Eval ω workspaceCommand s t (k+(3+((3+5*d)+1))) := Eval.seq hu (Eval.seq hv (Eval.seq hw ht))
  have hcg := hall.cursors_preserved (by decide)
  refine ⟨t,k+(3+((3+5*d)+1)),by omega,hall,?_,?_,?_,?_,?_,?_,?_,hcg.1,hcg.2⟩
  · change w.mem=_
    rw [hm,hv5,hv32]
    exact congrArg (fun m => writeArray m B (List.replicate d 0)) hum
  · change w.ptrs 9=B
    rw [hwptr 9 (by omega) (by omega)]
    simpa [v,blockAct,workspacePrefix,Op.act,B] using hu9
  · change w.ptrs 5=B+d
    rw [h5,hv5]
  · change w.ptrs 15=(d : ℤ)
    rw [hwptr 15 (by omega) (by omega),hv15]
  · change w.regs 32=0
    rw [hwreg,hv32]
  · intro r hr
    apply hall.register_preserved
    simp [workspaceCommand,workspacePrefix,inputEndCommand,inputEndInit,inputEndLoop,inputEndBody,inputEndTail,
      advanceCommand,advanceLoop,advanceStep,fillCommand,fillLoop,fillStep,Cmd.block,Cmd.registers,Op.registers,hr]
  · intro q hq
    apply hall.pointer_preserved
    simp [workspaceCommand,workspacePrefix,inputEndCommand,inputEndInit,inputEndLoop,inputEndBody,inputEndTail,
      advanceCommand,advanceLoop,advanceStep,fillCommand,fillLoop,fillStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMInputLayout
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
noncomputable def sampleCell (d N : ℕ) (S : Fin N → Example d) (i : ℕ) : ℝ :=
  if h : i/(d+1)<N then
    if hc : i%(d+1)<d then (S ⟨i/(d+1),h⟩).1 ⟨i%(d+1),hc⟩ else label (S ⟨i/(d+1),h⟩).2
  else 0
lemma sampleCell_row (d N : ℕ) (S : Fin N → Example d) (j : Fin N) (i : Fin (d+1)) :
    sampleCell d N S (j.val*(d+1)+i.val)=
      if hi : i.val<d then (S j).1 ⟨i.val,hi⟩ else label (S j).2 := by
  have hd : 0 < d+1 := by omega
  have hdiv : (j.val*(d+1)+i.val)/(d+1)=j.val := by
    rw [Nat.mul_comm j.val (d+1),Nat.mul_add_div hd,Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  have hmod : (j.val*(d+1)+i.val)%(d+1)=i.val := by
    rw [Nat.mul_comm j.val (d+1),Nat.mul_add_mod,Nat.mod_eq_of_lt i.isLt]
  simp only [sampleCell,hdiv,hmod,dif_pos j.isLt]
lemma learnerInput_sample (d p k M n₀ m : ℕ) (ε δ α β : ℝ)
    (S : Fin (k*n₀+m) → Example d) (i : ℕ) :
    learnerInput d p k M n₀ m ε δ α β S (11+i)=sampleCell d (k*n₀+m) S i := by
  unfold learnerInput sampleCell
  rw [dif_neg (by omega)]
  simp only [Nat.add_sub_cancel_left]
def InputRows (d N : ℕ) (S : Fin N → Example d) (input : ℕ → ℝ) : Prop :=
  ∀ (j : Fin N) (i : Fin (d+1)), input (11+j.val*(d+1)+i.val)=
    if hi : i.val<d then (S j).1 ⟨i.val,hi⟩ else label (S j).2
lemma learnerInput_rows (d p k M n₀ m : ℕ) (ε δ α β : ℝ) (S : Fin (k*n₀+m) → Example d) :
    InputRows d (k*n₀+m) S (learnerInput d p k M n₀ m ε δ α β S) := by
  intro j i
  rw [show 11+j.val*(d+1)+i.val=11+(j.val*(d+1)+i.val) by omega,learnerInput_sample,sampleCell_row]
lemma initialStore_nat_cell (d p M : ℕ) (input : ℕ → ℝ) (i : ℕ) :
    (initialStore d p M input).mem (i : ℤ)=input i := by simp [initialStore]
lemma initialStore_input_rows (d p M N : ℕ) (S : Fin N → Example d) (input : ℕ → ℝ) (h : InputRows d N S input) :
    (∀ j : Fin N, readArray (initialStore d p M input).mem (11+(j.val : ℤ)*((d : ℤ)+1)) d=
      List.ofFn (fun i => (S j).1 i)) ∧
    (∀ j : Fin N, (initialStore d p M input).mem (11+(j.val : ℤ)*((d : ℤ)+1)+(d : ℤ))=label (S j).2) := by
  constructor
  · intro j
    apply List.ext_getElem
    · simp [readArray]
    · intro i hi hj
      simp only [readArray,List.getElem_ofFn]
      have hi' : i < d := by simpa using hj
      have he : (11 : ℤ)+(j.val : ℤ)*((d : ℤ)+1)+(i : ℤ)=((11+j.val*(d+1)+i : ℕ) : ℤ) := by push_cast; ring
      rw [he,initialStore_nat_cell,h j ⟨i,by omega⟩,dif_pos hi']
  · intro j
    have he : (11 : ℤ)+(j.val : ℤ)*((d : ℤ)+1)+(d : ℤ)=((11+j.val*(d+1)+d : ℕ) : ℤ) := by push_cast; ring
    rw [he,initialStore_nat_cell,h j ⟨d,by omega⟩,dif_neg (by simp)]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPrepareWorkspace
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def prepareWorkspaceCommand : Cmd := .seq (.atom (.pset 7 11)) (.seq (headerNaturalCommand 17 10) workspaceCommand)
lemma prepare_workspace_correct (ω : PolySampIso.Streams) (d p M N : ℕ) (input : ℕ → ℝ) (hN : input 10=N) :
    let s := initialStore d p M input
    let B : ℤ := 11+(N : ℤ)*((d : ℤ)+1)
    ∃ t k, k ≤ 21+5*d+N*(13+4*d) ∧ Eval ω prepareWorkspaceCommand s t k ∧
      t.mem=writeArray s.mem B (List.replicate d 0) ∧
      t.ptrs 0=d ∧ t.ptrs 7=11 ∧ t.ptrs 9=B ∧ t.ptrs 13=B+d ∧ t.ptrs 15=d ∧ t.ptrs 17=N ∧
      t.regs 32=0 ∧ (∀ r, r ∉ ({32,40,41,43,44} : Finset ℕ) → t.regs r=0) ∧
      (∀ q, q ∉ ({5,7,9,12,13,15,16,17,30} : Finset ℕ) → t.ptrs q=s.ptrs q) ∧ t.gc=0 ∧ t.ec=0 := by
  dsimp only
  let s := initialStore d p M input
  let u := Op.act ω s (.pset 7 11)
  have hu : Eval ω (.atom (.pset 7 11)) s u 1 := Eval.atom s _
  have hu10 : u.mem (10 : ℤ)=N := by simpa [u,s,Op.act,initialStore] using hN
  obtain ⟨v,hv,hv17,hvm,hvgc,hvec,hvreg,hvptr⟩ := header_natural_command_correct ω 17 10 N u hu10
  have hv7 : v.ptrs 7=11 := by rw [hvptr 7 (by omega) (by omega)]; simp [u,Op.act]
  have hv0 : v.ptrs 0=d := by rw [hvptr 0 (by omega) (by omega)]; simp [u,s,Op.act,initialStore]
  obtain ⟨t,k,hk,ht,hm,h9,h13,h15,h32,hreg,hptr,hgc,hec⟩ := workspace_command_correct ω d N v hv0 hv17
  have hall : Eval ω prepareWorkspaceCommand s t (1+((9+6*N)+k)) := Eval.seq hu (Eval.seq hv ht)
  have hcg := hall.cursors_preserved (by decide)
  refine ⟨t,1+((9+6*N)+k),by nlinarith only [hk],hall,?_,?_,?_,?_,?_,h15,?_,h32,?_,?_,hcg.1,hcg.2⟩
  · simpa only [hv7,hvm,u,Op.act,s] using hm
  · rw [hptr 0 (by simp)]
    exact hv0
  · rw [hptr 7 (by simp)]
    exact hv7
  · simpa only [hv7] using h9
  · simpa only [hv7] using h13
  · rw [hptr 17 (by simp)]
    exact hv17
  · intro r hr
    have he := hall.register_preserved (r := r) (by
      simp [prepareWorkspaceCommand,headerNaturalCommand,headerPrefix,naturalCommand,naturalLoop,naturalInit,naturalStep,
        workspaceCommand,workspacePrefix,inputEndCommand,inputEndInit,inputEndLoop,inputEndBody,inputEndTail,
        advanceCommand,advanceLoop,advanceStep,fillCommand,fillLoop,fillStep,Cmd.block,Cmd.registers,Op.registers]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
      tauto)
    exact he
  · intro q hq
    apply hall.pointer_preserved
    simp [prepareWorkspaceCommand,headerNaturalCommand,headerPrefix,naturalCommand,naturalLoop,naturalInit,naturalStep,
      workspaceCommand,workspacePrefix,inputEndCommand,inputEndInit,inputEndLoop,inputEndBody,inputEndTail,
      advanceCommand,advanceLoop,advanceStep,fillCommand,fillLoop,fillStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.DenseIndexEnumeration
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
namespace DenseEnumeration
def valid (p : ℕ) (v : List ℕ) : Prop := v.sum ≤ p
def next (p : ℕ) : List ℕ → Option (List ℕ)
  | [] => none
  | a::v => if a+v.sum < p then some ((a+1)::v) else (next p v).map (0::·)
lemma digit_bound {p a : ℕ} {v : List ℕ} (h : valid p v) (ha : a ∈ v) : a ≤ p :=
  (List.le_sum_of_mem ha).trans h
lemma code_injective {p : ℕ} {v w : List ℕ} (hv : valid p v) (hw : valid p w)
    (hlen : v.length = w.length) (he : Nat.ofDigits (p+1) v = Nat.ofDigits (p+1) w) : v = w := by
  by_cases hp : p = 0
  · subst p
    have hz (x : List ℕ) (hx : valid 0 x) : x = List.replicate x.length 0 := by
      apply List.eq_replicate_length.mpr
      intro a ha
      exact Nat.eq_zero_of_le_zero (digit_bound hx ha)
    rw [hz v hv,hz w hw,hlen]
  · exact Nat.ofDigits_inj_of_len_eq (by omega) hlen
      (fun a ha => by have := digit_bound hv ha; omega)
      (fun a ha => by have := digit_bound hw ha; omega) he
lemma tail_code_strict {p a b : ℕ} {v w : List ℕ}
    (hv : valid p (a::v)) (hw : valid p (b::w)) (hs : a+v.sum=p)
    (hlen : v.length = w.length)
    (hcode : Nat.ofDigits (p+1) (a::v) < Nat.ofDigits (p+1) (b::w)) :
    Nat.ofDigits (p+1) v < Nat.ofDigits (p+1) w := by
  have hb : b ≤ p := digit_bound hw (by simp)
  have hva : valid p v := by unfold valid at *; simp only [List.sum_cons] at *; omega
  have hwa : valid p w := by unfold valid at *; simp only [List.sum_cons] at *; omega
  simp only [Nat.ofDigits_cons] at hcode
  by_contra hn
  have hle : Nat.ofDigits (p+1) w ≤ Nat.ofDigits (p+1) v := by omega
  rcases hle.eq_or_lt with he|he
  · have hvw := code_injective hva hwa hlen he.symm
    subst w
    have hh := hw
    unfold valid at hh
    simp only [List.sum_cons] at hh
    omega
  · nlinarith
lemma next_spec (p : ℕ) (v : List ℕ) (hv : valid p v) :
    match next p v with
    | none => ∀ w : List ℕ, valid p w → w.length=v.length → Nat.ofDigits (p+1) w ≤ Nat.ofDigits (p+1) v
    | some z => valid p z ∧ z.length=v.length ∧ Nat.ofDigits (p+1) v < Nat.ofDigits (p+1) z ∧
        ∀ w : List ℕ, valid p w → w.length=v.length → Nat.ofDigits (p+1) v < Nat.ofDigits (p+1) w →
          Nat.ofDigits (p+1) z ≤ Nat.ofDigits (p+1) w := by
  induction v with
  | nil => simp only [next,List.length_nil,List.length_eq_zero_iff]; intro w hw he; subst w; rfl
  | cons a v ih =>
    have ha : a ≤ p := digit_bound hv (by simp)
    have hv' : valid p v := by unfold valid at *; simp only [List.sum_cons] at *; omega
    have ih := ih hv'
    simp only [next]
    split_ifs with hsum
    · refine ⟨by unfold valid; simp; omega,by simp,?_,?_⟩
      · simp only [Nat.ofDigits_cons]; omega
      · intro w hw hl hcode
        simp only [Nat.ofDigits_cons] at *
        omega
    · have hs : a+v.sum=p := by have := hv; unfold valid at this; simp at this; omega
      cases he : next p v with
      | none =>
        simp only [he,Option.map_none] at ih ⊢
        intro w hw hl
        cases w with
        | nil => simp at hl
        | cons b w =>
          by_contra hh
          have hc : Nat.ofDigits (p+1) (a::v) < Nat.ofDigits (p+1) (b::w) := by omega
          have ht := tail_code_strict hv hw hs (by simpa using hl.symm) hc
          have hw' : valid p w := by unfold valid at *; simp only [List.sum_cons] at *; omega
          have hb := ih w hw' (by simpa using hl)
          omega
      | some z =>
        simp only [he,Option.map_some] at ih ⊢
        obtain ⟨hz,hlen,hgt,hmin⟩ := ih
        refine ⟨by simpa [valid] using hz,by simp [hlen],?_,?_⟩
        · simp only [Nat.ofDigits_cons]
          nlinarith
        · intro w hw hl hc
          cases w with
          | nil => simp at hl
          | cons b w =>
            have ht := tail_code_strict hv hw hs (by simpa using hl.symm) hc
            have hw' : valid p w := by unfold valid at *; simp only [List.sum_cons] at *; omega
            have hle := hmin w hw' (by simpa using hl) ht
            simp only [Nat.ofDigits_cons]
            nlinarith
end DenseEnumeration
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.DenseIndexRank
open scoped BigOperators
open Finset
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
namespace DenseEnumeration
def digits {d p : ℕ} (κ : Index d p) : List ℕ := List.ofFn (fun i => (κ.val i).val)
@[simp] lemma digits_length {d p : ℕ} (κ : Index d p) : (digits κ).length=d := by simp [digits]
lemma digits_valid {d p : ℕ} (κ : Index d p) : valid p (digits κ) := by
  simpa [valid,digits,List.sum_ofFn] using κ.property
lemma digits_code {d p : ℕ} (κ : Index d p) : Nat.ofDigits (p+1) (digits κ)=indexCode κ :=
  ofDigits_ofFn_sum (p+1) d _
lemma exists_index_of_list {d p : ℕ} (v : List ℕ) (hlen : v.length=d) (hv : valid p v) :
    ∃ κ : Index d p, digits κ=v := by
  subst d
  let κ : Fin v.length → Fin (p+1) := fun i => ⟨v.get i,by
    have h := digit_bound hv (List.get_mem v i)
    omega⟩
  have hd : List.ofFn (fun i => (κ i).val)=v := by simpa only [κ] using List.ofFn_get v
  have hs : (∑ i, (κ i).val) ≤ p := by
    rw [← List.sum_ofFn,hd]
    exact hv
  exact ⟨⟨κ,hs⟩,hd⟩
lemma rank_successor {d p : ℕ} (κ ξ : Index d p) (hn : next p (digits κ)=some (digits ξ)) :
    indexRank ξ=indexRank κ+1 := by
  classical
  have hs := next_spec p (digits κ) (digits_valid κ)
  simp only [hn] at hs
  have hlt : indexCode κ < indexCode ξ := by simpa only [digits_code] using hs.2.2.1
  have hmin (η : Index d p) (hη : indexCode κ < indexCode η) : indexCode ξ ≤ indexCode η := by
    have hh := hs.2.2.2 (digits η) (digits_valid η) (by simp) (by simpa only [digits_code] using hη)
    simpa only [digits_code] using hh
  have hfilter : (univ.filter (fun η : Index d p => indexCode η < indexCode ξ)) =
      insert κ (univ.filter (fun η : Index d p => indexCode η < indexCode κ)) := by
    ext η
    simp only [mem_filter,mem_univ,true_and,mem_insert]
    constructor
    · intro hη
      rcases lt_trichotomy (indexCode η) (indexCode κ) with h|h|h
      · exact Or.inr h
      · exact Or.inl (indexCode_injective d p h)
      · have hh := hmin η h
        omega
    · rintro (rfl|hη)
      · exact hlt
      · exact hη.trans hlt
  unfold indexRank
  rw [hfilter,card_insert_of_notMem (by simp)]
lemma rank_terminal {d p : ℕ} (κ : Index d p) (hn : next p (digits κ)=none) :
    indexRank κ+1=featureDimension d p := by
  classical
  have hs := next_spec p (digits κ) (digits_valid κ)
  simp only [hn] at hs
  have hmax (η : Index d p) : indexCode η ≤ indexCode κ := by
    have hh := hs (digits η) (digits_valid η) (by simp)
    simpa only [digits_code] using hh
  have he : insert κ (univ.filter (fun η : Index d p => indexCode η < indexCode κ))=univ := by
    ext η
    simp only [mem_insert,mem_filter,mem_univ,true_and,iff_true]
    rcases (hmax η).lt_or_eq with h|h
    · exact Or.inr h
    · exact Or.inl (indexCode_injective d p h)
  have hh := congrArg Finset.card he
  rw [card_insert_of_notMem (by simp)] at hh
  simpa only [← ((lemma_B_8 d).2.2.2 p).2.1,indexRank,Finset.card_univ] using hh
lemma next_rank_index {d p : ℕ} (κ : Index d p) (h : indexRank κ+1 < featureDimension d p) :
    next p (digits κ)=some (digits ((coefficientIndexEquiv d p).symm ⟨indexRank κ+1,h⟩)) := by
  cases hn : next p (digits κ) with
  | none => have hh := rank_terminal κ hn; omega
  | some z =>
    have hs := next_spec p (digits κ) (digits_valid κ)
    simp only [hn] at hs
    obtain ⟨ξ,hξ⟩ := exists_index_of_list z (by simpa using hs.2.1) hs.1
    rw [← hξ] at hn
    have hr := rank_successor κ ξ hn
    have he : ξ=(coefficientIndexEquiv d p).symm ⟨indexRank κ+1,h⟩ := by
      apply (coefficientIndexEquiv d p).injective
      simp only [Equiv.apply_symm_apply]
      exact Fin.ext hr
    exact congrArg some (hξ.symm.trans (congrArg digits he))
end DenseEnumeration
end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian.DenseEnumeration
noncomputable def zeroIndex (d p : ℕ) : Index d p := ⟨fun _ => 0,by simp⟩
@[simp] lemma zeroIndex_rank (d p : ℕ) : indexRank (zeroIndex d p)=0 := by
  simp [indexRank,indexCode,zeroIndex]
@[simp] lemma zeroIndex_digits (d p : ℕ) : digits (zeroIndex d p)=List.replicate d 0 := by
  simp [digits,zeroIndex,List.ofFn_const]
lemma rank_inverse_val {d p : ℕ} (i : Fin (featureDimension d p)) :
    indexRank ((coefficientIndexEquiv d p).symm i)=i.val :=
  congrArg Fin.val ((coefficientIndexEquiv d p).apply_symm_apply i)
lemma next_terminal {d p : ℕ} (κ : Index d p) (h : indexRank κ+1=featureDimension d p) : next p (digits κ)=none := by
  cases hn : next p (digits κ) with
  | none => rfl
  | some z =>
    have hs := next_spec p (digits κ) (digits_valid κ)
    simp only [hn] at hs
    obtain ⟨ξ,hξ⟩ := exists_index_of_list z (by simpa using hs.2.1) hs.1
    rw [← hξ] at hn
    have hr := rank_successor κ ξ hn
    have hl := indexRank_lt d p ξ
    omega
end PrivateAgnosticHalfspace.Gaussian.DenseEnumeration
end

section
-- Solutions.RAMIndexSuccessor
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
def indexSuccessorPrefix : List Op := [.add 23 20 25,.sub 23 23 21,.load 24 10]
def indexSuccessorYes : List Op := [.add 24 24 25,.store 10 24,.add 20 20 25,
  .literal 22 1,.pcopy 11 0,.pinc 11]
def indexSuccessorNo : List Op := [.store 10 26,.sub 20 20 24,.pinc 10,.pinc 11]
def indexSuccessorBody : Cmd := .seq (.block indexSuccessorPrefix)
  (.cond (.real 23) (.block indexSuccessorYes) (.block indexSuccessorNo))
def indexSuccessorLoop : Cmd := .loop (.pointer 11 0) indexSuccessorBody
def successorDigits (p : ℕ) (v : List ℕ) : List ℕ := (next p v).getD (List.replicate v.length 0)
lemma successorDigits_nil (p : ℕ) : successorDigits p []=[] := rfl
lemma successorDigits_cons_yes {p a : ℕ} {v : List ℕ} (h : a+v.sum<p) :
    successorDigits p (a::v)=(a+1)::v := by simp [successorDigits,next,h]
lemma successorDigits_cons_no {p a : ℕ} {v : List ℕ} (h : ¬a+v.sum<p) :
    successorDigits p (a::v)=0::successorDigits p v := by
  unfold successorDigits
  simp only [next,if_neg h]
  cases next p v <;> simp [List.replicate_succ]
structure IndexLoopInvariant (p : ℕ) (v : List ℕ) (s : Store) : Prop where
  bound : s.ptrs 11+(v.length : ℤ)=s.ptrs 0+1
  array : readArray s.mem (s.ptrs 10) v.length=v.map (fun a : ℕ => (a : ℝ))
  total : s.regs 20=(v.sum : ℝ)
  budget : s.regs 21=p
  flag : s.regs 22=0
  one : s.regs 25=1
  zero : s.regs 26=0
lemma index_successor_loop (ω : PolySampIso.Streams) (p : ℕ) (v : List ℕ) (hv : valid p v)
    (s : Store) (hs : IndexLoopInvariant p v s) :
    ∃ t k, k ≤ 14+11*v.length ∧ Eval ω indexSuccessorLoop s t k ∧
      t.mem=writeArray s.mem (s.ptrs 10) ((successorDigits p v).map (fun a : ℕ => (a : ℝ))) ∧
      t.regs 20=((successorDigits p v).sum : ℝ) ∧
      t.regs 22=(if (next p v).isSome then 1 else 0) ∧ t.ptrs 11=t.ptrs 0+1 := by
  induction v generalizing s with
  | nil =>
    refine ⟨s,2,by simp,Eval.loop_done ?_,?_,?_,?_,?_⟩
    · change ¬s.ptrs 11 ≤ s.ptrs 0
      have hh := hs.bound
      simp only [List.length_nil,Nat.cast_zero,add_zero] at hh
      omega
    · simp [successorDigits,next]
    · simpa only [successorDigits_nil,List.sum_nil,Nat.cast_zero] using hs.total
    · simpa [next] using hs.flag
    · simpa using hs.bound
  | cons a v ih =>
    have hv' : valid p v := by unfold valid at *; simp only [List.sum_cons] at *; omega
    have harray : s.mem (s.ptrs 10)=(a : ℝ) ∧
        readArray s.mem (s.ptrs 10+1) v.length=v.map (fun a : ℕ => (a : ℝ)) := by
      have h := hs.array
      rw [List.length_cons,readArray_cons,List.map_cons,List.cons.injEq] at h
      exact h
    have hhead : Test.holds s (.pointer 11 0) := by
      change s.ptrs 11 ≤ s.ptrs 0
      have h := hs.bound
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at h
      omega
    let u := blockAct ω indexSuccessorPrefix s
    have hu : Eval ω (.block indexSuccessorPrefix) s u 3 := eval_block ω indexSuccessorPrefix s
    have hpre : u.mem=s.mem ∧ u.ptrs=s.ptrs ∧ u.regs 20=s.regs 20 ∧ u.regs 21=s.regs 21 ∧
        u.regs 22=s.regs 22 ∧ u.regs 25=s.regs 25 ∧ u.regs 26=s.regs 26 ∧
        u.regs 23=(a+v.sum : ℕ)+1-p ∧ u.regs 24=a := by
      simp [u,blockAct,indexSuccessorPrefix,Op.act,hs.total,hs.one,hs.budget,harray.1,List.sum_cons,Nat.cast_add]
    by_cases hsum : a+v.sum<p
    · let t := blockAct ω indexSuccessorYes u
      have htest : Test.holds u (.real 23) := by
        change u.regs 23 ≤ 0
        rw [hpre.2.2.2.2.2.2.2.1]
        have hh : ((a+v.sum : ℕ) : ℝ)+1 ≤ p := by exact_mod_cast (show a+v.sum+1 ≤ p by omega)
        linarith
      have ht := eval_block ω indexSuccessorYes u
      have hfinished : ¬Test.holds t (.pointer 11 0) := by
        simp [t,blockAct,indexSuccessorYes,Op.act,Test.holds]
      have he := Eval.loop_step hhead (Eval.seq hu (Eval.cond_yes (no := .block indexSuccessorNo) htest ht)) (Eval.loop_done hfinished)
      refine ⟨t,14,by simp,he,?_,?_,?_,?_⟩
      · have hvArray : writeArray s.mem (s.ptrs 10+1) (v.map (fun a : ℕ => (a : ℝ)))=s.mem :=
          writeArray_congr_inside _ _ _ ((readArray_eq_iff _ _ _).mp (by simpa using harray.2))
        simp only [successorDigits_cons_yes hsum,List.map_cons,writeArray,hvArray]
        simp [t,blockAct,indexSuccessorYes,Op.act,hpre.1,hpre.2.1,hpre.2.2.2.2.2.2.2.2,hpre.2.2.2.2.2.1,hs.one]
      · rw [successorDigits_cons_yes hsum]
        simp [t,blockAct,indexSuccessorYes,Op.act,hpre.2.2.1,hpre.2.2.2.2.2.1,hs.total,hs.one,List.sum_cons,Nat.cast_add]
        <;> ring
      · simp [t,blockAct,indexSuccessorYes,Op.act,next,hsum]
      · simp [t,blockAct,indexSuccessorYes,Op.act]
    · let t₀ := blockAct ω indexSuccessorNo u
      have hsumEq : a+v.sum=p := by have := hv; unfold valid at this; simp only [List.sum_cons] at this; omega
      have htest : ¬Test.holds u (.real 23) := by
        change ¬u.regs 23 ≤ 0
        rw [hpre.2.2.2.2.2.2.2.1,hsumEq]
        simp
      have ht : Eval ω (.block indexSuccessorNo) u t₀ 4 := eval_block ω indexSuccessorNo u
      have htmem : t₀.mem=Function.update s.mem (s.ptrs 10) 0 := by
        simp [t₀,blockAct,indexSuccessorNo,Op.act,hpre.1,hpre.2.1,hpre.2.2.2.2.2.2.1,hs.zero]
      have htptr : t₀.ptrs=Function.update (Function.update s.ptrs 10 (s.ptrs 10+1)) 11 (s.ptrs 11+1) := by
        simp [t₀,blockAct,indexSuccessorNo,Op.act,hpre.2.1]
      have hinv : IndexLoopInvariant p v t₀ := by
        constructor
        · simp [htptr]
          have hh := hs.bound
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hh
          omega
        · simp only [htmem,htptr,Function.update_apply]
          norm_num
          rw [readArray_update_before _ _ _ _ _ (by omega)]
          exact harray.2
        · simp [t₀,blockAct,indexSuccessorNo,Op.act,hpre.2.2.1,hpre.2.2.2.2.2.2.2.2,hs.total,List.sum_cons,Nat.cast_add]
        · simp [t₀,blockAct,indexSuccessorNo,Op.act,hpre.2.2.2.1,hs.budget]
        · simp [t₀,blockAct,indexSuccessorNo,Op.act,hpre.2.2.2.2.1,hs.flag]
        · simp [t₀,blockAct,indexSuccessorNo,Op.act,hpre.2.2.2.2.2.1,hs.one]
        · simp [t₀,blockAct,indexSuccessorNo,Op.act,hpre.2.2.2.2.2.2.1,hs.zero]
      obtain ⟨t,k,hk,he,hm,h20,h22,h11⟩ := ih hv' t₀ hinv
      have hbody := Eval.seq hu (Eval.cond_no (yes := .block indexSuccessorYes) htest ht)
      have hall := Eval.loop_step hhead hbody he
      refine ⟨t,11+k,?_,hall,?_,?_,?_,h11⟩
      · simp only [List.length_cons]
        omega
      · rw [hm,htmem,htptr]
        norm_num
        rw [successorDigits_cons_no hsum,List.map_cons,writeArray_cons_sequential]
        norm_num
      · simpa only [successorDigits_cons_no hsum,List.sum_cons,zero_add] using h20
      · simpa only [next,if_neg hsum,Option.isSome_map] using h22
end PrivateAgnosticHalfspace.Gaussian.RAM

namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
def indexSuccessorInit : List Op := [.pcopy 10 9,.pset 11 1,.literal 22 0,.literal 25 1,.literal 26 0]
def indexSuccessorCommand : Cmd := .seq (.block indexSuccessorInit) indexSuccessorLoop
lemma index_successor_command (ω : PolySampIso.Streams) (d p : ℕ) (v : List ℕ)
    (hv : valid p v) (hlen : v.length=d) (s : Store) (hd : s.ptrs 0=d)
    (harray : readArray s.mem (s.ptrs 9) d=v.map (fun a : ℕ => (a : ℝ)))
    (htotal : s.regs 20=(v.sum : ℝ)) (hbudget : s.regs 21=p) :
    ∃ t k, k ≤ 19+11*d ∧ Eval ω indexSuccessorCommand s t k ∧
      t.mem=writeArray s.mem (s.ptrs 9) ((successorDigits p v).map (fun a : ℕ => (a : ℝ))) ∧
      t.regs 20=((successorDigits p v).sum : ℝ) ∧
      t.regs 22=(if (next p v).isSome then 1 else 0) ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({20,22,23,24,25,26} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ≠ 10 → q ≠ 11 → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω indexSuccessorInit s
  have hu : Eval ω (.block indexSuccessorInit) s u 5 := eval_block ω indexSuccessorInit s
  have humem : u.mem=s.mem := rfl
  have hu10 : u.ptrs 10=s.ptrs 9 := by simp [u,blockAct,indexSuccessorInit,Op.act]
  have hinv : IndexLoopInvariant p v u := by
    constructor
    · simp [u,blockAct,indexSuccessorInit,Op.act,hd,hlen,add_comm]
    · simpa only [humem,hu10,hlen] using harray
    · simpa [u,blockAct,indexSuccessorInit,Op.act] using htotal
    · simpa [u,blockAct,indexSuccessorInit,Op.act] using hbudget
    · simp [u,blockAct,indexSuccessorInit,Op.act]
    · simp [u,blockAct,indexSuccessorInit,Op.act]
    · simp [u,blockAct,indexSuccessorInit,Op.act]
  obtain ⟨t,k,hk,he,hm,h20,h22,h11⟩ := index_successor_loop ω p v hv u hinv
  have hall : Eval ω indexSuccessorCommand s t (5+k) := Eval.seq hu he
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,5+k,by omega,hall,?_,h20,h22,hc.1,hc.2,?_,?_⟩
  · simpa only [humem,hu10] using hm
  · intro r hr
    apply hall.register_preserved
    simp [indexSuccessorCommand,indexSuccessorLoop,indexSuccessorBody,Cmd.block,Cmd.registers,
      indexSuccessorInit,indexSuccessorPrefix,indexSuccessorYes,indexSuccessorNo,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq10 hq11
    apply hall.pointer_preserved
    simp [indexSuccessorCommand,indexSuccessorLoop,indexSuccessorBody,Cmd.block,Cmd.pointers,
      indexSuccessorInit,indexSuccessorPrefix,indexSuccessorYes,indexSuccessorNo,Op.pointers,hq10,hq11]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMHermite
open MeasureTheory ProbabilityTheory Polynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma derivative_hermite_integer (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n+1)) = Polynomial.C ((n : ℤ)+1)*Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_zero]
  | succ n ih =>
    have key : Polynomial.derivative (Polynomial.hermite (n+1+1)) = Polynomial.hermite (n+1)+
        Polynomial.C ((n : ℤ)+1)*(Polynomial.X*Polynomial.hermite n-Polynomial.derivative (Polynomial.hermite n)) := by
      rw [Polynomial.hermite_succ (n+1),Polynomial.derivative_sub,Polynomial.derivative_mul,
        Polynomial.derivative_X,ih,Polynomial.derivative_C_mul]
      ring
    have hC : (Polynomial.C (((n : ℕ)+1 : ℕ)+1 : ℤ) : Polynomial ℤ) = Polynomial.C ((n : ℤ)+1)+1 := by
      push_cast
      rw [Polynomial.C_add,Polynomial.C_1]
    rw [key,←Polynomial.hermite_succ n,hC,add_mul,one_mul,add_comm]
noncomputable def hermiteValue (n : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval x
@[simp] lemma hermiteValue_zero (x : ℝ) : hermiteValue 0 x = 1 := by simp [hermiteValue,Polynomial.hermite_zero]
@[simp] lemma hermiteValue_one (x : ℝ) : hermiteValue 1 x = x := by simp [hermiteValue]
lemma hermiteValue_step (j : ℕ) (x : ℝ) :
    hermiteValue (j+1) x = x*hermiteValue j x-(j : ℝ)*(if j=0 then 0 else hermiteValue (j-1) x) := by
  cases j with
  | zero => simp
  | succ j =>
    unfold hermiteValue
    rw [Polynomial.hermite_succ (j+1),derivative_hermite_integer j]
    simp [Polynomial.map_sub,Polynomial.map_mul]
def hermiteInit : List Op := [.literal 2 1,.literal 3 0,.literal 4 1,.literal 5 0,
  .literal 9 1,.literal 10 0,.sub 6 9 1]
def hermiteStep : List Op := [.mul 7 0 2,.mul 8 5 3,.sub 7 7 8,.add 3 2 10,
  .add 2 7 10,.add 5 5 9,.mul 4 4 5,.sub 6 5 1,.add 6 6 9]
def hermiteFinish : List Op := [.sqrt 4 4,.div 2 2 4]
def hermiteCommand : Cmd := .seq (.block hermiteInit) (.seq (.loop (.real 6) (.block hermiteStep)) (.block hermiteFinish))
noncomputable def hermiteStates (ω : PolySampIso.Streams) (s : Store) (j : ℕ) : Store :=
  (blockAct ω hermiteStep)^[j] (blockAct ω hermiteInit s)
def HermiteInvariant (x : ℝ) (m j : ℕ) (s : Store) : Prop :=
  s.regs 0=x ∧ s.regs 1=m ∧ s.regs 2=hermiteValue j x ∧
  s.regs 3=(if j=0 then 0 else hermiteValue (j-1) x) ∧ s.regs 4=(j.factorial : ℝ) ∧
  s.regs 5=j ∧ s.regs 6=(j : ℝ)+1-m ∧ s.regs 9=1 ∧ s.regs 10=0
lemma hermite_initial_invariant (ω : PolySampIso.Streams) (s : Store) (m : ℕ) (hs : s.regs 1=m) :
    HermiteInvariant (s.regs 0) m 0 (blockAct ω hermiteInit s) := by
  simp [HermiteInvariant,blockAct,hermiteInit,Op.act,Function.update_apply,hs]
lemma hermite_step_invariant (ω : PolySampIso.Streams) (s : Store) (x : ℝ) (m j : ℕ) (hs : HermiteInvariant x m j s) :
    HermiteInvariant x m (j+1) (blockAct ω hermiteStep s) := by
  rcases hs with ⟨h0,h1,h2,h3,h4,h5,h6,h9,h10⟩
  simp only [HermiteInvariant,blockAct,hermiteStep,List.foldl_cons,List.foldl_nil,Op.act,
    Function.update_apply]
  norm_num
  simp [h0,h1,h2,h3,h4,h5,h9,h10,hermiteValue_step,Nat.factorial_succ]
  <;> ring_nf <;> simp
lemma hermite_states_invariant (ω : PolySampIso.Streams) (s : Store) (m : ℕ) (hs : s.regs 1=m) (j : ℕ) :
    HermiteInvariant (s.regs 0) m j (hermiteStates ω s j) := by
  induction j with
  | zero => exact hermite_initial_invariant ω s m hs
  | succ j ih =>
    rw [hermiteStates,Function.iterate_succ_apply']
    exact hermite_step_invariant ω _ _ m j ih
lemma hermite_command_correct (ω : PolySampIso.Streams) (s : Store) (m : ℕ) (hs : s.regs 1=m) :
    ∃ t, Eval ω hermiteCommand s t (11+11*m) ∧ t.regs 2=AMPLowDeg.RankOne.hermNorm m (s.regs 0) := by
  let states := hermiteStates ω s
  have hinv := hermite_states_invariant ω s m hs
  have hlo := eval_loop_range ω (.real 6) (.block hermiteStep) m states (fun _ => 9)
    (fun i hi => by
      change (states i).regs 6 ≤ 0
      rw [(hinv i).2.2.2.2.2.2.1]
      have hc : (i : ℝ)+1 ≤ m := by exact_mod_cast (show i+1 ≤ m by omega)
      linarith)
    (by
      change ¬(states m).regs 6 ≤ 0
      rw [(hinv m).2.2.2.2.2.2.1]
      linarith)
    (fun i hi => by
      have he := eval_block ω hermiteStep (states i)
      change Eval ω (.block hermiteStep) (states i) (blockAct ω hermiteStep (states i)) 9 at he
      convert! he using 1
      exact Function.iterate_succ_apply' _ i _)
  let t := blockAct ω hermiteFinish (states m)
  refine ⟨t,?_,?_⟩
  · have he := Eval.seq (eval_block ω hermiteInit s) (Eval.seq hlo (eval_block ω hermiteFinish (states m)))
    convert he using 1 <;> simp [hermiteCommand,hermiteInit,hermiteFinish,states,hermiteStates] <;> omega
  · have hv := hinv m
    change (blockAct ω hermiteFinish (states m)).regs 2 = _
    have h2 : (states m).regs 2 = hermiteValue m (s.regs 0) := hv.2.2.1
    have h4 : (states m).regs 4 = (m.factorial : ℝ) := hv.2.2.2.2.1
    simp [blockAct,hermiteFinish,Op.act,h2,h4,AMPLowDeg.RankOne.hermNorm,hermiteValue]
lemma hermite_command_frame (ω : PolySampIso.Streams) (s : Store) (m : ℕ) (hs : s.regs 1=m) :
    ∃ t, Eval ω hermiteCommand s t (11+11*m) ∧
      t.regs 2=AMPLowDeg.RankOne.hermNorm m (s.regs 0) ∧ t.mem=s.mem ∧ t.ptrs=s.ptrs ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧ ∀ r, r < 2 ∨ 10 < r → t.regs r=s.regs r := by
  obtain ⟨t,he,hv⟩ := hermite_command_correct ω s m hs
  have hc := he.cursors_preserved (by decide)
  refine ⟨t,he,hv,he.memory_preserved (by decide),?_,hc.1,hc.2,?_⟩
  · funext q
    exact he.pointer_preserved (by simp [hermiteCommand,Cmd.pointers,Cmd.block,hermiteInit,hermiteStep,hermiteFinish,Op.pointers])
  · intro r hr
    apply he.register_preserved
    simp [hermiteCommand,Cmd.registers,Cmd.block,hermiteInit,hermiteStep,hermiteFinish,Op.registers]
    omega
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMTensorFeature
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
noncomputable def tensorValue (κ : List ℕ) (xs : List ℝ) : ℝ :=
  (List.zipWith (fun k x => AMPLowDeg.RankOne.hermNorm k x) κ xs).prod
def tensorPrefix : List Op := [.load 0 3,.load 1 4]
def tensorSuffix : List Op := [.mul 30 30 2,.pinc 3,.pinc 4,.pinc 12]
def tensorBody : Cmd := .seq (.block tensorPrefix) (.seq hermiteCommand (.block tensorSuffix))
def tensorLoop : Cmd := .loop (.pointer 12 0) tensorBody
lemma tensor_loop_correct (ω : PolySampIso.Streams) (xs : List ℝ) (κ : List ℕ)
    (hlen : κ.length=xs.length) (s : Store)
    (hbound : s.ptrs 12+(xs.length : ℤ)=s.ptrs 0+1)
    (hxs : readArray s.mem (s.ptrs 3) xs.length=xs)
    (hκ : readArray s.mem (s.ptrs 4) κ.length=κ.map (fun k : ℕ => (k : ℝ))) :
    ∃ t k, k ≤ 2+19*xs.length+11*κ.sum ∧ Eval ω tensorLoop s t k ∧
      t.regs 30=s.regs 30*tensorValue κ xs ∧ t.mem=s.mem ∧
      t.ptrs 3=s.ptrs 3+(xs.length : ℤ) ∧ t.ptrs 4=s.ptrs 4+(xs.length : ℤ) ∧
      t.ptrs 12=t.ptrs 0+1 := by
  induction xs generalizing κ s with
  | nil =>
    have hk : κ=[] := List.length_eq_zero_iff.mp hlen
    subst κ
    refine ⟨s,2,by simp,Eval.loop_done ?_,?_,rfl,?_,?_,?_⟩
    · change ¬s.ptrs 12 ≤ s.ptrs 0
      simp only [List.length_nil,Nat.cast_zero,add_zero] at hbound
      omega
    · simp [tensorValue]
    · simp
    · simp
    · simpa using hbound
  | cons x xs ih =>
    cases κ with
    | nil => simp at hlen
    | cons a κ =>
      have hlen' : κ.length=xs.length := by simpa using hlen
      have hxs' : s.mem (s.ptrs 3)=x ∧ readArray s.mem (s.ptrs 3+1) xs.length=xs := by
        simpa only [List.length_cons,readArray_cons,List.cons.injEq] using hxs
      have hκ' : s.mem (s.ptrs 4)=(a : ℝ) ∧
          readArray s.mem (s.ptrs 4+1) κ.length=κ.map (fun k : ℕ => (k : ℝ)) := by
        simpa only [List.length_cons,readArray_cons,List.map_cons,List.cons.injEq] using hκ
      have hhead : Test.holds s (.pointer 12 0) := by
        change s.ptrs 12 ≤ s.ptrs 0
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
        omega
      let u := blockAct ω tensorPrefix s
      have hu : Eval ω (.block tensorPrefix) s u 2 := eval_block ω tensorPrefix s
      have humem : u.mem=s.mem := rfl
      have huptr : u.ptrs=s.ptrs := rfl
      have hu0 : u.regs 0=x := by simp [u,blockAct,tensorPrefix,Op.act,hxs'.1]
      have hu1 : u.regs 1=(a : ℝ) := by simp [u,blockAct,tensorPrefix,Op.act,hκ'.1]
      obtain ⟨v,he,hval,hmem,hptr,hgc,hec,hreg⟩ := hermite_command_frame ω u a hu1
      let w := blockAct ω tensorSuffix v
      have hw : Eval ω (.block tensorSuffix) v w 4 := eval_block ω tensorSuffix v
      have hwmem : w.mem=s.mem := hmem.trans humem
      have hwptr : w.ptrs=Function.update (Function.update (Function.update s.ptrs 3 (s.ptrs 3+1)) 4 (s.ptrs 4+1)) 12 (s.ptrs 12+1) := by
        simp [w,blockAct,tensorSuffix,Op.act,hptr,huptr]
      have hw30 : w.regs 30=s.regs 30*AMPLowDeg.RankOne.hermNorm a x := by
        change v.regs 30*v.regs 2 = _
        rw [hreg 30 (by omega),hval,hu0]
        rfl
      have hwb : w.ptrs 12+(xs.length : ℤ)=w.ptrs 0+1 := by
        simp only [hwptr,Function.update_apply]
        norm_num
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
        omega
      obtain ⟨t,k,hk,hr,h30,hM,h3,h4,h12⟩ := ih κ hlen' w hwb
        (by simpa [hwmem,hwptr] using hxs'.2) (by simpa [hwmem,hwptr] using hκ'.2)
      have hall := Eval.loop_step hhead (Eval.seq hu (Eval.seq he hw)) hr
      refine ⟨t,19+11*a+k,?_,?_,?_,hM.trans hwmem,?_,?_,h12⟩
      · simp only [List.length_cons,List.sum_cons]
        omega
      · convert! hall using 1 <;> omega
      · rw [h30,hw30]
        simp only [tensorValue,List.zipWith_cons_cons,List.prod_cons]
        ring
      · rw [h3,hwptr]
        norm_num
        push_cast
        ring
      · rw [h4,hwptr]
        norm_num
        push_cast
        ring
end PrivateAgnosticHalfspace.Gaussian.RAM

namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
def tensorCommand : Cmd := .seq (.block [.literal 30 1,.pset 12 1]) tensorLoop
lemma tensorValue_ofFn (d : ℕ) (κ : Fin d → ℕ) (x : Vec d) :
    tensorValue (List.ofFn κ) (List.ofFn (fun i => x i))=hermite d κ x := by
  have hz : List.zipWith (fun k x => AMPLowDeg.RankOne.hermNorm k x) (List.ofFn κ)
      (List.ofFn (fun i => x i))=List.ofFn (fun i => AMPLowDeg.RankOne.hermNorm (κ i) (x i)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  simp only [tensorValue,hz,List.prod_ofFn,hermite]
lemma tensor_command_correct (ω : PolySampIso.Streams) (d p : ℕ) (κ : Index d p) (x : Vec d)
    (s : Store) (hd : s.ptrs 0=d)
    (hx : readArray s.mem (s.ptrs 3) d=List.ofFn (fun i => x i))
    (hκ : readArray s.mem (s.ptrs 4) d=(digits κ).map (fun k : ℕ => (k : ℝ))) :
    ∃ t k, k ≤ 4+19*d+11*p ∧ Eval ω tensorCommand s t k ∧
      t.regs 30=hermite d (fun i => (κ.val i).val) x ∧ t.mem=s.mem ∧
      t.ptrs 3=s.ptrs 3+d ∧ t.ptrs 4=s.ptrs 4+d ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,2,3,4,5,6,7,8,9,10,30} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω [.literal 30 1,.pset 12 1] s
  have hu : Eval ω (.block [.literal 30 1,.pset 12 1]) s u 2 := eval_block ω _ s
  have humem : u.mem=s.mem := rfl
  have hu3 : u.ptrs 3=s.ptrs 3 := by simp [u,blockAct,Op.act]
  have hu4 : u.ptrs 4=s.ptrs 4 := by simp [u,blockAct,Op.act]
  have hub : u.ptrs 12+((List.ofFn (fun i => x i)).length : ℤ)=u.ptrs 0+1 := by
    simp [u,blockAct,Op.act,hd,add_comm]
  obtain ⟨t,k,hk,he,h30,hmem,h3,h4,h12⟩ := tensor_loop_correct ω
    (List.ofFn (fun i => x i)) (digits κ) (by simp) u hub (by simpa [humem,hu3] using hx)
      (by simpa [humem,hu4] using hκ)
  have hall : Eval ω tensorCommand s t (2+k) := Eval.seq hu he
  have hsum : (digits κ).sum ≤ p := digits_valid κ
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,2+k,?_,hall,?_,hmem.trans humem,?_,?_,hc.1,hc.2,?_,?_⟩
  · simp only [List.length_ofFn] at hk
    omega
  · rw [h30]
    have hu30 : u.regs 30=1 := by simp [u,blockAct,Op.act]
    rw [hu30,one_mul]
    exact tensorValue_ofFn d _ x
  · simpa only [List.length_ofFn,hu3] using h3
  · simpa only [List.length_ofFn,hu4] using h4
  · intro r hr
    apply hall.register_preserved
    simp [tensorCommand,tensorLoop,tensorBody,hermiteCommand,Cmd.block,Cmd.registers,
      tensorPrefix,tensorSuffix,hermiteInit,hermiteStep,hermiteFinish,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [tensorCommand,tensorLoop,tensorBody,hermiteCommand,Cmd.block,Cmd.pointers,
      tensorPrefix,tensorSuffix,hermiteInit,hermiteStep,hermiteFinish,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMCyclicIndex
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
noncomputable def cyclicIndex (d p r : ℕ) : Index d p :=
  (coefficientIndexEquiv d p).symm ⟨r % featureDimension d p,Nat.mod_lt r (by
    exact Nat.choose_pos (by omega))⟩
lemma cyclicIndex_rank (d p r : ℕ) : indexRank (cyclicIndex d p r)=r % featureDimension d p :=
  rank_inverse_val _
lemma cyclicIndex_zero (d p : ℕ) : cyclicIndex d p 0=zeroIndex d p := by
  apply indexRank_injective d p
  simp [cyclicIndex_rank]
lemma cyclicIndex_end (d p : ℕ) : cyclicIndex d p (featureDimension d p)=zeroIndex d p := by
  apply indexRank_injective d p
  simp [cyclicIndex_rank]
lemma successor_cyclicIndex (d p r : ℕ) (hr : r < featureDimension d p) :
    successorDigits p (digits (cyclicIndex d p r))=digits (cyclicIndex d p (r+1)) := by
  by_cases hn : r+1 < featureDimension d p
  · have he := next_rank_index (cyclicIndex d p r) (by simpa only [cyclicIndex_rank,Nat.mod_eq_of_lt hr] using hn)
    unfold successorDigits
    rw [he]
    simp only [Option.getD_some,cyclicIndex_rank,Nat.mod_eq_of_lt hr]
    congr 2
    exact Fin.ext (Nat.mod_eq_of_lt hn).symm
  · have he : r+1=featureDimension d p := by omega
    have ht : next p (digits (cyclicIndex d p r))=none :=
      next_terminal _ (by simpa only [cyclicIndex_rank,Nat.mod_eq_of_lt hr] using he)
    simp [successorDigits,ht,he,cyclicIndex_end]
lemma coefficientIsometry_feature (d p : ℕ) (x : Vec d) (i : Fin (featureDimension d p)) :
    (coefficientIsometry d p (features d p x)) i=
      hermite d (fun j => (((coefficientIndexEquiv d p).symm i).val j).val) x := by
  rfl
end PrivateAgnosticHalfspace.Gaussian.RAM

namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma cyclicIndex_of_fin {d p : ℕ} (i : Fin (featureDimension d p)) :
    cyclicIndex d p i.val=(coefficientIndexEquiv d p).symm i := by
  unfold cyclicIndex
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMDimensionBody
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
lemma cyclicIndex_next_flag (d p r : ℕ) (hr : r < featureDimension d p) :
    (if (next p (digits (cyclicIndex d p r))).isSome then (1 : ℝ) else 0)=
      if r+1 < featureDimension d p then 1 else 0 := by
  by_cases h : r+1 < featureDimension d p
  · have hh := next_rank_index (cyclicIndex d p r) (by simpa only [cyclicIndex_rank,Nat.mod_eq_of_lt hr] using h)
    simp [hh,h]
  · have hh := next_terminal (cyclicIndex d p r) (by rw [cyclicIndex_rank,Nat.mod_eq_of_lt hr]; omega)
    simp [hh,h]
def dimensionIncrement : List Op := [.pinc 15,.pointerReal 44 15,.add 41 40 43,.sub 41 41 44]
def dimensionDecision : Cmd := .cond (.real 22) (.block [.literal 42 1])
  (.seq (.block dimensionIncrement) (.cond (.real 41) (.block [.literal 42 1]) .skip))
def dimensionBody : Cmd := .seq indexSuccessorCommand dimensionDecision
def dimensionLoop : Cmd := .loop (.real 42) dimensionBody
def dimensionInit : List Op := [.pset 15 1,.literal 42 0,.literal 43 1]
def dimensionCommand : Cmd := .seq (.block dimensionInit) dimensionLoop
lemma dimension_decision_correct (ω : PolySampIso.Streams) (D n r : ℕ) (hrD : r < D) (hrn : r < n)
    (s : Store) (h15 : s.ptrs 15=(r : ℤ)+1) (h22 : s.regs 22=if r+1<D then 1 else 0)
    (h40 : s.regs 40=n) (h42 : s.regs 42=0) (h43 : s.regs 43=1) :
    ∃ t k, k ≤ 8 ∧ Eval ω dimensionDecision s t k ∧ t.mem=s.mem ∧
      t.ptrs 15=((min (r+2) D : ℕ) : ℤ) ∧ t.regs 42=(if r+1<D ∧ r+1<n then 0 else 1) ∧
      (∀ q, q ≠ 15 → t.ptrs q=s.ptrs q) ∧
      (∀ j, j ∉ ({41,42,44} : Finset ℕ) → t.regs j=s.regs j) := by
  by_cases hlast : r+1<D
  · have hno : ¬Test.holds s (.real 22) := by simp [Test.holds,h22,hlast]
    let u := blockAct ω dimensionIncrement s
    have hu : Eval ω (.block dimensionIncrement) s u 4 := eval_block ω dimensionIncrement s
    have hu15 : u.ptrs 15=(r : ℤ)+2 := by simp [u,blockAct,dimensionIncrement,Op.act,h15]; ring
    have hu41 : u.regs 41=(n : ℝ)+1-((r : ℝ)+2) := by
      simp [u,blockAct,dimensionIncrement,Op.act,h15,h40,h43]
      push_cast
      ring
    have hu42 : u.regs 42=0 := by simpa [u,blockAct,dimensionIncrement,Op.act] using h42
    by_cases hstop : r+1<n
    · have htest : ¬Test.holds u (.real 41) := by
        change ¬u.regs 41 ≤ 0
        rw [hu41]
        have hh : (r : ℝ)+2 ≤ n := by exact_mod_cast (show r+2 ≤ n by omega)
        linarith
      have he : Eval ω dimensionDecision s u 8 := Eval.cond_no hno (Eval.seq hu (Eval.cond_no htest (Eval.skip u)))
      refine ⟨u,8,by omega,he,rfl,?_,?_,?_,?_⟩
      · rw [hu15,Nat.min_eq_left (by omega)]
        push_cast
        ring
      · simp [hlast,hstop,hu42]
      · intro q hq
        exact he.pointer_preserved (by simp [dimensionDecision,dimensionIncrement,Cmd.block,Cmd.pointers,Op.pointers,hq])
      · intro j hj
        apply he.register_preserved
        simp [dimensionDecision,dimensionIncrement,Cmd.block,Cmd.registers,Op.registers]
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
        tauto
    · have htest : Test.holds u (.real 41) := by
        change u.regs 41 ≤ 0
        rw [hu41]
        have hh : n=r+1 := by omega
        subst n
        push_cast
        linarith
      let t := blockAct ω [.literal 42 1] u
      have ht : Eval ω (.block [.literal 42 1]) u t 1 := eval_block ω _ u
      have he : Eval ω dimensionDecision s t 8 := Eval.cond_no hno (Eval.seq hu (Eval.cond_yes htest ht))
      refine ⟨t,8,by omega,he,rfl,?_,?_,?_,?_⟩
      · change u.ptrs 15=_
        rw [hu15,Nat.min_eq_left (by omega)]
        push_cast
        ring
      · simp [t,blockAct,Op.act,hlast,hstop]
      · intro q hq
        exact he.pointer_preserved (by simp [dimensionDecision,dimensionIncrement,Cmd.block,Cmd.pointers,Op.pointers,hq])
      · intro j hj
        apply he.register_preserved
        simp [dimensionDecision,dimensionIncrement,Cmd.block,Cmd.registers,Op.registers]
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
        tauto
  · have hyes : Test.holds s (.real 22) := by simp [Test.holds,h22,hlast]
    let t := blockAct ω [.literal 42 1] s
    have ht : Eval ω (.block [.literal 42 1]) s t 1 := eval_block ω _ s
    have he : Eval ω dimensionDecision s t 2 := Eval.cond_yes hyes ht
    refine ⟨t,2,by omega,he,rfl,?_,?_,?_,?_⟩
    · change s.ptrs 15=_
      rw [h15,Nat.min_eq_right (by omega)]
      have hh : D=r+1 := by omega
      subst D
      push_cast
      rfl
    · simp [t,blockAct,Op.act,hlast]
    · intro q hq
      exact he.pointer_preserved (by simp [dimensionDecision,dimensionIncrement,Cmd.block,Cmd.pointers,Op.pointers,hq])
    · intro j hj
      apply he.register_preserved
      simp [dimensionDecision,dimensionIncrement,Cmd.block,Cmd.registers,Op.registers]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
      tauto
end PrivateAgnosticHalfspace.Gaussian.RAM

namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
lemma dimension_body_correct (ω : PolySampIso.Streams) (d p n r : ℕ)
    (hrD : r < featureDimension d p) (hrn : r < n) (s : Store)
    (hd : s.ptrs 0=d) (h15 : s.ptrs 15=(r : ℤ)+1)
    (harray : readArray s.mem (s.ptrs 9) d=(digits (cyclicIndex d p r)).map (fun a : ℕ => (a : ℝ)))
    (h20 : s.regs 20=((digits (cyclicIndex d p r)).sum : ℝ)) (h21 : s.regs 21=p)
    (h40 : s.regs 40=n) (h42 : s.regs 42=0) (h43 : s.regs 43=1) :
    ∃ t k, k ≤ 27+11*d ∧ Eval ω dimensionBody s t k ∧
      t.mem=writeArray s.mem (s.ptrs 9) ((digits (cyclicIndex d p (r+1))).map (fun a : ℕ => (a : ℝ))) ∧
      t.ptrs 15=((min (r+2) (featureDimension d p) : ℕ) : ℤ) ∧
      t.regs 42=(if r+1<featureDimension d p ∧ r+1<n then 0 else 1) ∧
      t.regs 20=((digits (cyclicIndex d p (r+1))).sum : ℝ) ∧ t.regs 21=p ∧ t.regs 40=n ∧ t.regs 43=1 ∧
      (∀ q, q ∉ ({10,11,15} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨u,k,hk,hu,hm,hu20,hu22,hgc,hec,hreg,hptr⟩ := index_successor_command ω d p
    (digits (cyclicIndex d p r)) (digits_valid _) (digits_length _) s hd harray h20 h21
  have hu15 : u.ptrs 15=(r : ℤ)+1 := by rw [hptr 15 (by omega) (by omega),h15]
  have hu22' : u.regs 22=if r+1<featureDimension d p then 1 else 0 :=
    hu22.trans (cyclicIndex_next_flag d p r hrD)
  have hu40 : u.regs 40=n := by rw [hreg 40 (by simp),h40]
  have hu42 : u.regs 42=0 := by rw [hreg 42 (by simp),h42]
  have hu43 : u.regs 43=1 := by rw [hreg 43 (by simp),h43]
  obtain ⟨t,l,hl,ht,htmem,ht15,ht42,htptr,htreg⟩ := dimension_decision_correct ω (featureDimension d p) n r hrD hrn
    u hu15 hu22' hu40 hu42 hu43
  have hall : Eval ω dimensionBody s t (k+l) := Eval.seq hu ht
  refine ⟨t,k+l,by omega,hall,?_,ht15,ht42,?_,?_,?_,?_,?_⟩
  · rw [htmem,hm,successor_cyclicIndex d p r hrD]
  · rw [htreg 20 (by simp),hu20,successor_cyclicIndex d p r hrD]
  · rw [htreg 21 (by simp),hreg 21 (by simp),h21]
  · rw [htreg 40 (by simp)]
    exact hu40
  · rw [htreg 43 (by simp)]
    exact hu43
  · intro q hq
    apply hall.pointer_preserved
    simp [dimensionBody,dimensionDecision,dimensionIncrement,indexSuccessorCommand,indexSuccessorLoop,indexSuccessorBody,
      indexSuccessorInit,indexSuccessorPrefix,indexSuccessorYes,indexSuccessorNo,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMDimensionCount
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
structure DimensionInvariant (d p n : ℕ) (s₀ : Store) (r : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ≠ 10 → q ≠ 11 → q ≠ 15 → s.ptrs q=s₀.ptrs q
  count : s.ptrs 15=((min (r+1) (featureDimension d p) : ℕ) : ℤ)
  array : readArray s.mem (s.ptrs 9) d=(digits (cyclicIndex d p r)).map (fun a : ℕ => (a : ℝ))
  total : s.regs 20=((digits (cyclicIndex d p r)).sum : ℝ)
  budget : s.regs 21=p
  sampleSize : s.regs 40=n
  one : s.regs 43=1
  stopped : s.regs 42=if r<featureDimension d p ∧ r<n then 0 else 1
  frame : ∀ z, (z < s₀.ptrs 9 ∨ s₀.ptrs 9+(d : ℤ) ≤ z) → s.mem z=s₀.mem z
lemma dimension_invariant_step (ω : PolySampIso.Streams) (d p n : ℕ) (s₀ : Store) (hd : s₀.ptrs 0=d)
    (r : ℕ) (hrD : r < featureDimension d p) (hrn : r < n) (s : Store) (hs : DimensionInvariant d p n s₀ r s) :
    ∃ t k, k ≤ 27+11*d ∧ Eval ω dimensionBody s t k ∧ DimensionInvariant d p n s₀ (r+1) t := by
  have hs0 : s.ptrs 0=d := (hs.fixedPointers 0 (by omega) (by omega) (by omega)).trans hd
  have hs15 : s.ptrs 15=(r : ℤ)+1 := by rw [hs.count,Nat.min_eq_left (by omega)]; push_cast; rfl
  have hs42 : s.regs 42=0 := by simpa only [hrD,hrn,and_self,ite_true] using hs.stopped
  obtain ⟨t,k,hk,he,hm,h15,h42,h20,h21,h40,h43,hptr⟩ := dimension_body_correct ω d p n r hrD hrn s
    hs0 hs15 hs.array hs.total hs.budget hs.sampleSize hs42 hs.one
  have hs9 := hs.fixedPointers 9 (by omega) (by omega) (by omega)
  have ht9 := hptr 9 (by simp)
  refine ⟨t,k,hk,he,?_⟩
  constructor
  · intro q hq10 hq11 hq15
    exact (hptr q (by simp [hq10,hq11,hq15])).trans (hs.fixedPointers q hq10 hq11 hq15)
  · simpa only [Nat.add_assoc,show 1+1=2 by rfl] using h15
  · rw [ht9,hm]
    have hlen : ((digits (cyclicIndex d p (r+1))).map (fun a : ℕ => (a : ℝ))).length=d := by simp
    simpa only [hlen] using readArray_writeArray s.mem (s.ptrs 9)
      ((digits (cyclicIndex d p (r+1))).map (fun a : ℕ => (a : ℝ)))
  · exact h20
  · exact h21
  · exact h40
  · exact h43
  · exact h42
  · intro z hz
    rw [hm,writeArray_outside _ _ _ z (by simpa [hs9] using hz)]
    exact hs.frame z hz
lemma dimension_command_correct (ω : PolySampIso.Streams) (d p n : ℕ) (hn : 0 < n) (s : Store)
    (hd : s.ptrs 0=d) (harray : readArray s.mem (s.ptrs 9) d=List.replicate d 0)
    (h20 : s.regs 20=0) (h21 : s.regs 21=p) (h40 : s.regs 40=n) :
    ∃ t k, k ≤ 5+n*(29+11*d) ∧ Eval ω dimensionCommand s t k ∧
      t.ptrs 15=((if featureDimension d p ≤ n then featureDimension d p else n+1 : ℕ) : ℤ) ∧
      t.regs 42=1 ∧ t.regs 21=p ∧ t.regs 40=n ∧ t.regs 43=1 ∧
      (featureDimension d p ≤ n → readArray t.mem (s.ptrs 9) d=List.replicate d 0 ∧ t.regs 20=0) ∧
      (∀ z, (z < s.ptrs 9 ∨ s.ptrs 9+(d : ℤ) ≤ z) → t.mem z=s.mem z) ∧
      (∀ q, q ≠ 10 → q ≠ 11 → q ≠ 15 → t.ptrs q=s.ptrs q) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  let N := min (featureDimension d p) n
  have hD : 0 < featureDimension d p := Nat.choose_pos (by omega)
  have hN : 0 < N := Nat.lt_min.mpr ⟨hD,hn⟩
  let u := blockAct ω dimensionInit s
  have hu : Eval ω (.block dimensionInit) s u 3 := eval_block ω dimensionInit s
  let Inv := DimensionInvariant d p n s
  have hinit : Inv 0 u := by
    constructor
    · intro q hq10 hq11 hq15
      simp [u,blockAct,dimensionInit,Op.act,hq15]
    · simp [u,blockAct,dimensionInit,Op.act,Nat.min_eq_left hD]
    · simpa [u,blockAct,dimensionInit,Op.act,cyclicIndex_zero] using harray
    · simpa [u,blockAct,dimensionInit,Op.act,cyclicIndex_zero] using h20
    · simpa [u,blockAct,dimensionInit,Op.act] using h21
    · simpa [u,blockAct,dimensionInit,Op.act] using h40
    · simp [u,blockAct,dimensionInit,Op.act]
    · simp [u,blockAct,dimensionInit,Op.act,hD,hn]
    · intro z hz; rfl
  have htrue (i : ℕ) (hi : i < N) (v : Store) (hv : Inv i v) : Test.holds v (.real 42) := by
    change v.regs 42 ≤ 0
    rw [hv.stopped,if_pos (by dsimp [N] at hi; omega)]
  have hfalse (v : Store) (hv : Inv N v) : ¬Test.holds v (.real 42) := by
    change ¬v.regs 42 ≤ 0
    rw [hv.stopped,if_neg (by dsimp [N]; omega)]
    norm_num
  obtain ⟨t,k,hk,he,ht⟩ := eval_loop_invariant ω (.real 42) dimensionBody N (27+11*d) Inv htrue hfalse
    (fun i hi v hv => dimension_invariant_step ω d p n s hd i (by dsimp [N] at hi; omega) (by dsimp [N] at hi; omega) v hv) u hinit
  have hall : Eval ω dimensionCommand s t (3+k) := Eval.seq hu he
  have hcg := hall.cursors_preserved (by decide)
  refine ⟨t,3+k,?_,hall,?_,?_,ht.budget,ht.sampleSize,ht.one,?_,ht.frame,ht.fixedPointers,hcg.1,hcg.2⟩
  · have hNn : N ≤ n := Nat.min_le_right _ _
    nlinarith only [hk,hNn]
  · rw [ht.count]
    by_cases hDn : featureDimension d p ≤ n
    · simp only [if_pos hDn,N,Nat.min_eq_left hDn]
      rw [Nat.min_eq_right (by omega)]
    · simp only [if_neg hDn,N,Nat.min_eq_right (show n ≤ featureDimension d p by omega)]
      rw [Nat.min_eq_left (by omega)]
  · rw [ht.stopped,if_neg (by dsimp [N]; omega)]
  · intro hDn
    have heN : N=featureDimension d p := Nat.min_eq_left hDn
    have harr := ht.array
    rw [ht.fixedPointers 9 (by omega) (by omega) (by omega),heN] at harr
    have hsum := ht.total
    rw [heN] at hsum
    exact ⟨by simpa [cyclicIndex_end] using harr,by simpa [cyclicIndex_end] using hsum⟩
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPreparedShape
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def workspaceBase (d N : ℕ) : ℤ := 11+(N : ℤ)*((d : ℤ)+1)
def shapeSetup : List Op := [.pset 30 4,.load 40 30,.literal 20 0,.pointerReal 21 1]
def prepareShapeCommand : Cmd := .seq prepareWorkspaceCommand (.seq (.block shapeSetup) dimensionCommand)
structure PreparedShape (d p M N n : ℕ) (input : ℕ → ℝ) (t : Store) : Prop where
  dim : t.ptrs 0=d
  degreePointer : t.ptrs 1=p
  thresholdPointer : t.ptrs 2=M
  inputStart : t.ptrs 7=11
  exponentBase : t.ptrs 9=workspaceBase d N
  featureBase : t.ptrs 13=workspaceBase d N+d
  dimension : t.ptrs 15=((if featureDimension d p ≤ n then featureDimension d p else n+1 : ℕ) : ℤ)
  totalSize : t.ptrs 17=N
  budget : t.regs 21=p
  trainSize : t.regs 40=n
  active : featureDimension d p ≤ n → readArray t.mem (t.ptrs 9) d=List.replicate d 0 ∧ t.regs 20=0
  frame : ∀ z, (z < workspaceBase d N ∨ workspaceBase d N+(d : ℤ) ≤ z) →
    t.mem z=(initialStore d p M input).mem z
lemma prepare_shape_correct (ω : PolySampIso.Streams) (d p M N n : ℕ) (hn : 0 < n)
    (input : ℕ → ℝ) (hN : input 10=N) (htrain : input 4=n) :
    ∃ t k, k ≤ 30+5*d+N*(13+4*d)+n*(29+11*d) ∧
      Eval ω prepareShapeCommand (initialStore d p M input) t k ∧ PreparedShape d p M N n input t ∧ t.gc=0 ∧ t.ec=0 := by
  obtain ⟨u,k,hk,hu,hum,hu0,hu7,hu9,hu13,hu15,hu17,hu32,hureg,huptr,hugc,huec⟩ :=
    prepare_workspace_correct ω d p M N input hN
  change u.mem=writeArray (initialStore d p M input).mem (workspaceBase d N) (List.replicate d 0) at hum
  have hu1 : u.ptrs 1=p := by rw [huptr 1 (by simp)]; simp [initialStore]
  have hB : (4 : ℤ) < workspaceBase d N := by
    unfold workspaceBase
    have h : 0 ≤ (N : ℤ)*((d : ℤ)+1) := by positivity
    omega
  have hu4 : u.mem (4 : ℤ)=n := by
    rw [hum,writeArray_outside _ _ _ _ (Or.inl hB)]
    simpa [initialStore] using htrain
  let v := blockAct ω shapeSetup u
  have hv : Eval ω (.block shapeSetup) u v 4 := eval_block ω shapeSetup u
  have hv0 : v.ptrs 0=d := by simp [v,blockAct,shapeSetup,Op.act,hu0]
  have hv9 : v.ptrs 9=workspaceBase d N := by simp [v,blockAct,shapeSetup,Op.act,hu9,workspaceBase]
  have hv40 : v.regs 40=n := by simp [v,blockAct,shapeSetup,Op.act,hu4]
  have hv20 : v.regs 20=0 := by simp [v,blockAct,shapeSetup,Op.act]
  have hv21 : v.regs 21=p := by simp [v,blockAct,shapeSetup,Op.act,hu1]
  have hvarray : readArray v.mem (v.ptrs 9) d=List.replicate d 0 := by
    rw [hv9]
    change readArray u.mem (workspaceBase d N) d=_
    rw [hum]
    simpa only [List.length_replicate] using readArray_writeArray (initialStore d p M input).mem (workspaceBase d N) (List.replicate d 0)
  obtain ⟨t,l,hl,ht,ht15,ht42,ht21,ht40,ht43,htactive,htframe,htptr,htgc,htec⟩ :=
    dimension_command_correct ω d p n hn v hv0 hvarray hv20 hv21 hv40
  have hall : Eval ω prepareShapeCommand (initialStore d p M input) t (k+(4+l)) := Eval.seq hu (Eval.seq hv ht)
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,k+(4+l),by omega,hall,?_,hc.1,hc.2⟩
  constructor
  · rw [htptr 0 (by omega) (by omega) (by omega)]
    exact hv0
  · have hh := hall.pointer_preserved (q := 1) (by decide)
    simpa [initialStore] using hh
  · have hh := hall.pointer_preserved (q := 2) (by decide)
    simpa [initialStore] using hh
  · rw [htptr 7 (by omega) (by omega) (by omega)]
    simpa [v,blockAct,shapeSetup,Op.act] using hu7
  · rw [htptr 9 (by omega) (by omega) (by omega)]
    exact hv9
  · rw [htptr 13 (by omega) (by omega) (by omega)]
    simpa [v,blockAct,shapeSetup,Op.act,workspaceBase] using hu13
  · exact ht15
  · rw [htptr 17 (by omega) (by omega) (by omega)]
    simpa [v,blockAct,shapeSetup,Op.act] using hu17
  · exact ht21
  · exact ht40
  · intro hDn
    rw [htptr 9 (by omega) (by omega) (by omega)]
    exact htactive hDn
  · intro z hz
    rw [htframe z (by simpa only [hv9] using hz)]
    change u.mem z=_
    rw [hum,writeArray_outside _ _ _ z (by simpa [workspaceBase] using hz)]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMArrayFacts
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma readArray_congr (mem mem' : ℤ → ℝ) (base : ℤ) (n : ℕ)
    (h : ∀ i, i < n → mem (base+(i : ℤ))=mem' (base+(i : ℤ))) : readArray mem base n=readArray mem' base n := by
  unfold readArray
  congr 1
  funext i
  exact h i.val i.isLt
lemma encoded_index_interval (base : ℤ) (W j r i : ℕ) (hj : j < r) (hi : i < W) :
    base+(j : ℤ)*(W : ℤ)+(i : ℤ) < base+(r : ℤ)*(W : ℤ) := by
  have hm := mul_le_mul_of_nonneg_right (show (j : ℤ)+1 ≤ r by exact_mod_cast (show j+1 ≤ r by omega))
    (show (0 : ℤ) ≤ W by positivity)
  have hi' : (i : ℤ) < W := by exact_mod_cast hi
  nlinarith only [hm,hi']
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPreparedInput
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma workspaceBase_ge_eleven (d N : ℕ) : (11 : ℤ) ≤ workspaceBase d N := by
  unfold workspaceBase
  have h : 0 ≤ (N : ℤ)*((d : ℤ)+1) := by positivity
  omega
lemma workspace_row_cell_lt (d N : ℕ) (j : Fin N) (i : ℕ) (hi : i < d+1) :
    (11 : ℤ)+(j.val : ℤ)*((d : ℤ)+1)+(i : ℤ) < workspaceBase d N := by
  simpa [workspaceBase,Nat.cast_add,Nat.cast_one] using encoded_index_interval 11 (d+1) j.val N i j.isLt hi
lemma PreparedShape.header {d p M N n : ℕ} {input : ℕ → ℝ} {t : Store} (hs : PreparedShape d p M N n input t)
    (i : ℕ) (hi : i < 11) : t.mem (i : ℤ)=input i := by
  have hz : (i : ℤ) < workspaceBase d N := lt_of_lt_of_le (by exact_mod_cast hi) (workspaceBase_ge_eleven d N)
  rw [hs.frame _ (Or.inl hz),initialStore_nat_cell]
lemma PreparedShape.input_rows {d p M N n : ℕ} {input : ℕ → ℝ} {t : Store} (hs : PreparedShape d p M N n input t)
    (S : Fin N → Example d) (hS : InputRows d N S input) :
    (∀ j : Fin N, readArray t.mem (11+(j.val : ℤ)*((d : ℤ)+1)) d=List.ofFn (fun i => (S j).1 i)) ∧
    (∀ j : Fin N, t.mem (11+(j.val : ℤ)*((d : ℤ)+1)+(d : ℤ))=label (S j).2) := by
  obtain ⟨hxs,hys⟩ := initialStore_input_rows d p M N S input hS
  constructor
  · intro j
    have he : readArray t.mem (11+(j.val : ℤ)*((d : ℤ)+1)) d=
        readArray (initialStore d p M input).mem (11+(j.val : ℤ)*((d : ℤ)+1)) d := by
      apply readArray_congr
      intro i hi
      exact hs.frame _ (Or.inl (workspace_row_cell_lt d N j i (by omega)))
    rw [he]
    exact hxs j
  · intro j
    rw [hs.frame _ (Or.inl (workspace_row_cell_lt d N j d (by omega)))]
    exact hys j
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMFeatureBody
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
def featureReset : List Op := [.pcopy 3 7,.pcopy 4 9]
def featureStore : List Op := [.store 13 30,.pinc 13]
def featureBody : Cmd := .seq (.block featureReset) (.seq tensorCommand
  (.seq (.block featureStore) (.seq indexSuccessorCommand (.atom (.pinc 14)))))
def featureLoop : Cmd := .loop (.pointer 14 15) featureBody
lemma feature_body_correct (ω : PolySampIso.Streams) (d p r : ℕ) (hr : r < featureDimension d p)
    (x : Vec d) (s : Store) (hd : s.ptrs 0=d)
    (hx : readArray s.mem (s.ptrs 7) d=List.ofFn (fun i => x i))
    (hκ : readArray s.mem (s.ptrs 9) d=(digits (cyclicIndex d p r)).map (fun a : ℕ => (a : ℝ)))
    (hinput : s.ptrs 7+(d : ℤ) ≤ s.ptrs 9) (houtput : s.ptrs 9+(d : ℤ) ≤ s.ptrs 13)
    (htotal : s.regs 20=((digits (cyclicIndex d p r)).sum : ℝ)) (hbudget : s.regs 21=p) :
    ∃ t k, k ≤ 28+30*d+11*p ∧ Eval ω featureBody s t k ∧
      t.mem=writeArray (Function.update s.mem (s.ptrs 13)
        (hermite d (fun i => ((cyclicIndex d p r).val i).val) x)) (s.ptrs 9)
        ((digits (cyclicIndex d p (r+1))).map (fun a : ℕ => (a : ℝ))) ∧
      t.regs 20=((digits (cyclicIndex d p (r+1))).sum : ℝ) ∧ t.regs 21=p ∧
      t.ptrs 13=s.ptrs 13+1 ∧ t.ptrs 14=s.ptrs 14+1 ∧
      (∀ q, q ∉ ({3,4,10,11,12,13,14} : Finset ℕ) → t.ptrs q=s.ptrs q) ∧
      t.gc=s.gc ∧ t.ec=s.ec := by
  let u := blockAct ω featureReset s
  have hu : Eval ω (.block featureReset) s u 2 := eval_block ω featureReset s
  have humem : u.mem=s.mem := rfl
  have hu3 : u.ptrs 3=s.ptrs 7 := by simp [u,blockAct,featureReset,Op.act]
  have hu4 : u.ptrs 4=s.ptrs 9 := by simp [u,blockAct,featureReset,Op.act]
  have hu0 : u.ptrs 0=d := by simpa [u,blockAct,featureReset,Op.act] using hd
  obtain ⟨v,l,hl,hv,hvalue,hmem,h3,h4,hgc,hec,hreg,hptr⟩ := tensor_command_correct ω d p (cyclicIndex d p r) x u hu0
    (by simpa only [humem,hu3] using hx) (by simpa only [humem,hu4] using hκ)
  have hp9 : v.ptrs 9=s.ptrs 9 := by rw [hptr 9 (by simp)]; simp [u,blockAct,featureReset,Op.act]
  have hp13 : v.ptrs 13=s.ptrs 13 := by rw [hptr 13 (by simp)]; simp [u,blockAct,featureReset,Op.act]
  have hp0 : v.ptrs 0=d := by rw [hptr 0 (by simp)]; exact hu0
  have hr20 : v.regs 20=s.regs 20 := by rw [hreg 20 (by simp)]; rfl
  have hr21 : v.regs 21=s.regs 21 := by rw [hreg 21 (by simp)]; rfl
  let w := blockAct ω featureStore v
  have hw : Eval ω (.block featureStore) v w 2 := eval_block ω featureStore v
  have hwmem : w.mem=Function.update s.mem (s.ptrs 13)
      (hermite d (fun i => ((cyclicIndex d p r).val i).val) x) := by
    simp [w,blockAct,featureStore,Op.act,hvalue,hmem,humem,hp13]
  have hwp9 : w.ptrs 9=s.ptrs 9 := by simp [w,blockAct,featureStore,Op.act,hp9]
  have hwp0 : w.ptrs 0=d := by simp [w,blockAct,featureStore,Op.act,hp0]
  have hwarray : readArray w.mem (w.ptrs 9) d=(digits (cyclicIndex d p r)).map (fun a : ℕ => (a : ℝ)) := by
    rw [hwmem,hwp9,readArray_update_after _ _ _ _ _ houtput]
    exact hκ
  have hw20 : w.regs 20=((digits (cyclicIndex d p r)).sum : ℝ) := by
    simpa [w,blockAct,featureStore,Op.act,hr20] using htotal
  have hw21 : w.regs 21=p := by simpa [w,blockAct,featureStore,Op.act,hr21] using hbudget
  obtain ⟨z,m,hm,hz,hzm,hz20,hz22,hzgc,hzec,hzreg,hzptr⟩ := index_successor_command ω d p
    (digits (cyclicIndex d p r)) (digits_valid _) (digits_length _) w hwp0 hwarray hw20 hw21
  let t := Op.act ω z (.pinc 14)
  have ht : Eval ω (.atom (.pinc 14)) z t 1 := Eval.atom z _
  have hall : Eval ω featureBody s t (2+(l+(2+(m+1)))) := Eval.seq hu (Eval.seq hv (Eval.seq hw (Eval.seq hz ht)))
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,2+(l+(2+(m+1))),by omega,hall,?_,?_,?_,?_,?_,?_,hc.1,hc.2⟩
  · change z.mem=_
    rw [hzm,hwmem,hwp9,successor_cyclicIndex d p r hr]
  · change z.regs 20=_
    rw [hz20,successor_cyclicIndex d p r hr]
  · change z.regs 21=p
    rw [hzreg 21 (by simp)]
    exact hw21
  · change z.ptrs 13=s.ptrs 13+1
    rw [hzptr 13 (by omega) (by omega)]
    simp [w,blockAct,featureStore,Op.act,hp13]
  · change z.ptrs 14+1=s.ptrs 14+1
    rw [hzptr 14 (by omega) (by omega)]
    have hv14 := hptr 14 (by simp)
    simp [w,blockAct,featureStore,Op.act,hv14,u,featureReset]
  · intro q hq
    apply hall.pointer_preserved
    simp [featureBody,featureReset,featureStore,tensorCommand,tensorLoop,tensorBody,
      hermiteCommand,hermiteInit,hermiteStep,hermiteFinish,tensorPrefix,tensorSuffix,
      indexSuccessorCommand,indexSuccessorLoop,indexSuccessorBody,indexSuccessorInit,indexSuccessorPrefix,
      indexSuccessorYes,indexSuccessorNo,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMFeatureLoop
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open DenseEnumeration
noncomputable def orderedFeatures (d p : ℕ) (x : Vec d) : List ℝ :=
  List.ofFn (fun i : Fin (featureDimension d p) => hermite d (fun j => ((cyclicIndex d p i.val).val j).val) x)
structure FeatureInvariant (d p : ℕ) (x : Vec d) (s₀ : Store) (r : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ∈ ({0,7,9,15} : Finset ℕ) → s.ptrs q=s₀.ptrs q
  output : s.ptrs 13=s₀.ptrs 13+(r : ℤ)
  counter : s.ptrs 14=(r : ℤ)+1
  input : readArray s.mem (s.ptrs 7) d=List.ofFn (fun i => x i)
  digits : readArray s.mem (s.ptrs 9) d=(DenseEnumeration.digits (cyclicIndex d p r)).map (fun a : ℕ => (a : ℝ))
  total : s.regs 20=((DenseEnumeration.digits (cyclicIndex d p r)).sum : ℝ)
  budget : s.regs 21=p
  written : ∀ i, i < r → s.mem (s₀.ptrs 13+(i : ℤ))=hermite d (fun j => ((cyclicIndex d p i).val j).val) x
  frame : ∀ z, (z < s₀.ptrs 9 ∨ s₀.ptrs 9+(d : ℤ) ≤ z) →
    (z < s₀.ptrs 13 ∨ s₀.ptrs 13+(r : ℤ) ≤ z) → s.mem z=s₀.mem z
lemma feature_invariant_step (ω : PolySampIso.Streams) (d p : ℕ) (x : Vec d) (s₀ : Store)
    (hd : s₀.ptrs 0=d) (hinput : s₀.ptrs 7+(d : ℤ) ≤ s₀.ptrs 9)
    (houtput : s₀.ptrs 9+(d : ℤ) ≤ s₀.ptrs 13) (r : ℕ) (hr : r < featureDimension d p)
    (s : Store) (hs : FeatureInvariant d p x s₀ r s) :
    ∃ t k, k ≤ 28+30*d+11*p ∧ Eval ω featureBody s t k ∧ FeatureInvariant d p x s₀ (r+1) t := by
  have hp0 := hs.fixedPointers 0 (by simp)
  have hp7 := hs.fixedPointers 7 (by simp)
  have hp9 := hs.fixedPointers 9 (by simp)
  have hin : s.ptrs 7+(d : ℤ) ≤ s.ptrs 9 := by simpa only [hp7,hp9] using hinput
  have hout : s.ptrs 9+(d : ℤ) ≤ s.ptrs 13 := by rw [hp9,hs.output]; omega
  obtain ⟨t,k,hk,he,hm,h20,h21,h13,h14,hpublic,hgc,hec⟩ := feature_body_correct ω d p r hr x s
    (hp0.trans hd) hs.input hs.digits hin hout hs.total hs.budget
  have ht7 : t.ptrs 7=s.ptrs 7 := hpublic 7 (by simp)
  have ht9 : t.ptrs 9=s.ptrs 9 := hpublic 9 (by simp)
  refine ⟨t,k,hk,he,?_⟩
  constructor
  · intro q hq
    exact (hpublic q (by simp only [Finset.mem_insert,Finset.mem_singleton] at hq; rcases hq with rfl|rfl|rfl|rfl <;> simp)).trans (hs.fixedPointers q hq)
  · rw [h13,hs.output]
    push_cast
    ring
  · rw [h14,hs.counter]
    push_cast
    ring
  · rw [ht7,hm]
    have hlen : ((DenseEnumeration.digits (cyclicIndex d p (r+1))).map (fun a : ℕ => (a : ℝ))).length=d := by simp
    rw [readArray_write_after _ _ _ _ _ hin]
    rw [readArray_update_after _ _ _ _ _ (by omega)]
    exact hs.input
  · rw [ht9,hm]
    have hlen : ((DenseEnumeration.digits (cyclicIndex d p (r+1))).map (fun a : ℕ => (a : ℝ))).length=d := by simp
    simpa only [hlen] using readArray_writeArray
      (Function.update s.mem (s.ptrs 13) (hermite d (fun i => ((cyclicIndex d p r).val i).val) x))
      (s.ptrs 9) ((DenseEnumeration.digits (cyclicIndex d p (r+1))).map (fun a : ℕ => (a : ℝ)))
  · exact h20
  · exact h21
  · intro i hi
    have hExp : s.ptrs 9+(d : ℤ) ≤ s₀.ptrs 13+(i : ℤ) := by rw [hp9]; omega
    rw [hm,writeArray_outside _ _ _ _ (Or.inr (by simpa using hExp))]
    rcases Nat.lt_or_eq_of_le (show i ≤ r by omega) with hir|hir
    · rw [Function.update_of_ne (by rw [hs.output]; omega)]
      exact hs.written i hir
    · subst i
      rw [← hs.output]
      simp
  · intro z hzExp hzOut
    rw [hm,writeArray_outside _ _ _ z (by simpa [hp9] using hzExp),
      Function.update_of_ne (by rw [hs.output]; push_cast at hzOut; omega)]
    apply hs.frame z hzExp
    push_cast at hzOut
    omega
lemma feature_loop_correct (ω : PolySampIso.Streams) (d p : ℕ) (x : Vec d) (s : Store)
    (hd : s.ptrs 0=d) (hD : s.ptrs 15=featureDimension d p) (hc : s.ptrs 14=1)
    (hx : readArray s.mem (s.ptrs 7) d=List.ofFn (fun i => x i))
    (hκ : readArray s.mem (s.ptrs 9) d=List.replicate d 0) (htotal : s.regs 20=0) (hbudget : s.regs 21=p)
    (hinput : s.ptrs 7+(d : ℤ) ≤ s.ptrs 9) (houtput : s.ptrs 9+(d : ℤ) ≤ s.ptrs 13) :
    ∃ t k, k ≤ 2+featureDimension d p*(30+30*d+11*p) ∧ Eval ω featureLoop s t k ∧
      readArray t.mem (s.ptrs 13) (featureDimension d p)=orderedFeatures d p x ∧
      readArray t.mem (s.ptrs 9) d=List.replicate d 0 ∧
      t.ptrs 13=s.ptrs 13+(featureDimension d p : ℤ) ∧ t.regs 20=0 ∧
      readArray t.mem (s.ptrs 7) d=List.ofFn (fun i => x i) ∧
      (∀ z, (z < s.ptrs 9 ∨ s.ptrs 9+(d : ℤ) ≤ z) →
        (z < s.ptrs 13 ∨ s.ptrs 13+(featureDimension d p : ℤ) ≤ z) → t.mem z=s.mem z) ∧
      (∀ q, q ∉ ({3,4,10,11,12,13,14} : Finset ℕ) → t.ptrs q=s.ptrs q) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  let Inv := FeatureInvariant d p x s
  have hinit : Inv 0 s := by
    constructor
    · intro q hq; rfl
    · simp
    · simpa using hc
    · exact hx
    · simpa [cyclicIndex_zero] using hκ
    · simpa [cyclicIndex_zero] using htotal
    · exact hbudget
    · intro i hi; omega
    · intro z hz1 hz2; rfl
  have htrue (i : ℕ) (hi : i < featureDimension d p) (u : Store) (hu : Inv i u) : Test.holds u (.pointer 14 15) := by
    change u.ptrs 14 ≤ u.ptrs 15
    rw [hu.counter,hu.fixedPointers 15 (by simp),hD]
    omega
  have hfalse (u : Store) (hu : Inv (featureDimension d p) u) : ¬Test.holds u (.pointer 14 15) := by
    change ¬u.ptrs 14 ≤ u.ptrs 15
    rw [hu.counter,hu.fixedPointers 15 (by simp),hD]
    omega
  obtain ⟨t,k,hk,he,ht⟩ := eval_loop_invariant ω (.pointer 14 15) featureBody (featureDimension d p)
    (28+30*d+11*p) Inv htrue hfalse
    (fun i hi u hu => feature_invariant_step ω d p x s hd hinput houtput i hi u hu) s hinit
  have hcg := he.cursors_preserved (by decide)
  refine ⟨t,k,by nlinarith only [hk],he,?_,?_,ht.output,?_,?_,ht.frame,?_,hcg.1,hcg.2⟩
  · apply List.ext_getElem
    · simp [readArray,orderedFeatures]
    · intro i hi hj
      simp only [readArray,orderedFeatures,List.getElem_ofFn]
      apply ht.written
      simpa [orderedFeatures] using hj
  · have hh := ht.digits
    rw [ht.fixedPointers 9 (by simp)] at hh
    simpa [cyclicIndex_end] using hh
  · simpa [cyclicIndex_end] using ht.total
  · have hh := ht.input
    rw [ht.fixedPointers 7 (by simp)] at hh
    exact hh
  · intro q hq
    apply he.pointer_preserved
    simp [featureLoop,featureBody,featureReset,featureStore,tensorCommand,tensorLoop,tensorBody,
      hermiteCommand,hermiteInit,hermiteStep,hermiteFinish,tensorPrefix,tensorSuffix,
      indexSuccessorCommand,indexSuccessorLoop,indexSuccessorBody,indexSuccessorInit,indexSuccessorPrefix,
      indexSuccessorYes,indexSuccessorNo,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM

namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma orderedFeatures_isometry (d p : ℕ) (x : Vec d) :
    orderedFeatures d p x=List.ofFn (fun i => (coefficientIsometry d p (features d p x)) i) := by
  unfold orderedFeatures
  congr 1
  funext i
  rw [cyclicIndex_of_fin]
  exact (coefficientIsometry_feature d p x i).symm
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMDotProduct
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
noncomputable def dotValue (xs ys : List ℝ) : ℝ := (List.zipWith (fun x y => x*y) xs ys).sum
def dotStep : List Op := [.load 0 3,.load 1 4,.mul 0 0 1,.add 31 31 0,.pinc 3,.pinc 4,.pinc 12]
def dotLoop : Cmd := .loop (.pointer 12 15) (.block dotStep)
def dotCommand : Cmd := .seq (.block [.literal 31 0,.pset 12 1]) dotLoop
lemma dot_loop_correct (ω : PolySampIso.Streams) (xs ys : List ℝ) (hlen : ys.length=xs.length)
    (s : Store) (hbound : s.ptrs 12+(xs.length : ℤ)=s.ptrs 15+1)
    (hx : readArray s.mem (s.ptrs 3) xs.length=xs) (hy : readArray s.mem (s.ptrs 4) ys.length=ys) :
    ∃ t, Eval ω dotLoop s t (2+9*xs.length) ∧
      t.regs 31=s.regs 31+dotValue xs ys ∧ t.mem=s.mem ∧
      t.ptrs 3=s.ptrs 3+(xs.length : ℤ) ∧ t.ptrs 4=s.ptrs 4+(xs.length : ℤ) := by
  induction xs generalizing ys s with
  | nil =>
    have hh : ys=[] := List.length_eq_zero_iff.mp hlen
    subst ys
    refine ⟨s,Eval.loop_done ?_,?_,rfl,?_,?_⟩
    · change ¬s.ptrs 12 ≤ s.ptrs 15
      simp only [List.length_nil,Nat.cast_zero,add_zero] at hbound
      omega
    · simp [dotValue]
    · simp
    · simp
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : ys.length=xs.length := by simpa using hlen
      have hx' : s.mem (s.ptrs 3)=x ∧ readArray s.mem (s.ptrs 3+1) xs.length=xs := by
        simpa only [List.length_cons,readArray_cons,List.cons.injEq] using hx
      have hy' : s.mem (s.ptrs 4)=y ∧ readArray s.mem (s.ptrs 4+1) ys.length=ys := by
        simpa only [List.length_cons,readArray_cons,List.cons.injEq] using hy
      have hhead : Test.holds s (.pointer 12 15) := by
        change s.ptrs 12 ≤ s.ptrs 15
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
        omega
      let u := blockAct ω dotStep s
      have hu : Eval ω (.block dotStep) s u 7 := eval_block ω dotStep s
      have humem : u.mem=s.mem := rfl
      have huptr : u.ptrs=Function.update (Function.update (Function.update s.ptrs 3 (s.ptrs 3+1)) 4 (s.ptrs 4+1)) 12 (s.ptrs 12+1) := by
        simp [u,blockAct,dotStep,Op.act]
      have hu31 : u.regs 31=s.regs 31+x*y := by simp [u,blockAct,dotStep,Op.act,hx'.1,hy'.1]
      have hub : u.ptrs 12+(xs.length : ℤ)=u.ptrs 15+1 := by
        simp only [huptr,Function.update_apply]
        norm_num
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
        omega
      obtain ⟨t,he,h31,hm,h3,h4⟩ := ih ys hlen' u hub
        (by simpa [humem,huptr] using hx'.2) (by simpa [humem,huptr] using hy'.2)
      have hall := Eval.loop_step hhead hu he
      refine ⟨t,?_,?_,hm.trans humem,?_,?_⟩
      · convert! hall using 1 <;> simp only [List.length_cons] <;> omega
      · rw [h31,hu31]
        simp only [dotValue,List.zipWith_cons_cons,List.sum_cons]
        ring
      · rw [h3,huptr]
        norm_num
        ring
      · rw [h4,huptr]
        norm_num
        ring
lemma dotValue_ofFn (D : ℕ) (x y : Vec D) : dotValue (List.ofFn (fun i => x i)) (List.ofFn (fun i => y i))=inner ℝ x y := by
  have hz : List.zipWith (fun x y : ℝ => x*y) (List.ofFn (fun i => x i)) (List.ofFn (fun i => y i))=
      List.ofFn (fun i => x i*y i) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  simp only [dotValue,hz,List.sum_ofFn,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  simp [mul_comm]
lemma dot_command_correct (ω : PolySampIso.Streams) (D : ℕ) (x y : Vec D) (s : Store)
    (hD : s.ptrs 15=D) (hx : readArray s.mem (s.ptrs 3) D=List.ofFn (fun i => x i))
    (hy : readArray s.mem (s.ptrs 4) D=List.ofFn (fun i => y i)) :
    ∃ t, Eval ω dotCommand s t (4+9*D) ∧ t.regs 31=inner ℝ x y ∧ t.mem=s.mem ∧
      t.ptrs 3=s.ptrs 3+D ∧ t.ptrs 4=s.ptrs 4+D ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω [.literal 31 0,.pset 12 1] s
  have hu : Eval ω (.block [.literal 31 0,.pset 12 1]) s u 2 := eval_block ω _ s
  have humem : u.mem=s.mem := rfl
  have hu3 : u.ptrs 3=s.ptrs 3 := by simp [u,blockAct,Op.act]
  have hu4 : u.ptrs 4=s.ptrs 4 := by simp [u,blockAct,Op.act]
  have hub : u.ptrs 12+((List.ofFn (fun i => x i)).length : ℤ)=u.ptrs 15+1 := by simp [u,blockAct,Op.act,hD,add_comm]
  obtain ⟨t,he,h31,hm,h3,h4⟩ := dot_loop_correct ω (List.ofFn (fun i => x i)) (List.ofFn (fun i => y i))
    (by simp) u hub (by simpa [humem,hu3] using hx) (by simpa [humem,hu4] using hy)
  have hall : Eval ω dotCommand s t (4+9*D) := by
    convert! Eval.seq hu he using 1 <;> simp <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,?_,hm.trans humem,?_,?_,hc.1,hc.2,?_,?_⟩
  · rw [h31]
    have hu31 : u.regs 31=0 := by simp [u,blockAct,Op.act]
    rw [hu31,zero_add,dotValue_ofFn]
  · simpa only [List.length_ofFn,hu3] using h3
  · simpa only [List.length_ofFn,hu4] using h4
  · intro r hr
    apply hall.register_preserved
    simp [dotCommand,dotLoop,dotStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [dotCommand,dotLoop,dotStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMScaleArray
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def scaleStep : List Op := [.load 0 3,.mul 0 0 32,.store 3 0,.pinc 3,.pinc 12]
def scaleLoop : Cmd := .loop (.pointer 12 15) (.block scaleStep)
def scaleCommand : Cmd := .seq (.atom (.pset 12 1)) scaleLoop
lemma scale_loop_correct (ω : PolySampIso.Streams) (xs : List ℝ) (s : Store)
    (hbound : s.ptrs 12+(xs.length : ℤ)=s.ptrs 15+1) (hx : readArray s.mem (s.ptrs 3) xs.length=xs) :
    ∃ t, Eval ω scaleLoop s t (2+7*xs.length) ∧
      t.mem=writeArray s.mem (s.ptrs 3) (xs.map (fun x : ℝ => x*s.regs 32)) ∧
      t.ptrs 3=s.ptrs 3+(xs.length : ℤ) ∧ t.regs 32=s.regs 32 := by
  induction xs generalizing s with
  | nil =>
    refine ⟨s,Eval.loop_done ?_,rfl,by simp,rfl⟩
    change ¬s.ptrs 12 ≤ s.ptrs 15
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hbound
    omega
  | cons x xs ih =>
    have hx' : s.mem (s.ptrs 3)=x ∧ readArray s.mem (s.ptrs 3+1) xs.length=xs := by
      simpa only [List.length_cons,readArray_cons,List.cons.injEq] using hx
    have hhead : Test.holds s (.pointer 12 15) := by
      change s.ptrs 12 ≤ s.ptrs 15
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
      omega
    let u := blockAct ω scaleStep s
    have hu : Eval ω (.block scaleStep) s u 5 := eval_block ω scaleStep s
    have humem : u.mem=Function.update s.mem (s.ptrs 3) (x*s.regs 32) := by simp [u,blockAct,scaleStep,Op.act,hx'.1]
    have huptr : u.ptrs=Function.update (Function.update s.ptrs 3 (s.ptrs 3+1)) 12 (s.ptrs 12+1) := by simp [u,blockAct,scaleStep,Op.act]
    have hub : u.ptrs 12+(xs.length : ℤ)=u.ptrs 15+1 := by
      simp only [huptr,Function.update_apply]
      norm_num
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
      omega
    have hux : readArray u.mem (u.ptrs 3) xs.length=xs := by
      simp only [humem,huptr,Function.update_apply]
      norm_num
      rw [readArray_update_before _ _ _ _ _ (by omega)]
      exact hx'.2
    obtain ⟨t,he,hm,h3,h32⟩ := ih u hub hux
    have hall := Eval.loop_step hhead hu he
    refine ⟨t,?_,?_,?_,h32⟩
    · convert! hall using 1 <;> simp only [List.length_cons] <;> omega
    · rw [hm,humem,huptr]
      norm_num
      rw [writeArray_cons_sequential]
      rfl
    · rw [h3,huptr]
      norm_num
      push_cast
      ring
lemma scale_command_correct (ω : PolySampIso.Streams) (xs : List ℝ) (s : Store) (hn : s.ptrs 15=xs.length)
    (hx : readArray s.mem (s.ptrs 3) xs.length=xs) :
    ∃ t, Eval ω scaleCommand s t (3+7*xs.length) ∧
      t.mem=writeArray s.mem (s.ptrs 3) (xs.map (fun x : ℝ => x*s.regs 32)) ∧
      t.ptrs 3=s.ptrs 3+(xs.length : ℤ) ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 0 → t.regs r=s.regs r) ∧ (∀ q, q ≠ 3 → q ≠ 12 → t.ptrs q=s.ptrs q) := by
  let u := Op.act ω s (.pset 12 1)
  have hu : Eval ω (.atom (.pset 12 1)) s u 1 := Eval.atom s _
  have hub : u.ptrs 12+(xs.length : ℤ)=u.ptrs 15+1 := by simp [u,Op.act,hn,add_comm]
  obtain ⟨t,he,hm,h3,h32⟩ := scale_loop_correct ω xs u hub (by simpa [u,Op.act] using hx)
  have hall : Eval ω scaleCommand s t (3+7*xs.length) := by convert! Eval.seq hu he using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,?_,?_,hc.1,hc.2,?_,?_⟩
  · simpa [u,Op.act] using hm
  · simpa [u,Op.act] using h3
  · intro r hr
    apply hall.register_preserved
    simp [scaleCommand,scaleLoop,scaleStep,Cmd.block,Cmd.registers,Op.registers,hr]
  · intro q hq3 hq12
    apply hall.pointer_preserved
    simp [scaleCommand,scaleLoop,scaleStep,Cmd.block,Cmd.pointers,Op.pointers,hq3,hq12]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMRadialClip
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def clipPrefix : List Op := [.pcopy 3 6,.pcopy 4 6]
def clipNorm : List Op := [.sqrt 31 31,.literal 32 1,.sub 0 31 34]
def clipFactor : Cmd := .cond (.real 0) .skip (.block [.div 32 34 31])
def clipCommand : Cmd := .seq (.block clipPrefix) (.seq dotCommand
  (.seq (.block clipNorm) (.seq clipFactor (.seq (.atom (.pcopy 3 6)) scaleCommand))))
noncomputable def radialClip {D : ℕ} (T : ℝ) (x : Vec D) : Vec D := (T/max T ‖x‖) • x
lemma clip_command_correct (ω : PolySampIso.Streams) (D : ℕ) (T : ℝ) (hT : 0 < T) (x : Vec D) (s : Store)
    (hTs : s.regs 34=T)
    (hD : s.ptrs 15=D) (hx : readArray s.mem (s.ptrs 6) D=List.ofFn (fun i => x i)) :
    ∃ t k, k ≤ 16+16*D ∧ Eval ω clipCommand s t k ∧
      t.mem=writeArray s.mem (s.ptrs 6) (List.ofFn (fun i => (radialClip T x) i)) ∧
      t.regs 31=‖x‖ ∧ t.regs 32=T/max T ‖x‖ ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31,32} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω clipPrefix s
  have hu : Eval ω (.block clipPrefix) s u 2 := eval_block ω clipPrefix s
  have humem : u.mem=s.mem := rfl
  have hu15 : u.ptrs 15=D := by simpa [u,blockAct,clipPrefix,Op.act] using hD
  have hu3 : u.ptrs 3=s.ptrs 6 := by simp [u,blockAct,clipPrefix,Op.act]
  have hu4 : u.ptrs 4=s.ptrs 6 := by simp [u,blockAct,clipPrefix,Op.act]
  obtain ⟨v,hv,h31,hmem,h3,h4,hgc,hec,hreg,hptr⟩ := dot_command_correct ω D x x u hu15
    (by simpa only [humem,hu3] using hx) (by simpa only [humem,hu4] using hx)
  have hv34 : v.regs 34=T := by
    rw [hreg 34 (by simp)]
    exact hTs
  let w := blockAct ω clipNorm v
  have hw : Eval ω (.block clipNorm) v w 3 := eval_block ω clipNorm v
  have hw31 : w.regs 31=‖x‖ := by
    simp [w,blockAct,clipNorm,Op.act,h31,hv34,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg x)]
  have hw34 : w.regs 34=T := hv34
  have hw32 : w.regs 32=1 := by simp [w,blockAct,clipNorm,Op.act]
  have hw0 : w.regs 0=‖x‖-T := by
    simp [w,blockAct,clipNorm,Op.act,h31,hv34,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg x)]
  have hfactor : ∃ z k, k ≤ 3 ∧ Eval ω clipFactor w z k ∧ z.mem=w.mem ∧ z.ptrs=w.ptrs ∧
      z.regs 32=T/max T ‖x‖ := by
    by_cases hnorm : ‖x‖ ≤ T
    · refine ⟨w,1,by omega,Eval.cond_yes (no := .block [.div 32 34 31]) ?_ (Eval.skip w),rfl,rfl,?_⟩
      · change w.regs 0 ≤ 0
        rw [hw0]
        linarith
      · rw [hw32,max_eq_left hnorm,div_self hT.ne']
    · let z := blockAct ω [.div 32 34 31] w
      have he : Eval ω (.block [.div 32 34 31]) w z 1 := eval_block ω _ w
      refine ⟨z,3,by omega,Eval.cond_no (yes := .skip) ?_ he,rfl,rfl,?_⟩
      · change ¬w.regs 0 ≤ 0
        rw [hw0]
        linarith
      · simp [z,blockAct,Op.act,hw32,hw31,hw34,max_eq_right (by linarith : T ≤ ‖x‖)]
  obtain ⟨z,k,hk,hz,hzmem,hzptr,hz32⟩ := hfactor
  let a := Op.act ω z (.pcopy 3 6)
  have ha : Eval ω (.atom (.pcopy 3 6)) z a 1 := Eval.atom z _
  have hmemw : w.mem=s.mem := hmem.trans humem
  have hmema : a.mem=s.mem := hzmem.trans hmemw
  have hp6 : z.ptrs 6=s.ptrs 6 := by
    rw [hzptr]
    change v.ptrs 6=s.ptrs 6
    rw [hptr 6 (by simp)]
    simp [u,blockAct,clipPrefix,Op.act]
  have ha3 : a.ptrs 3=s.ptrs 6 := by simp [a,Op.act,hp6]
  have ha15 : a.ptrs 15=(List.ofFn (fun i => x i)).length := by
    simp only [List.length_ofFn]
    change z.ptrs 15=(D : ℤ)
    rw [hzptr]
    change v.ptrs 15=(D : ℤ)
    rw [hptr 15 (by simp)]
    exact hu15
  obtain ⟨t,ht,htmem,ht3,htgc,htec,htreg,htptr⟩ := scale_command_correct ω (List.ofFn (fun i => x i)) a ha15
    (by simpa only [List.length_ofFn,hmema,ha3] using hx)
  have hall : Eval ω clipCommand s t (2+(4+9*D)+(3+(k+(1+(3+7*D))))) := by
    convert! Eval.seq hu (Eval.seq hv (Eval.seq hw (Eval.seq hz (Eval.seq ha ht)))) using 1 <;> simp <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,2+(4+9*D)+(3+(k+(1+(3+7*D)))),by omega,hall,?_,?_,?_,hc.1,hc.2,?_,?_⟩
  · rw [htmem,hmema,ha3]
    congr 1
    simp only [List.map_ofFn,radialClip,PiLp.smul_apply,smul_eq_mul]
    have ha32 : a.regs 32=T/max T ‖x‖ := hz32
    simp only [ha32]
    congr 1
    funext i
    simp [Function.comp_apply,mul_comm]
  · rw [htreg 31 (by omega)]
    change z.regs 31=‖x‖
    rw [hz.register_preserved (r := 31) (by decide)]
    exact hw31
  · rw [htreg 32 (by omega)]
    exact hz32
  · intro r hr
    apply hall.register_preserved
    simp [clipCommand,clipPrefix,clipNorm,clipFactor,dotCommand,dotLoop,dotStep,
      scaleCommand,scaleLoop,scaleStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [clipCommand,clipPrefix,clipNorm,clipFactor,dotCommand,dotLoop,dotStep,
      scaleCommand,scaleLoop,scaleStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPointFeatures
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma radialClip_features (d p : ℕ) (x : Vec d) :
    radialClip (radius d p) (coefficientIsometry d p (features d p x))=coefficientIsometry d p (clipped d p x) := by
  unfold radialClip clipped clipScale
  rw [(coefficientIsometry d p).map_smul,(coefficientIsometry d p).norm_map]
def pointFeaturesCommand : Cmd := .seq (.atom (.pcopy 6 13)) (.seq featureLoop clipCommand)
lemma point_features_command_correct (ω : PolySampIso.Streams) (d p : ℕ) (x : Vec d) (s : Store)
    (hd : s.ptrs 0=d) (hD : s.ptrs 15=featureDimension d p) (hc : s.ptrs 14=1)
    (hx : readArray s.mem (s.ptrs 7) d=List.ofFn (fun i => x i))
    (hκ : readArray s.mem (s.ptrs 9) d=List.replicate d 0) (htotal : s.regs 20=0) (hbudget : s.regs 21=p)
    (hT : s.regs 34=radius d p) (hinput : s.ptrs 7+(d : ℤ) ≤ s.ptrs 9)
    (houtput : s.ptrs 9+(d : ℤ) ≤ s.ptrs 13) :
    ∃ t k, k ≤ 100*featureDimension d p*(d+p+1) ∧ Eval ω pointFeaturesCommand s t k ∧
      readArray t.mem (s.ptrs 13) (featureDimension d p)=
        List.ofFn (fun i => (coefficientIsometry d p (clipped d p x)) i) ∧
      readArray t.mem (s.ptrs 9) d=List.replicate d 0 ∧
      readArray t.mem (s.ptrs 7) d=List.ofFn (fun i => x i) ∧
      t.ptrs 13=s.ptrs 13+(featureDimension d p : ℤ) ∧
      t.regs 20=0 ∧ t.regs 21=p ∧ t.regs 34=radius d p ∧
      t.regs 31=‖features d p x‖ ∧ t.regs 32=clipScale d p x ∧
      (∀ z, (z < s.ptrs 9 ∨ s.ptrs 9+(d : ℤ) ≤ z) →
        (z < s.ptrs 13 ∨ s.ptrs 13+(featureDimension d p : ℤ) ≤ z) → t.mem z=s.mem z) ∧
      (∀ q, q ∉ ({3,4,6,10,11,12,13,14} : Finset ℕ) → t.ptrs q=s.ptrs q) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  let u := Op.act ω s (.pcopy 6 13)
  have hu : Eval ω (.atom (.pcopy 6 13)) s u 1 := Eval.atom s _
  have humem : u.mem=s.mem := rfl
  have hu6 : u.ptrs 6=s.ptrs 13 := by simp [u,Op.act]
  obtain ⟨v,k,hk,hv,harray,hzeros,h13,h20,hxs,hframe,hptr,hgc,hec⟩ := feature_loop_correct ω d p x u
    (by simpa [u,Op.act] using hd) (by simpa [u,Op.act] using hD) (by simpa [u,Op.act] using hc)
    (by simpa [u,Op.act] using hx) (by simpa [u,Op.act] using hκ) htotal hbudget
    (by simpa [u,Op.act] using hinput) (by simpa [u,Op.act] using houtput)
  have hv6 : v.ptrs 6=s.ptrs 13 := (hptr 6 (by simp)).trans hu6
  have hv15 : v.ptrs 15=featureDimension d p := by rw [hptr 15 (by simp)]; simpa [u,Op.act] using hD
  have hv34 : v.regs 34=radius d p := by rw [hv.register_preserved (r := 34) (by decide)]; exact hT
  have hv21 : v.regs 21=p := by rw [hv.register_preserved (r := 21) (by decide)]; exact hbudget
  have hv9 : v.ptrs 9=s.ptrs 9 := by rw [hptr 9 (by simp)]; simp [u,Op.act]
  have hv7 : v.ptrs 7=s.ptrs 7 := by rw [hptr 7 (by simp)]; simp [u,Op.act]
  have hinputV : readArray v.mem (v.ptrs 6) (featureDimension d p)=
      List.ofFn (fun i => (coefficientIsometry d p (features d p x)) i) := by
    rw [hv6]
    simpa only [u,Op.act,Function.update_of_ne (by norm_num : (13 : ℕ) ≠ 6),orderedFeatures_isometry] using harray
  obtain ⟨t,l,hl,ht,hm,ht31,ht32,htgc,htec,htreg,htptr⟩ := clip_command_correct ω (featureDimension d p)
    (radius d p) (RegressionGeometry.radius_pos d p) (coefficientIsometry d p (features d p x)) v hv34 hv15 hinputV
  have hall : Eval ω pointFeaturesCommand s t (1+(k+l)) := Eval.seq hu (Eval.seq hv ht)
  have hcg := hall.cursors_preserved (by decide)
  have hnorm : ‖coefficientIsometry d p (features d p x)‖=‖features d p x‖ := (coefficientIsometry d p).norm_map _
  have hcard : 1 ≤ featureDimension d p := RegressionGeometry.featureDimension_pos d p
  refine ⟨t,1+(k+l),?_,hall,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hcg.1,hcg.2⟩
  · nlinarith only [hk,hl,hcard]
  · rw [hm,hv6,radialClip_features]
    simpa only [List.length_ofFn] using readArray_writeArray v.mem (s.ptrs 13)
      (List.ofFn (fun i => (coefficientIsometry d p (clipped d p x)) i))
  · rw [hm,hv6,readArray_write_after _ _ _ _ _ houtput]
    simpa [u,Op.act] using hzeros
  · rw [hm,hv6,readArray_write_after _ _ _ _ _ (by omega)]
    simpa [u,Op.act] using hxs
  · rw [htptr 13 (by simp),h13]
    simp [u,Op.act]
  · rw [htreg 20 (by simp)]
    exact h20
  · rw [htreg 21 (by simp)]
    exact hv21
  · rw [htreg 34 (by simp)]
    exact hv34
  · simpa only [hnorm] using ht31
  · simpa only [hnorm,clipScale] using ht32
  · intro z hzExp hzOut
    rw [hm,hv6,writeArray_outside _ _ _ z (by simpa using hzOut)]
    simpa [u,Op.act] using hframe z (by simpa [u,Op.act] using hzExp) (by simpa [u,Op.act] using hzOut)
  · intro q hq
    apply hall.pointer_preserved
    simp [pointFeaturesCommand,featureLoop,featureBody,featureReset,featureStore,tensorCommand,tensorLoop,tensorBody,
      hermiteCommand,hermiteInit,hermiteStep,hermiteFinish,tensorPrefix,tensorSuffix,
      indexSuccessorCommand,indexSuccessorLoop,indexSuccessorBody,indexSuccessorInit,indexSuccessorPrefix,indexSuccessorYes,indexSuccessorNo,
      clipCommand,clipPrefix,clipNorm,clipFactor,dotCommand,dotLoop,dotStep,scaleCommand,scaleLoop,scaleStep,
      Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMRowMetadata
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def rowMetadata : List Op := [.load 0 7,.store 13 0,.pinc 13,.mul 0 31 32,
  .store 13 0,.pinc 13,.pinc 7,.pinc 16]
lemma row_metadata_correct (ω : PolySampIso.Streams) (s : Store) :
    let t := blockAct ω rowMetadata s
    Eval ω (.block rowMetadata) s t 8 ∧
      t.mem=Function.update (Function.update s.mem (s.ptrs 13) (s.mem (s.ptrs 7)))
        (s.ptrs 13+1) (s.regs 31*s.regs 32) ∧
      t.ptrs 13=s.ptrs 13+2 ∧ t.ptrs 7=s.ptrs 7+1 ∧ t.ptrs 16=s.ptrs 16+1 ∧
      (∀ r, r ≠ 0 → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({7,13,16} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let t := blockAct ω rowMetadata s
  have he : Eval ω (.block rowMetadata) s t 8 := eval_block ω rowMetadata s
  refine ⟨he,?_,?_,?_,?_,?_,?_⟩
  · simp [t,blockAct,rowMetadata,Op.act]
  · simp [t,blockAct,rowMetadata,Op.act]
    ring
  · simp [t,blockAct,rowMetadata,Op.act]
  · simp [t,blockAct,rowMetadata,Op.act]
  · intro r hr
    exact he.register_preserved (by simp [Cmd.block,rowMetadata,Cmd.registers,Op.registers,hr])
  · intro q hq
    apply he.pointer_preserved
    simp [Cmd.block,rowMetadata,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
lemma row_metadata_array (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ) (a b : ℝ)
    (hx : readArray mem base xs.length=xs) :
    readArray (Function.update (Function.update mem (base+(xs.length : ℤ)) a) (base+(xs.length : ℤ)+1) b)
      base (xs.length+2)=xs++[a,b] := by
  rw [readArray_append]
  have hfront : readArray (Function.update (Function.update mem (base+(xs.length : ℤ)) a)
      (base+(xs.length : ℤ)+1) b) base xs.length=xs := by
    rw [readArray_update_after _ _ _ _ _ (by omega),readArray_update_after _ _ _ _ _ (by omega)]
    exact hx
  rw [hfront]
  congr 1
  have hne : base+(xs.length : ℤ) ≠ base+(xs.length : ℤ)+1 := by omega
  simp [readArray,List.ofFn_succ,Function.update_apply,hne,Ne.symm hne]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPackedRow
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
noncomputable def encodedRow (d p : ℕ) (x : Vec d) (y : Bool) : List ℝ :=
  List.ofFn (fun i => (coefficientIsometry d p (clipped d p x)) i)++[label y,‖clipped d p x‖]
def packedRowCommand : Cmd := .seq (.atom (.pset 14 1)) (.seq pointFeaturesCommand
  (.seq (advanceCommand 7 0) (.block rowMetadata)))
lemma packed_row_command_correct (ω : PolySampIso.Streams) (d p : ℕ) (x : Vec d) (y : Bool) (s : Store)
    (hd : s.ptrs 0=d) (hD : s.ptrs 15=featureDimension d p)
    (hx : readArray s.mem (s.ptrs 7) d=List.ofFn (fun i => x i)) (hy : s.mem (s.ptrs 7+d)=label y)
    (hκ : readArray s.mem (s.ptrs 9) d=List.replicate d 0) (htotal : s.regs 20=0) (hbudget : s.regs 21=p)
    (hT : s.regs 34=radius d p) (hinput : s.ptrs 7+(d : ℤ)+1 ≤ s.ptrs 9)
    (houtput : s.ptrs 9+(d : ℤ) ≤ s.ptrs 13) :
    ∃ t k, k ≤ 120*featureDimension d p*(d+p+1) ∧ Eval ω packedRowCommand s t k ∧
      readArray t.mem (s.ptrs 13) (featureDimension d p+2)=encodedRow d p x y ∧
      readArray t.mem (s.ptrs 9) d=List.replicate d 0 ∧ t.regs 20=0 ∧ t.regs 21=p ∧ t.regs 34=radius d p ∧
      t.ptrs 7=s.ptrs 7+(d : ℤ)+1 ∧ t.ptrs 13=s.ptrs 13+(featureDimension d p : ℤ)+2 ∧ t.ptrs 16=s.ptrs 16+1 ∧
      (∀ z, (z < s.ptrs 9 ∨ s.ptrs 9+(d : ℤ) ≤ z) →
        (z < s.ptrs 13 ∨ s.ptrs 13+((featureDimension d p+2 : ℕ) : ℤ) ≤ z) → t.mem z=s.mem z) ∧
      (∀ q, q ∉ ({3,4,6,7,10,11,12,13,14,16} : Finset ℕ) → t.ptrs q=s.ptrs q) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  let u := Op.act ω s (.pset 14 1)
  have hu : Eval ω (.atom (.pset 14 1)) s u 1 := Eval.atom s _
  obtain ⟨v,k,hk,hv,hfeat,hzero,hxv,h13,h20,h21,h34,h31,h32,hframe,hptr,hgc,hec⟩ := point_features_command_correct ω d p x u
    (by simpa [u,Op.act] using hd) (by simpa [u,Op.act] using hD) (by simp [u,Op.act])
    (by simpa [u,Op.act] using hx) (by simpa [u,Op.act] using hκ) htotal hbudget hT
    (by simp [u,Op.act]; omega) (by simpa [u,Op.act] using houtput)
  have hv0 : v.ptrs 0=d := by rw [hptr 0 (by simp)]; simpa [u,Op.act] using hd
  have hv7 : v.ptrs 7=s.ptrs 7 := by rw [hptr 7 (by simp)]; simp [u,Op.act]
  have hv13 : v.ptrs 13=s.ptrs 13+(featureDimension d p : ℤ) := by simpa [u,Op.act] using h13
  have hv16 : v.ptrs 16=s.ptrs 16 := by rw [hptr 16 (by simp)]; simp [u,Op.act]
  have hvlabel : v.mem (s.ptrs 7+(d : ℤ))=label y := by
    have hh := hframe (s.ptrs 7+(d : ℤ)) (Or.inl (by simp [u,Op.act]; omega)) (Or.inl (by simp [u,Op.act]; omega))
    exact hh.trans hy
  obtain ⟨w,hw,h7,hwm,hwregs,hwgc,hwec,hwptr⟩ := advance_command_correct ω 7 0 d (by omega) (by omega) (by omega) v hv0
  have hw7 : w.ptrs 7=s.ptrs 7+(d : ℤ) := by simpa only [hv7] using h7
  have hw13 : w.ptrs 13=s.ptrs 13+(featureDimension d p : ℤ) := by rw [hwptr 13 (by omega) (by omega)]; exact hv13
  have hw16 : w.ptrs 16=s.ptrs 16 := by rw [hwptr 16 (by omega) (by omega)]; exact hv16
  have hwlabel : w.mem (w.ptrs 7)=label y := by rw [hwm,hw7,hvlabel]
  have hwnorm : w.regs 31*w.regs 32=‖clipped d p x‖ := by
    rw [hwregs,h31,h32,clipped,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (RegressionGeometry.clipScale_bounds d p x).1]
    ring
  let t := blockAct ω rowMetadata w
  obtain ⟨ht,hm,ht13,ht7,ht16,htregs,htptr⟩ := row_metadata_correct ω w
  have hall : Eval ω packedRowCommand s t (1+(k+((3+4*d)+8))) := Eval.seq hu (Eval.seq hv (Eval.seq hw ht))
  have hcg := hall.cursors_preserved (by decide)
  have hcard : 1 ≤ featureDimension d p := RegressionGeometry.featureDimension_pos d p
  refine ⟨t,1+(k+((3+4*d)+8)),?_,hall,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hcg.1,hcg.2⟩
  · have hmul := Nat.mul_le_mul_right (d+p+1) hcard
    nlinarith only [hk,hmul]
  · rw [hm,hw13,hwlabel,hwnorm]
    let xs := List.ofFn (fun i => (coefficientIsometry d p (clipped d p x)) i)
    have hread : readArray w.mem (s.ptrs 13) xs.length=xs := by simpa [xs,hwm,u,Op.act] using hfeat
    simpa [xs,encodedRow] using row_metadata_array w.mem (s.ptrs 13) xs (label y) ‖clipped d p x‖ hread
  · rw [hm,hw13,readArray_update_after _ _ _ _ _ (by omega),readArray_update_after _ _ _ _ _ (by omega),hwm]
    simpa [u,Op.act] using hzero
  · rw [htregs 20 (by omega),hwregs,h20]
  · rw [htregs 21 (by omega),hwregs,h21]
  · rw [htregs 34 (by omega),hwregs,h34]
  · rw [ht7,hw7]
  · rw [ht13,hw13]
  · rw [ht16,hw16]
  · intro z hzExp hzOut
    rw [hm,hw13,Function.update_of_ne (by push_cast at hzOut; omega),
      Function.update_of_ne (by push_cast at hzOut; omega),hwm]
    simpa [u,Op.act] using hframe z (by simpa [u,Op.act] using hzExp)
      (by simp [u,Op.act]; push_cast at hzOut; omega)
  · intro q hq
    apply hall.pointer_preserved
    simp [packedRowCommand,pointFeaturesCommand,featureLoop,featureBody,featureReset,featureStore,tensorCommand,tensorLoop,tensorBody,
      hermiteCommand,hermiteInit,hermiteStep,hermiteFinish,tensorPrefix,tensorSuffix,
      indexSuccessorCommand,indexSuccessorLoop,indexSuccessorBody,indexSuccessorInit,indexSuccessorPrefix,indexSuccessorYes,indexSuccessorNo,
      clipCommand,clipPrefix,clipNorm,clipFactor,dotCommand,dotLoop,dotStep,scaleCommand,scaleLoop,scaleStep,
      advanceCommand,advanceLoop,advanceStep,rowMetadata,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMDatasetInvariant
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
structure DatasetInvariant (d p N : ℕ) (S : Fin N → Example d) (s₀ : Store) (r : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ∈ ({0,9,15,17} : Finset ℕ) → s.ptrs q=s₀.ptrs q
  inputCursor : s.ptrs 7=s₀.ptrs 7+(r : ℤ)*((d : ℤ)+1)
  outputCursor : s.ptrs 13=s₀.ptrs 13+(r : ℤ)*((featureDimension d p : ℤ)+2)
  counter : s.ptrs 16=(r : ℤ)+1
  zeros : readArray s.mem (s.ptrs 9) d=List.replicate d 0
  total : s.regs 20=0
  budget : s.regs 21=p
  radius : s.regs 34=PrivateAgnosticHalfspace.Gaussian.radius d p
  written : ∀ j : Fin N, j.val < r →
    readArray s.mem (s₀.ptrs 13+(j.val : ℤ)*((featureDimension d p : ℤ)+2)) (featureDimension d p+2)=
      encodedRow d p (S j).1 (S j).2
  frame : ∀ z, (z < s₀.ptrs 9 ∨ s₀.ptrs 9+(d : ℤ) ≤ z) →
    (z < s₀.ptrs 13 ∨ s₀.ptrs 13+(r : ℤ)*((featureDimension d p : ℤ)+2) ≤ z) → s.mem z=s₀.mem z
lemma dataset_invariant_step (ω : PolySampIso.Streams) (d p N : ℕ) (S : Fin N → Example d) (s₀ : Store)
    (hd : s₀.ptrs 0=d) (hD : s₀.ptrs 15=featureDimension d p)
    (hinput : s₀.ptrs 7+(N : ℤ)*((d : ℤ)+1) ≤ s₀.ptrs 9) (houtput : s₀.ptrs 9+(d : ℤ) ≤ s₀.ptrs 13)
    (hxs : ∀ j : Fin N, readArray s₀.mem (s₀.ptrs 7+(j.val : ℤ)*((d : ℤ)+1)) d=List.ofFn (fun i => (S j).1 i))
    (hys : ∀ j : Fin N, s₀.mem (s₀.ptrs 7+(j.val : ℤ)*((d : ℤ)+1)+(d : ℤ))=label (S j).2)
    (r : ℕ) (hr : r < N) (s : Store) (hs : DatasetInvariant d p N S s₀ r s) :
    ∃ t k, k ≤ 120*featureDimension d p*(d+p+1) ∧ Eval ω packedRowCommand s t k ∧
      DatasetInvariant d p N S s₀ (r+1) t := by
  let j : Fin N := ⟨r,hr⟩
  have hp0 := hs.fixedPointers 0 (by simp)
  have hp9 := hs.fixedPointers 9 (by simp)
  have hp15 := hs.fixedPointers 15 (by simp)
  have hrowend : s.ptrs 7+(d : ℤ)+1 ≤ s₀.ptrs 9 := by
    rw [hs.inputCursor]
    have hm := mul_le_mul_of_nonneg_right (show (r : ℤ)+1 ≤ N by exact_mod_cast (show r+1 ≤ N by omega))
      (show (0 : ℤ) ≤ (d : ℤ)+1 by positivity)
    nlinarith only [hm,hinput]
  have hsameInput : readArray s.mem (s.ptrs 7) d=readArray s₀.mem (s.ptrs 7) d := by
    apply readArray_congr
    intro i hi
    apply hs.frame
    · left; omega
    · left; have hi' : (i : ℤ) < d := by exact_mod_cast hi
      omega
  have hx : readArray s.mem (s.ptrs 7) d=List.ofFn (fun i => (S j).1 i) := by
    rw [hsameInput,hs.inputCursor]
    exact hxs j
  have hy : s.mem (s.ptrs 7+d)=label (S j).2 := by
    rw [hs.frame _ (Or.inl (by omega)) (Or.inl (by omega)),hs.inputCursor]
    exact hys j
  have hrout : 0 ≤ (r : ℤ)*((featureDimension d p : ℤ)+2) := by positivity
  have hout : s.ptrs 9+(d : ℤ) ≤ s.ptrs 13 := by rw [hp9,hs.outputCursor]; omega
  obtain ⟨t,k,hk,he,hrow,hzeros,h20,h21,h34,h7,h13,h16,hframe,hptr,hgc,hec⟩ := packed_row_command_correct ω d p
    (S j).1 (S j).2 s (hp0.trans hd) (hp15.trans hD) hx hy hs.zeros hs.total hs.budget hs.radius
      (by rw [hp9]; exact hrowend) hout
  have ht9 : t.ptrs 9=s.ptrs 9 := hptr 9 (by simp)
  refine ⟨t,k,hk,he,?_⟩
  constructor
  · intro q hq
    exact (hptr q (by simp only [Finset.mem_insert,Finset.mem_singleton] at hq; rcases hq with rfl|rfl|rfl|rfl <;> simp)).trans (hs.fixedPointers q hq)
  · rw [h7,hs.inputCursor]
    push_cast
    ring
  · rw [h13,hs.outputCursor]
    push_cast
    ring
  · rw [h16,hs.counter]
    push_cast
    ring
  · rw [ht9]
    exact hzeros
  · exact h20
  · exact h21
  · exact h34
  · intro i hi
    rcases Nat.lt_or_eq_of_le (show i.val ≤ r by omega) with hir|hir
    · have heq : readArray t.mem (s₀.ptrs 13+(i.val : ℤ)*((featureDimension d p : ℤ)+2)) (featureDimension d p+2)=
          readArray s.mem (s₀.ptrs 13+(i.val : ℤ)*((featureDimension d p : ℤ)+2)) (featureDimension d p+2) := by
        apply readArray_congr
        intro a ha
        apply hframe
        · right
          rw [hp9]
          have hm : 0 ≤ (i.val : ℤ)*((featureDimension d p : ℤ)+2) := by positivity
          omega
        · left
          rw [hs.outputCursor]
          have hh := encoded_index_interval (s₀.ptrs 13) (featureDimension d p+2) i.val r a hir ha
          simpa only [Nat.cast_add,Nat.cast_ofNat] using hh
      rw [heq]
      exact hs.written i hir
    · have hij : i=j := Fin.ext hir
      subst i
      rw [← hs.outputCursor]
      exact hrow
  · intro z hzExp hzOut
    have hewidth : ((r+1 : ℕ) : ℤ)*((featureDimension d p : ℤ)+2)=
        (r : ℤ)*((featureDimension d p : ℤ)+2)+((featureDimension d p : ℤ)+2) := by push_cast; ring
    rw [hewidth] at hzOut
    rw [hframe z (by simpa only [hp9] using hzExp)
      (by rw [hs.outputCursor]; push_cast; omega)]
    apply hs.frame z hzExp
    omega
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMDatasetEncoding
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def encodeDatasetLoop : Cmd := .loop (.pointer 16 17) packedRowCommand
def encodeDatasetCommand : Cmd := .seq (.atom (.pset 16 1)) encodeDatasetLoop
lemma encode_dataset_command_correct (ω : PolySampIso.Streams) (d p N : ℕ) (S : Fin N → Example d) (s : Store)
    (hd : s.ptrs 0=d) (hD : s.ptrs 15=featureDimension d p) (hN : s.ptrs 17=N)
    (hinput : s.ptrs 7+(N : ℤ)*((d : ℤ)+1) ≤ s.ptrs 9) (houtput : s.ptrs 9+(d : ℤ) ≤ s.ptrs 13)
    (hxs : ∀ j : Fin N, readArray s.mem (s.ptrs 7+(j.val : ℤ)*((d : ℤ)+1)) d=List.ofFn (fun i => (S j).1 i))
    (hys : ∀ j : Fin N, s.mem (s.ptrs 7+(j.val : ℤ)*((d : ℤ)+1)+(d : ℤ))=label (S j).2)
    (hκ : readArray s.mem (s.ptrs 9) d=List.replicate d 0) (h20 : s.regs 20=0) (h21 : s.regs 21=p)
    (h34 : s.regs 34=radius d p) :
    ∃ t k, k ≤ 3+N*(2+120*featureDimension d p*(d+p+1)) ∧ Eval ω encodeDatasetCommand s t k ∧
      (∀ j : Fin N, readArray t.mem (s.ptrs 13+(j.val : ℤ)*((featureDimension d p : ℤ)+2)) (featureDimension d p+2)=
        encodedRow d p (S j).1 (S j).2) ∧
      readArray t.mem (s.ptrs 9) d=List.replicate d 0 ∧ t.regs 20=0 ∧ t.regs 21=p ∧ t.regs 34=radius d p ∧
      t.ptrs 7=s.ptrs 7+(N : ℤ)*((d : ℤ)+1) ∧ t.ptrs 13=s.ptrs 13+(N : ℤ)*((featureDimension d p : ℤ)+2) ∧
      (∀ z, (z < s.ptrs 9 ∨ s.ptrs 9+(d : ℤ) ≤ z) →
        (z < s.ptrs 13 ∨ s.ptrs 13+(N : ℤ)*((featureDimension d p : ℤ)+2) ≤ z) → t.mem z=s.mem z) ∧
      (∀ q, q ∉ ({3,4,6,7,10,11,12,13,14,16} : Finset ℕ) → t.ptrs q=s.ptrs q) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  let u := Op.act ω s (.pset 16 1)
  have hu : Eval ω (.atom (.pset 16 1)) s u 1 := Eval.atom s _
  let Inv := DatasetInvariant d p N S s
  have hinit : Inv 0 u := by
    constructor
    · intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> simp [u,Op.act]
    · simp [u,Op.act]
    · simp [u,Op.act]
    · simp [u,Op.act]
    · simpa [u,Op.act] using hκ
    · exact h20
    · exact h21
    · exact h34
    · intro j hj; omega
    · intro z hz1 hz2; rfl
  have htrue (i : ℕ) (hi : i < N) (v : Store) (hv : Inv i v) : Test.holds v (.pointer 16 17) := by
    change v.ptrs 16 ≤ v.ptrs 17
    rw [hv.counter,hv.fixedPointers 17 (by simp),hN]
    omega
  have hfalse (v : Store) (hv : Inv N v) : ¬Test.holds v (.pointer 16 17) := by
    change ¬v.ptrs 16 ≤ v.ptrs 17
    rw [hv.counter,hv.fixedPointers 17 (by simp),hN]
    omega
  obtain ⟨t,k,hk,he,ht⟩ := eval_loop_invariant ω (.pointer 16 17) packedRowCommand N
    (120*featureDimension d p*(d+p+1)) Inv htrue hfalse
    (fun i hi v hv => dataset_invariant_step ω d p N S s hd hD hinput houtput hxs hys i hi v hv) u hinit
  have hall : Eval ω encodeDatasetCommand s t (1+k) := Eval.seq hu he
  have hcg := hall.cursors_preserved (by decide)
  refine ⟨t,1+k,by omega,hall,(fun j => ht.written j j.isLt),?_,ht.total,ht.budget,ht.radius,
    ht.inputCursor,ht.outputCursor,ht.frame,?_,hcg.1,hcg.2⟩
  · rw [← ht.fixedPointers 9 (by simp)]
    exact ht.zeros
  · intro q hq
    apply hall.pointer_preserved
    simp [encodeDatasetCommand,encodeDatasetLoop,packedRowCommand,pointFeaturesCommand,featureLoop,featureBody,featureReset,featureStore,tensorCommand,tensorLoop,tensorBody,
      hermiteCommand,hermiteInit,hermiteStep,hermiteFinish,tensorPrefix,tensorSuffix,
      indexSuccessorCommand,indexSuccessorLoop,indexSuccessorBody,indexSuccessorInit,indexSuccessorPrefix,indexSuccessorYes,indexSuccessorNo,
      clipCommand,clipPrefix,clipNorm,clipFactor,dotCommand,dotLoop,dotStep,scaleCommand,scaleLoop,scaleStep,
      advanceCommand,advanceLoop,advanceStep,rowMetadata,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMActiveEncoding
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def radiusSetup : List Op := [.pointerReal 34 15,.sqrt 34 34,.literal 0 2,.mul 34 0 34]
def activeEncodingCommand : Cmd := .seq (.block radiusSetup) encodeDatasetCommand
lemma active_encoding_command_correct (ω : PolySampIso.Streams) (d p M N n : ℕ) (input : ℕ → ℝ)
    (S : Fin N → Example d) (hS : InputRows d N S input) (s : Store) (hs : PreparedShape d p M N n input s)
    (hDn : featureDimension d p ≤ n) :
    ∃ t k, k ≤ 7+N*(2+120*featureDimension d p*(d+p+1)) ∧ Eval ω activeEncodingCommand s t k ∧
      (∀ j : Fin N, readArray t.mem (workspaceBase d N+(d : ℤ)+(j.val : ℤ)*((featureDimension d p : ℤ)+2))
        (featureDimension d p+2)=encodedRow d p (S j).1 (S j).2) ∧
      t.ptrs 7=workspaceBase d N ∧
      t.ptrs 13=workspaceBase d N+(d : ℤ)+(N : ℤ)*((featureDimension d p : ℤ)+2) ∧
      readArray t.mem (workspaceBase d N) d=List.replicate d 0 ∧ t.regs 20=0 ∧ t.regs 21=p ∧ t.regs 34=radius d p ∧
      (∀ z, (z < workspaceBase d N ∨ workspaceBase d N+(d : ℤ) ≤ z) →
        (z < workspaceBase d N+(d : ℤ) ∨
          workspaceBase d N+(d : ℤ)+(N : ℤ)*((featureDimension d p : ℤ)+2) ≤ z) → t.mem z=s.mem z) ∧
      (∀ q, q ∉ ({3,4,6,7,10,11,12,13,14,16} : Finset ℕ) → t.ptrs q=s.ptrs q) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  have hs15 : s.ptrs 15=featureDimension d p := by simpa only [if_pos hDn] using hs.dimension
  let u := blockAct ω radiusSetup s
  have hu : Eval ω (.block radiusSetup) s u 4 := eval_block ω radiusSetup s
  have hu34 : u.regs 34=radius d p := by simp [u,blockAct,radiusSetup,Op.act,hs15,radius]
  obtain ⟨hxs,hys⟩ := hs.input_rows S hS
  obtain ⟨hzeros,h20⟩ := hs.active hDn
  have hi : u.ptrs 7+(N : ℤ)*((d : ℤ)+1) ≤ u.ptrs 9 := by
    change s.ptrs 7+(N : ℤ)*((d : ℤ)+1) ≤ s.ptrs 9
    rw [hs.inputStart,hs.exponentBase]
    rfl
  have ho : u.ptrs 9+(d : ℤ) ≤ u.ptrs 13 := by
    change s.ptrs 9+(d : ℤ) ≤ s.ptrs 13
    rw [hs.exponentBase,hs.featureBase]
  obtain ⟨t,k,hk,ht,hrows,hκ,ht20,ht21,ht34,h7,h13,hframe,hptr,hgc,hec⟩ := encode_dataset_command_correct ω d p N S u
    hs.dim hs15 hs.totalSize hi ho
    (fun j => by simpa [u,blockAct,radiusSetup,Op.act,hs.inputStart] using hxs j)
    (fun j => by simpa [u,blockAct,radiusSetup,Op.act,hs.inputStart] using hys j)
    hzeros h20 hs.budget hu34
  have hall : Eval ω activeEncodingCommand s t (4+k) := Eval.seq hu ht
  refine ⟨t,4+k,by omega,hall,?_,?_,?_,?_,ht20,ht21,ht34,?_,?_,hgc,hec⟩
  · intro j
    simpa [u,blockAct,radiusSetup,Op.act,hs.featureBase] using hrows j
  · simpa [u,blockAct,radiusSetup,Op.act,hs.inputStart,workspaceBase] using h7
  · simpa [u,blockAct,radiusSetup,Op.act,hs.featureBase] using h13
  · simpa [u,blockAct,radiusSetup,Op.act,hs.exponentBase] using hκ
  · intro z hz1 hz2
    simpa [u,blockAct,radiusSetup,Op.act] using hframe z
      (by simpa [u,blockAct,radiusSetup,Op.act,hs.exponentBase] using hz1)
      (by simpa [u,blockAct,radiusSetup,Op.act,hs.featureBase] using hz2)
  · intro q hq
    exact hptr q hq
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPublicSizes
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def publicSizesCommand : Cmd := .seq (headerNaturalCommand 16 4)
  (.seq (headerNaturalCommand 19 2) (headerNaturalCommand 20 5))
lemma public_sizes_correct (ω : PolySampIso.Streams) (n k m : ℕ) (s : Store)
    (hn : s.mem 4=n) (hk : s.mem 2=k) (hm : s.mem 5=m) :
    ∃ t, Eval ω publicSizesCommand s t (27+6*(n+k+m)) ∧ t.mem=s.mem ∧
      t.ptrs 16=n ∧ t.ptrs 19=k ∧ t.ptrs 20=m ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({40,41,43,44} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({16,19,20,30} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨u,hu,hu16,hum,hugc,huec,hur,hup⟩ := header_natural_command_correct ω 16 4 n s hn
  obtain ⟨v,hv,hv19,hvm,hvgc,hvec,hvr,hvp⟩ := header_natural_command_correct ω 19 2 k u (by rw [hum]; exact hk)
  obtain ⟨t,ht,ht20,htm,htgc,htec,htr,htp⟩ := header_natural_command_correct ω 20 5 m v (by rw [hvm,hum]; exact hm)
  have hall : Eval ω publicSizesCommand s t (27+6*(n+k+m)) := by
    convert! Eval.seq hu (Eval.seq hv ht) using 1 <;> omega
  refine ⟨t,hall,htm.trans (hvm.trans hum),?_,?_,ht20,htgc.trans (hvgc.trans hugc),htec.trans (hvec.trans huec),?_,?_⟩
  · rw [htp 16 (by omega) (by omega),hvp 16 (by omega) (by omega),hu16]
  · rw [htp 19 (by omega) (by omega),hv19]
  · intro r hr
    exact (htr r hr).trans ((hvr r hr).trans (hur r hr))
  · intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    exact (htp q (by tauto) (by tauto)).trans ((hvp q (by tauto) (by tauto)).trans (hup q (by tauto) (by tauto)))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.OptimizerStepFormula
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open RegressionGeometry
lemma optimizerStep_formula (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) :
    optimizerStep d p n ε δ=ε/(20*radius d p*n*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))) := by
  let T := radius d p
  let D := featureDimension d p
  let R := Real.sqrt ((D : ℝ)*Real.log (1/δ))
  have hT : 0 < T := radius_pos d p
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (featureDimension_pos d p)
  have hlog := privacyLog_lower δ hδ
  have hlog0 : 0 ≤ Real.log (1/δ) := by linarith
  have hDlog := mul_le_mul_of_nonneg_right hD hlog0
  have hR : 1/2 ≤ R := by
    have hs : R^2=(D : ℝ)*Real.log (1/δ) := Real.sq_sqrt (by positivity)
    have hr : 0 ≤ R := Real.sqrt_nonneg _
    nlinarith only [hs,hr,hDlog,hlog]
  have hRpos : 0 < R := by linarith
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have he1 : 1/(2*(2*T/((n : ℝ)⁻¹)))=1/(4*T*n) := by field_simp [hnR.ne']; ring
  have he2 : 1/(regressionSigma T D n ε δ*n*Real.sqrt n)=ε/(20*T*n*R) := by
    unfold regressionSigma
    dsimp [R]
    field_simp [hsqrtn]
    <;> ring
  have hbound : ε/(20*T*n*R) ≤ 1/(4*T*n) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 20*T*n*R) (by positivity : (0 : ℝ) < 4*T*n)).mpr
    have hh := mul_le_mul_of_nonneg_left (show ε ≤ 5*R by linarith) (show (0 : ℝ) ≤ 4*T*n by positivity)
    nlinarith only [hh]
  change min (1/(2*(2*T/((n : ℝ)⁻¹)))) (1/(regressionSigma T D n ε δ*n*Real.sqrt n))=ε/(20*T*n*R)
  rw [he1,he2,min_eq_right hbound]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RAMOptimizerParameters
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
def optimizerParameters : List Op := [
  .pset 30 4,.load 52 30,.pset 30 6,.load 53 30,.pset 30 7,.load 54 30,
  .literal 55 1,.literal 56 2,.div 59 55 52,
  .div 1 55 54,.log 1 1,.div 2 1 52,.sqrt 2 2,.literal 3 8,
  .mul 2 2 34,.mul 2 2 3,.div 50 2 53,
  .pointerReal 4 15,.mul 4 4 1,.sqrt 4 4,.literal 5 20,
  .mul 5 5 34,.mul 5 5 52,.mul 5 5 4,.div 51 53 5]
def OptimizerParametersInvariant (d p n : ℕ) (ε δ : ℝ) (s : Store) : Prop :=
  s.regs 50=regressionTau (radius d p) n ε δ ∧ s.regs 51=optimizerStep d p n ε δ ∧
  s.regs 52=n ∧ s.regs 53=ε ∧ s.regs 54=δ ∧ s.regs 55=1 ∧ s.regs 56=2 ∧ s.regs 59=(n : ℝ)⁻¹
lemma optimizer_parameters_correct (ω : PolySampIso.Streams) (d p n : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) (s : Store)
    (h4 : s.mem 4=n) (h6 : s.mem 6=ε) (h7 : s.mem 7=δ)
    (hD : s.ptrs 15=featureDimension d p) (hT : s.regs 34=radius d p) :
    let t := blockAct ω optimizerParameters s
    Eval ω (.block optimizerParameters) s t 25 ∧ OptimizerParametersInvariant d p n ε δ t ∧
      t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ q, q ≠ 30 → t.ptrs q=s.ptrs q) ∧
      (∀ r, r ∉ ({1,2,3,4,5,50,51,52,53,54,55,56,59} : Finset ℕ) → t.regs r=s.regs r) := by
  let t := blockAct ω optimizerParameters s
  have he : Eval ω (.block optimizerParameters) s t 25 := eval_block ω optimizerParameters s
  have hc := he.cursors_preserved (by decide)
  refine ⟨he,?_,he.memory_preserved (by decide),hc.1,hc.2,?_,?_⟩
  · simp [OptimizerParametersInvariant,t,blockAct,optimizerParameters,Op.act,h4,h6,h7,hD,hT,
      regressionTau,optimizerStep_formula d p n hn ε δ hε hδ]
    <;> ring
  · intro q hq
    exact he.pointer_preserved (by simp [Cmd.block,optimizerParameters,Cmd.pointers,Op.pointers,hq])
  · intro r hr
    apply he.register_preserved
    simp [Cmd.block,optimizerParameters,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPreparedMatrix
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
structure PreparedMatrix (d p k M n m : ℕ) (ε δ : ℝ) (input : ℕ → ℝ)
    (S : Fin (k*n+m) → Example d) (s : Store) : Prop where
  dimension : s.ptrs 15=featureDimension d p
  trainingSize : s.ptrs 16=n
  blocks : s.ptrs 19=k
  validationSize : s.ptrs 20=m
  thresholds : s.ptrs 2=M
  matrixBase : s.ptrs 40=workspaceBase d (k*n+m)+d
  freeBase : s.ptrs 13=workspaceBase d (k*n+m)+d+((k*n+m : ℕ) : ℤ)*((featureDimension d p : ℤ)+2)
  parameters : OptimizerParametersInvariant d p n ε δ s
  rows : ∀ j : Fin (k*n+m), readArray s.mem
    (workspaceBase d (k*n+m)+(d : ℤ)+(j.val : ℤ)*((featureDimension d p : ℤ)+2))
    (featureDimension d p+2)=encodedRow d p (S j).1 (S j).2
  header : ∀ i : ℕ, i<11 → s.mem (i : ℤ)=input i
  gaussianCursor : s.gc=0
  exponentialCursor : s.ec=0
def prepareMatrixCommand : Cmd := .seq (.atom (.pcopy 40 13)) (.seq activeEncodingCommand
  (.seq publicSizesCommand (.block optimizerParameters)))
lemma prepare_matrix_correct (ω : PolySampIso.Streams) (d p k M n m : ℕ) (hn : 0<n) (ε δ : ℝ)
    (hε : 0<ε ∧ ε≤1/2) (hδ : 0<δ ∧ δ≤1/2) (input : ℕ → ℝ)
    (S : Fin (k*n+m) → Example d) (hS : InputRows d (k*n+m) S input)
    (h4 : input 4=n) (h2 : input 2=k) (h5 : input 5=m) (h6 : input 6=ε) (h7 : input 7=δ)
    (s : Store) (hs : PreparedShape d p M (k*n+m) n input s)
    (hDn : featureDimension d p≤n) (hgc : s.gc=0) (hec : s.ec=0) :
    ∃ t cost, Eval ω prepareMatrixCommand s t cost ∧
      cost≤60+6*(n+k+m)+(k*n+m)*(2+120*featureDimension d p*(d+p+1)) ∧
      PreparedMatrix d p k M n m ε δ input S t := by
  let u := Op.act ω s (.pcopy 40 13)
  have hu : Eval ω (.atom (.pcopy 40 13)) s u 1 := Eval.atom s _
  have hus : PreparedShape d p M (k*n+m) n input u := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hs.budget,hs.trainSize,?_,hs.frame⟩
    · simpa [u,Op.act] using hs.dim
    · simpa [u,Op.act] using hs.degreePointer
    · simpa [u,Op.act] using hs.thresholdPointer
    · simpa [u,Op.act] using hs.inputStart
    · simpa [u,Op.act] using hs.exponentBase
    · simpa [u,Op.act] using hs.featureBase
    · simpa [u,Op.act] using hs.dimension
    · simpa [u,Op.act] using hs.totalSize
    · intro h
      simpa [u,Op.act] using hs.active h
  obtain ⟨e,ce,hce,he,herows,he7,he13,hezeros,he20,he21,he34,heframe,hep,hegc,heec⟩ :=
    active_encoding_command_correct ω d p M (k*n+m) n input S hS u hus hDn
  have eh (i : ℕ) (hi : i<11) : e.mem (i : ℤ)=input i := by
    have hB : 11≤workspaceBase d (k*n+m) := by
      unfold workspaceBase
      have h : 0≤((k*n+m : ℕ) : ℤ)*((d : ℤ)+1) := by positivity
      omega
    rw [heframe _ (Or.inl (by omega)) (Or.inl (by omega))]
    exact hs.header i hi
  have e15 : e.ptrs 15=featureDimension d p := by
    rw [hep 15 (by decide)]
    simpa only [if_pos hDn] using hus.dimension
  have e40 : e.ptrs 40=workspaceBase d (k*n+m)+d := by
    rw [hep 40 (by decide)]
    simpa [u,Op.act] using hs.featureBase
  obtain ⟨f,hf,hfm,hf16,hf19,hf20,hfgc,hfec,hfr,hfp⟩ := public_sizes_correct ω n k m e
    ((eh 4 (by omega)).trans h4) ((eh 2 (by omega)).trans h2) ((eh 5 (by omega)).trans h5)
  have f15 : f.ptrs 15=featureDimension d p := (hfp 15 (by decide)).trans e15
  have f34 : f.regs 34=radius d p := (hfr 34 (by decide)).trans he34
  let t := blockAct ω optimizerParameters f
  obtain ⟨ht,htpar,htm,htgc,htec,htp,htr⟩ := optimizer_parameters_correct ω d p n hn ε δ hε hδ f
    (by rw [hfm]; exact (eh 4 (by omega)).trans h4)
    (by rw [hfm]; exact (eh 6 (by omega)).trans h6)
    (by rw [hfm]; exact (eh 7 (by omega)).trans h7) f15 f34
  have hall : Eval ω prepareMatrixCommand s t (1+ce+(27+6*(n+k+m))+25) := by
    convert! Eval.seq hu (Eval.seq he (Eval.seq hf ht)) using 1 <;> omega
  refine ⟨t,_,hall,by omega,?_⟩
  constructor
  · exact (htp 15 (by omega)).trans f15
  · exact (htp 16 (by omega)).trans hf16
  · exact (htp 19 (by omega)).trans hf19
  · exact (htp 20 (by omega)).trans hf20
  · rw [htp 2 (by omega),hfp 2 (by decide),hep 2 (by decide)]
    exact hus.thresholdPointer
  · rw [htp 40 (by omega),hfp 40 (by decide),e40]
  · rw [htp 13 (by omega),hfp 13 (by decide),he13]
  · exact htpar
  · intro j
    rw [show t.mem=f.mem from htm,hfm]
    exact herows j
  · intro i hi
    rw [show t.mem=f.mem from htm,hfm]
    exact eh i hi
  · exact htgc.trans (hfgc.trans (hegc.trans hgc))
  · exact htec.trans (hfec.trans (heec.trans hec))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMGaussianArray
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def gaussianStep : List Op := [.gauss 0,.store 5 0,.pinc 5,.pinc 12]
def gaussianLoop : Cmd := .loop (.pointer 12 15) (.block gaussianStep)
def gaussianCommand : Cmd := .seq (.atom (.pset 12 1)) gaussianLoop
lemma gaussian_loop_correct (ω : PolySampIso.Streams) (n : ℕ) (s : Store)
    (hbound : s.ptrs 12+(n : ℤ)=s.ptrs 15+1) :
    ∃ t, Eval ω gaussianLoop s t (2+6*n) ∧
      t.mem=writeArray s.mem (s.ptrs 5) (List.ofFn (fun i : Fin n => ω.1 (s.gc+i.val))) ∧
      t.ptrs 5=s.ptrs 5+n ∧ t.gc=s.gc+n ∧ t.ec=s.ec := by
  induction n generalizing s with
  | zero =>
    refine ⟨s,Eval.loop_done ?_,rfl,by simp,by simp,rfl⟩
    change ¬s.ptrs 12 ≤ s.ptrs 15
    simp only [Nat.cast_zero,add_zero] at hbound
    omega
  | succ n ih =>
    have hhead : Test.holds s (.pointer 12 15) := by
      change s.ptrs 12 ≤ s.ptrs 15
      push_cast at hbound
      omega
    let u := blockAct ω gaussianStep s
    have hu : Eval ω (.block gaussianStep) s u 4 := eval_block ω gaussianStep s
    have humem : u.mem=Function.update s.mem (s.ptrs 5) (ω.1 s.gc) := rfl
    have huptr : u.ptrs=Function.update (Function.update s.ptrs 5 (s.ptrs 5+1)) 12 (s.ptrs 12+1) := by simp [u,blockAct,gaussianStep,Op.act]
    have hub : u.ptrs 12+(n : ℤ)=u.ptrs 15+1 := by
      simp only [huptr,Function.update_apply]
      norm_num
      push_cast at hbound
      omega
    obtain ⟨t,he,hm,h5,hgc,hec⟩ := ih u hub
    have hall := Eval.loop_step hhead hu he
    refine ⟨t,?_,?_,?_,?_,hec⟩
    · convert! hall using 1 <;> omega
    · rw [hm,humem,huptr]
      norm_num
      rw [writeArray_cons_sequential]
      have hlist : List.ofFn (fun i : Fin n => ω.1 (u.gc+i.val))=
          List.ofFn (fun i : Fin n => ω.1 (s.gc+(i.val+1))) := by
        congr 1
        funext i
        apply congrArg ω.1
        change s.gc+1+i.val=s.gc+(i.val+1)
        omega
      rw [hlist]
    · rw [h5,huptr]
      norm_num
      push_cast
      ring
    · rw [hgc]
      change s.gc+1+n=s.gc+(n+1)
      omega
lemma gaussian_command_correct (ω : PolySampIso.Streams) (n : ℕ) (s : Store) (hn : s.ptrs 15=n) :
    ∃ t, Eval ω gaussianCommand s t (3+6*n) ∧
      t.mem=writeArray s.mem (s.ptrs 5) (List.ofFn (fun i : Fin n => ω.1 (s.gc+i.val))) ∧
      t.ptrs 5=s.ptrs 5+n ∧ t.gc=s.gc+n ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 0 → t.regs r=s.regs r) ∧ (∀ q, q ≠ 5 → q ≠ 12 → t.ptrs q=s.ptrs q) := by
  let u := Op.act ω s (.pset 12 1)
  have hu : Eval ω (.atom (.pset 12 1)) s u 1 := Eval.atom s _
  have hub : u.ptrs 12+(n : ℤ)=u.ptrs 15+1 := by simp [u,Op.act,hn,add_comm]
  obtain ⟨t,he,hm,h5,hgc,hec⟩ := gaussian_loop_correct ω n u hub
  have hall : Eval ω gaussianCommand s t (3+6*n) := by convert! Eval.seq hu he using 1 <;> omega
  refine ⟨t,hall,?_,?_,hgc,hec,?_,?_⟩
  · simpa [u,Op.act] using hm
  · simpa [u,Op.act] using h5
  · intro r hr
    apply hall.register_preserved
    simp [gaussianCommand,gaussianLoop,gaussianStep,Cmd.block,Cmd.registers,Op.registers,hr]
  · intro q hq5 hq12
    apply hall.pointer_preserved
    simp [gaussianCommand,gaussianLoop,gaussianStep,Cmd.block,Cmd.pointers,Op.pointers,hq5,hq12]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPreloadNoise
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def preloadPrefix : List Op := [.pcopy 41 13,.pcopy 5 13,.pcopy 18 15,
  .pointerReal 0 16,.pointerReal 1 15,.pointerReal 2 19,.literal 3 1,
  .add 4 0 3,.add 0 0 1,.mul 40 4 0,.mul 40 40 2]
def preloadTail : List Op := [.pcopy 15 18,.pcopy 13 5]
def preloadNoiseCommand : Cmd := .seq (.block preloadPrefix) (.seq (naturalCommand 23)
  (.seq (.atom (.pcopy 15 23)) (.seq gaussianCommand (.block preloadTail))))
lemma preload_noise_command_correct (ω : PolySampIso.Streams) (k n D : ℕ) (s : Store)
    (hk : s.ptrs 19=k) (hn : s.ptrs 16=n) (hD : s.ptrs 15=D) :
    let T := k*(n+1)*(n+D)
    ∃ t, Eval ω preloadNoiseCommand s t (24+12*T) ∧
      t.mem=writeArray s.mem (s.ptrs 13) (List.ofFn (fun i : Fin T => ω.1 (s.gc+i.val))) ∧
      t.ptrs 41=s.ptrs 13 ∧ t.ptrs 13=s.ptrs 13+(T : ℤ) ∧ t.ptrs 15=D ∧ t.gc=s.gc+T ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,2,3,4,40,41,43,44} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({5,12,13,15,18,23,41} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  dsimp only
  let T := k*(n+1)*(n+D)
  let u := blockAct ω preloadPrefix s
  have hu : Eval ω (.block preloadPrefix) s u 11 := eval_block ω preloadPrefix s
  have hu40 : u.regs 40=(T : ℝ) := by
    simp [u,blockAct,preloadPrefix,Op.act,hk,hn,hD,T,Nat.cast_mul,Nat.cast_add]
    ring
  have hu5 : u.ptrs 5=s.ptrs 13 := by simp [u,blockAct,preloadPrefix,Op.act]
  have hu18 : u.ptrs 18=D := by simp [u,blockAct,preloadPrefix,Op.act,hD]
  have hu41 : u.ptrs 41=s.ptrs 13 := by simp [u,blockAct,preloadPrefix,Op.act]
  obtain ⟨v,hv,hv23,hvm,hvgc,hvec,hvreg,hvptr⟩ := natural_command_correct ω T 23 u hu40
  let a := Op.act ω v (.pcopy 15 23)
  have ha : Eval ω (.atom (.pcopy 15 23)) v a 1 := Eval.atom v _
  have ha15 : a.ptrs 15=T := by simp [a,Op.act,hv23]
  have ham : a.mem=s.mem := hvm
  have hagc : a.gc=s.gc := hvgc
  have haec : a.ec=s.ec := hvec
  obtain ⟨w,hw,hwm,hw5,hwgc,hwec,hwreg,hwptr⟩ := gaussian_command_correct ω T a ha15
  let t := blockAct ω preloadTail w
  have ht : Eval ω (.block preloadTail) w t 2 := eval_block ω preloadTail w
  have hall : Eval ω preloadNoiseCommand s t (24+12*T) := by
    convert! Eval.seq hu (Eval.seq hv (Eval.seq ha (Eval.seq hw ht))) using 1 <;> omega
  refine ⟨t,hall,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change w.mem=_
    rw [hwm]
    have ha5 : a.ptrs 5=s.ptrs 13 := by simp [a,Op.act,hvptr 5 (by omega),hu5]
    rw [ha5]
    rw [ham,hagc]
  · change w.ptrs 41=s.ptrs 13
    rw [hwptr 41 (by omega) (by omega)]
    simp [a,Op.act,hvptr 41 (by omega),hu41]
  · change w.ptrs 5=s.ptrs 13+(T : ℤ)
    rw [hw5]
    simp [a,Op.act,hvptr 5 (by omega),hu5]
  · change w.ptrs 18=(D : ℤ)
    rw [hwptr 18 (by omega) (by omega)]
    simp [a,Op.act,hvptr 18 (by omega),hu18]
  · change w.gc=s.gc+T
    rw [hwgc,hagc]
  · change w.ec=s.ec
    exact hwec.trans haec
  · intro r hr
    apply hall.register_preserved
    simp [preloadNoiseCommand,preloadPrefix,preloadTail,naturalCommand,naturalLoop,naturalInit,naturalStep,
      gaussianCommand,gaussianLoop,gaussianStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [preloadNoiseCommand,preloadPrefix,preloadTail,naturalCommand,naturalLoop,naturalInit,naturalStep,
      gaussianCommand,gaussianLoop,gaussianStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMAllocate
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def allocateCommand (q b : ℕ) : Cmd := .seq (.atom (.pcopy q 13)) (advanceCommand 13 b)
lemma allocate_command_correct (ω : PolySampIso.Streams) (q b n : ℕ) (hq13 : q ≠ 13) (hq12 : q ≠ 12)
    (hbq : b ≠ q) (hb12 : b ≠ 12) (hb13 : b ≠ 13) (s : Store) (hn : s.ptrs b=n) :
    ∃ t, Eval ω (allocateCommand q b) s t (4+4*n) ∧ t.ptrs q=s.ptrs 13 ∧ t.ptrs 13=s.ptrs 13+n ∧
      t.mem=s.mem ∧ t.regs=s.regs ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ≠ q → j ≠ 12 → j ≠ 13 → t.ptrs j=s.ptrs j) := by
  let u := Op.act ω s (.pcopy q 13)
  have hu : Eval ω (.atom (.pcopy q 13)) s u 1 := Eval.atom s _
  have hub : u.ptrs b=n := by simpa [u,Op.act,hbq] using hn
  obtain ⟨t,he,h13,hm,hr,hgc,hec,hptr⟩ := advance_command_correct ω 13 b n (by omega) hb12 hb13 u hub
  have hall : Eval ω (allocateCommand q b) s t (4+4*n) := by convert! Eval.seq hu he using 1 <;> omega
  refine ⟨t,hall,?_,?_,hm,hr,hgc,hec,?_⟩
  · rw [hptr q hq13 hq12]
    simp [u,Op.act]
  · simpa [u,Op.act,Ne.symm hq13] using h13
  · intro j hjq hj12 hj13
    exact hall.pointer_preserved (by simp [allocateCommand,advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers,hjq,hj12,hj13])
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMOptimizerBuffers
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def optimizerBuffersCommand : Cmd := .seq (allocateCommand 43 15) (.seq (allocateCommand 44 15)
  (.seq (allocateCommand 46 15) (.seq (allocateCommand 48 15) (.block [.pcopy 49 13,.pcopy 50 13]))))
lemma optimizer_buffers_correct (ω : PolySampIso.Streams) (D : ℕ) (s : Store) (hD : s.ptrs 15=D) :
    ∃ t, Eval ω optimizerBuffersCommand s t (18+16*D) ∧ t.mem=s.mem ∧ t.regs=s.regs ∧
      t.ptrs 43=s.ptrs 13 ∧ t.ptrs 44=s.ptrs 13+D ∧ t.ptrs 46=s.ptrs 13+2*D ∧
      t.ptrs 48=s.ptrs 13+3*D ∧ t.ptrs 49=s.ptrs 13+4*D ∧ t.ptrs 50=s.ptrs 13+4*D ∧
      t.ptrs 13=s.ptrs 13+4*D ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ q, q ∉ ({12,13,43,44,46,48,49,50} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨a,ha,ha43,ha13,ham,har,hagc,haec,hap⟩ := allocate_command_correct ω 43 15 D
    (by omega) (by omega) (by omega) (by omega) (by omega) s hD
  obtain ⟨b,hb,hb44,hb13,hbm,hbr,hbgc,hbec,hbp⟩ := allocate_command_correct ω 44 15 D
    (by omega) (by omega) (by omega) (by omega) (by omega) a ((hap 15 (by omega) (by omega) (by omega)).trans hD)
  obtain ⟨c,hc,hc46,hc13,hcm,hcr,hcgc,hcec,hcp⟩ := allocate_command_correct ω 46 15 D
    (by omega) (by omega) (by omega) (by omega) (by omega) b
    ((hbp 15 (by omega) (by omega) (by omega)).trans ((hap 15 (by omega) (by omega) (by omega)).trans hD))
  obtain ⟨e,he,he48,he13,hem,her,hegc,heec,hep⟩ := allocate_command_correct ω 48 15 D
    (by omega) (by omega) (by omega) (by omega) (by omega) c
    ((hcp 15 (by omega) (by omega) (by omega)).trans ((hbp 15 (by omega) (by omega) (by omega)).trans
      ((hap 15 (by omega) (by omega) (by omega)).trans hD)))
  let t := blockAct ω [.pcopy 49 13,.pcopy 50 13] e
  have ht : Eval ω (.block [.pcopy 49 13,.pcopy 50 13]) e t 2 := eval_block ω _ e
  have hall : Eval ω optimizerBuffersCommand s t (18+16*D) := by
    convert! Eval.seq ha (Eval.seq hb (Eval.seq hc (Eval.seq he ht))) using 1 <;> omega
  have hmem : t.mem=s.mem := hem.trans (hcm.trans (hbm.trans ham))
  have hregs : t.regs=s.regs := her.trans (hcr.trans (hbr.trans har))
  have htc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,hmem,hregs,?_,?_,?_,?_,?_,?_,?_,htc.1,htc.2,?_⟩
  · change e.ptrs 43=s.ptrs 13
    rw [hep 43 (by omega) (by omega) (by omega),hcp 43 (by omega) (by omega) (by omega),hbp 43 (by omega) (by omega) (by omega),ha43]
  · change e.ptrs 44=s.ptrs 13+D
    rw [hep 44 (by omega) (by omega) (by omega),hcp 44 (by omega) (by omega) (by omega),hb44,ha13]
  · change e.ptrs 46=s.ptrs 13+2*D
    rw [hep 46 (by omega) (by omega) (by omega),hc46,hb13,ha13]
    ring
  · change e.ptrs 48=s.ptrs 13+3*D
    rw [he48,hc13,hb13,ha13]
    ring
  · change e.ptrs 13=s.ptrs 13+4*D
    rw [he13,hc13,hb13,ha13]
    ring
  · change e.ptrs 13=s.ptrs 13+4*D
    rw [he13,hc13,hb13,ha13]
    ring
  · change e.ptrs 13=s.ptrs 13+4*D
    rw [he13,hc13,hb13,ha13]
    ring
  · intro q hq
    apply hall.pointer_preserved
    simp [optimizerBuffersCommand,allocateCommand,advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMBlockWorkspace
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def stridePrefix : List Op := [.pointerReal 0 16,.pointerReal 1 15,.literal 2 2,.add 1 1 2,.mul 40 0 1]
def bankPrefix : List Op := [.pointerReal 0 19,.pointerReal 1 15,.mul 40 0 1]
def blockWorkspaceCommand : Cmd := .seq (.block stridePrefix) (.seq (naturalCommand 17)
  (.seq (.block bankPrefix) (.seq (naturalCommand 23) (advanceCommand 13 23))))
lemma block_workspace_correct (ω : PolySampIso.Streams) (k n D : ℕ) (s : Store)
    (hk : s.ptrs 19=k) (hn : s.ptrs 16=n) (hD : s.ptrs 15=D) :
    ∃ t, Eval ω blockWorkspaceCommand s t (25+6*(n*(D+2))+10*(k*D)) ∧
      t.ptrs 17=n*(D+2) ∧ t.ptrs 13=s.ptrs 13+k*D ∧ t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,2,40,41,43,44} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({12,13,17,23} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω stridePrefix s
  have hu : Eval ω (.block stridePrefix) s u 5 := eval_block ω _ s
  have u40 : u.regs 40=(n*(D+2) : ℕ) := by simp [u,blockAct,stridePrefix,Op.act,hn,hD,Nat.cast_mul,Nat.cast_add]
  obtain ⟨v,hv,hv17,hvm,hvgc,hvec,hvr,hvp⟩ := natural_command_correct ω (n*(D+2)) 17 u u40
  let w := blockAct ω bankPrefix v
  have hw : Eval ω (.block bankPrefix) v w 3 := eval_block ω _ v
  have w40 : w.regs 40=(k*D : ℕ) := by
    simp [w,blockAct,bankPrefix,Op.act,hvp 19 (by omega),hvp 15 (by omega),u,blockAct,stridePrefix,hk,hD,Nat.cast_mul]
  obtain ⟨a,ha,ha23,ham,hagc,haec,har,hap⟩ := natural_command_correct ω (k*D) 23 w w40
  obtain ⟨t,ht,ht13,htm,htr,htgc,htec,htp⟩ := advance_command_correct ω 13 23 (k*D)
    (by omega) (by omega) (by omega) a ha23
  have hall : Eval ω blockWorkspaceCommand s t (25+6*(n*(D+2))+10*(k*D)) := by
    convert! Eval.seq hu (Eval.seq hv (Eval.seq hw (Eval.seq ha ht))) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,?_,?_,htm.trans (ham.trans hvm),hc.1,hc.2,?_,?_⟩
  · rw [htp 17 (by omega) (by omega),hap 17 (by omega)]
    exact hv17
  · rw [ht13,hap 13 (by omega)]
    change v.ptrs 13+(k*D : ℕ)=s.ptrs 13+(k*D : ℕ)
    rw [hvp 13 (by omega)]
    rfl
  · intro r hr
    apply hall.register_preserved
    simp [blockWorkspaceCommand,stridePrefix,bankPrefix,naturalCommand,naturalLoop,naturalInit,naturalStep,
      advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [blockWorkspaceCommand,stridePrefix,bankPrefix,naturalCommand,naturalLoop,naturalInit,naturalStep,
      advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMReadyHeap
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
abbrev matrixAddress (d N : ℕ) : ℤ := workspaceBase d N+d
abbrev noiseAddress (d p N : ℕ) : ℤ := matrixAddress d N+(N : ℤ)*((featureDimension d p : ℤ)+2)
abbrev noiseCount (k n D : ℕ) : ℕ := k*(n+1)*(n+D)
abbrev gradientAddress (d p k n m : ℕ) : ℤ := noiseAddress d p (k*n+m)+(noiseCount k n (featureDimension d p) : ℤ)
structure ReadyHeap (d p k M n m : ℕ) (ε δ : ℝ) (S : Fin (k*n+m) → Example d)
    (ω : PolySampIso.Streams) (s : Store) : Prop where
  dimension : s.ptrs 15=featureDimension d p
  trainingSize : s.ptrs 16=n
  blocks : s.ptrs 19=k
  validationSize : s.ptrs 20=m
  thresholds : s.ptrs 2=M
  stride : s.ptrs 17=n*(featureDimension d p+2)
  matrixBase : s.ptrs 40=matrixAddress d (k*n+m)
  blockBase : s.ptrs 53=matrixAddress d (k*n+m)
  noiseBase : s.ptrs 41=noiseAddress d p (k*n+m)
  noiseCursor : s.ptrs 42=noiseAddress d p (k*n+m)
  gradient : s.ptrs 43=gradientAddress d p k n m
  xbase : s.ptrs 44=gradientAddress d p k n m+featureDimension d p
  agbase : s.ptrs 46=gradientAddress d p k n m+2*featureDimension d p
  midpoint : s.ptrs 48=gradientAddress d p k n m+3*featureDimension d p
  bankBase : s.ptrs 49=gradientAddress d p k n m+4*featureDimension d p
  bankCursor : s.ptrs 50=gradientAddress d p k n m+4*featureDimension d p
  freeBase : s.ptrs 13=gradientAddress d p k n m+4*featureDimension d p+k*featureDimension d p
  counter : s.ptrs 22=1
  parameters : OptimizerParametersInvariant d p n ε δ s
  rows : ∀ j : Fin (k*n+m), readArray s.mem
    (matrixAddress d (k*n+m)+(j.val : ℤ)*((featureDimension d p : ℤ)+2))
    (featureDimension d p+2)=encodedRow d p (S j).1 (S j).2
  noise : ∀ i : Fin (noiseCount k n (featureDimension d p)),
    s.mem (noiseAddress d p (k*n+m)+(i.val : ℤ))=ω.1 i.val
  gaussianCursor : s.gc=noiseCount k n (featureDimension d p)
  exponentialCursor : s.ec=0
def readyHeapInit : List Op := [.pcopy 42 41,.pcopy 53 40,.pset 22 1]
def readyHeapCommand : Cmd := .seq preloadNoiseCommand (.seq optimizerBuffersCommand
  (.seq blockWorkspaceCommand (.block readyHeapInit)))
lemma ready_heap_correct (ω : PolySampIso.Streams) (d p k M n m : ℕ) (ε δ : ℝ) (input : ℕ → ℝ)
    (S : Fin (k*n+m) → Example d) (s : Store) (hs : PreparedMatrix d p k M n m ε δ input S s) :
    ∃ t, Eval ω readyHeapCommand s t
      (70+12*noiseCount k n (featureDimension d p)+16*featureDimension d p+
        6*(n*(featureDimension d p+2))+10*(k*featureDimension d p)) ∧
      ReadyHeap d p k M n m ε δ S ω t := by
  let D := featureDimension d p
  let T := noiseCount k n D
  obtain ⟨e,he,hem,he41,he13,he15,hegc,heec,her,hep⟩ := preload_noise_command_correct ω k n D s hs.blocks hs.trainingSize hs.dimension
  obtain ⟨b,hb,hbm,hbr,hb43,hb44,hb46,hb48,hb49,hb50,hb13,hbgc,hbec,hbp⟩ := optimizer_buffers_correct ω D e he15
  obtain ⟨w,hw,hw17,hw13,hwm,hwgc,hwec,hwr,hwp⟩ := block_workspace_correct ω k n D b
    ((hbp 19 (by decide)).trans ((hep 19 (by decide)).trans hs.blocks))
    ((hbp 16 (by decide)).trans ((hep 16 (by decide)).trans hs.trainingSize))
    ((hbp 15 (by decide)).trans he15)
  let t := blockAct ω readyHeapInit w
  have ht : Eval ω (.block readyHeapInit) w t 3 := eval_block ω _ w
  have hall : Eval ω readyHeapCommand s t (70+12*T+16*D+6*(n*(D+2))+10*(k*D)) := by
    convert! Eval.seq he (Eval.seq hb (Eval.seq hw ht)) using 1 <;> simp only [T,noiseCount] <;> omega
  have tp (q : ℕ) (hq : q ∉ ({22,42,53} : Finset ℕ)) : t.ptrs q=w.ptrs q := by
    apply ht.pointer_preserved
    simp [Cmd.block,readyHeapInit,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
  have oldp (q : ℕ) (hq : q ∉ ({5,12,13,15,17,18,23,41,43,44,46,48,49,50} : Finset ℕ)) : w.ptrs q=s.ptrs q := by
    rw [hwp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto),
      hbp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto),
      hep q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)]
  have tm : t.mem=writeArray s.mem (noiseAddress d p (k*n+m)) (List.ofFn (fun i : Fin T => ω.1 i.val)) := by
    change w.mem=_
    rw [hwm,hbm,hem,hs.freeBase,hs.gaussianCursor]
    simp [noiseAddress,matrixAddress] <;> rfl
  have tr (r : ℕ) (hr : 50≤r) : t.regs r=s.regs r := by
    change w.regs r=s.regs r
    rw [hwr r (by simp; omega),hbr,her r (by simp; omega)]
  have w43 : w.ptrs 43=gradientAddress d p k n m := by
    rw [hwp 43 (by decide),hb43,he13,hs.freeBase]
  have w44 : w.ptrs 44=gradientAddress d p k n m+D := by
    rw [hwp 44 (by decide),hb44,he13,hs.freeBase]
  have w46 : w.ptrs 46=gradientAddress d p k n m+2*D := by
    rw [hwp 46 (by decide),hb46,he13,hs.freeBase]
  have w48 : w.ptrs 48=gradientAddress d p k n m+3*D := by
    rw [hwp 48 (by decide),hb48,he13,hs.freeBase]
  have w49 : w.ptrs 49=gradientAddress d p k n m+4*D := by
    rw [hwp 49 (by decide),hb49,he13,hs.freeBase]
  have w50 : w.ptrs 50=gradientAddress d p k n m+4*D := by
    rw [hwp 50 (by decide),hb50,he13,hs.freeBase]
  have w41 : w.ptrs 41=noiseAddress d p (k*n+m) := by
    rw [hwp 41 (by decide),hbp 41 (by decide),he41,hs.freeBase]
  refine ⟨t,hall,?_⟩
  constructor
  · rw [tp 15 (by decide),hwp 15 (by decide),hbp 15 (by decide),he15]
  · rw [tp 16 (by decide),oldp 16 (by decide),hs.trainingSize]
  · rw [tp 19 (by decide),oldp 19 (by decide),hs.blocks]
  · rw [tp 20 (by decide),oldp 20 (by decide),hs.validationSize]
  · rw [tp 2 (by decide),oldp 2 (by decide),hs.thresholds]
  · rw [tp 17 (by decide),hw17]
  · rw [tp 40 (by decide),oldp 40 (by decide),hs.matrixBase]
  · simp [t,blockAct,readyHeapInit,Op.act,oldp 40 (by decide),hs.matrixBase]
  · rw [tp 41 (by decide),w41]
  · simp [t,blockAct,readyHeapInit,Op.act,w41]
  · rw [tp 43 (by decide),w43]
  · rw [tp 44 (by decide),w44]
  · rw [tp 46 (by decide),w46]
  · rw [tp 48 (by decide),w48]
  · rw [tp 49 (by decide),w49]
  · rw [tp 50 (by decide),w50]
  · rw [tp 13 (by decide),hw13,hb13,he13,hs.freeBase]
  · simp [t,blockAct,readyHeapInit,Op.act]
  · simpa only [OptimizerParametersInvariant,tr 50 (by omega),tr 51 (by omega),tr 52 (by omega),tr 53 (by omega),
      tr 54 (by omega),tr 55 (by omega),tr 56 (by omega),tr 59 (by omega)] using hs.parameters
  · intro j
    rw [tm,readArray_write_after _ _ _ _ _ ?_]
    · exact hs.rows j
    · have hi := encoded_index_interval (matrixAddress d (k*n+m)) (D+2) j.val (k*n+m) (D+1) j.isLt (by omega)
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hi
      dsimp only [noiseAddress,D] at hi ⊢
      simp only [Nat.cast_add,Nat.cast_mul] at hi ⊢
      omega
  · intro i
    rw [tm,writeArray_at _ _ _ i.val (by simp only [List.length_ofFn]; exact i.isLt)]
    simp
  · change w.gc=T
    rw [hwgc,hbgc,hegc,hs.gaussianCursor]
    simp [T,noiseCount]
  · change w.ec=0
    exact hwec.trans (hbec.trans (heec.trans hs.exponentialCursor))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMAcceleratedParameters
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def acceleratedParameters : List Op := [.pointerReal 60 21,.add 0 60 55,.div 57 56 0,
  .mul 58 60 51,.div 58 58 56,.sub 61 55 57,.literal 0 0,.sub 62 0 58,.sub 63 0 51]
lemma accelerated_parameters_correct (ω : PolySampIso.Streams) (k : ℕ) (β : ℝ) (s : Store)
    (hk : s.ptrs 21=k) (hβ : s.regs 51=β) (h1 : s.regs 55=1) (h2 : s.regs 56=2) :
    let t := blockAct ω acceleratedParameters s
    Eval ω (.block acceleratedParameters) s t 9 ∧ t.mem=s.mem ∧ t.ptrs=s.ptrs ∧
      t.regs 57=accelAlpha k ∧ t.regs 58=accelLambda β k ∧ t.regs 61=1-accelAlpha k ∧
      t.regs 62= -accelLambda β k ∧ t.regs 63= -β ∧
      (∀ r, r ∉ ({0,57,58,60,61,62,63} : Finset ℕ) → t.regs r=s.regs r) := by
  dsimp only
  have he := eval_block ω acceleratedParameters s
  refine ⟨he,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
  · simp [blockAct,acceleratedParameters,Op.act,hk,hβ,h1,h2,accelAlpha]
  · simp [blockAct,acceleratedParameters,Op.act,hk,hβ,h1,h2,accelLambda]
  · simp [blockAct,acceleratedParameters,Op.act,hk,hβ,h1,h2,accelAlpha]
  · simp [blockAct,acceleratedParameters,Op.act,hk,hβ,h1,h2,accelLambda]
  · simp [blockAct,acceleratedParameters,Op.act,hβ]
  · intro r hr
    apply he.register_preserved
    simp [Cmd.block,acceleratedParameters,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMAffineArray
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def affineStep : List Op := [.load 0 3,.load 1 4,.mul 0 0 32,.mul 1 1 33,.add 0 0 1,
  .store 3 0,.pinc 3,.pinc 4,.pinc 12]
def affineLoop : Cmd := .loop (.pointer 12 15) (.block affineStep)
def affineCommand : Cmd := .seq (.atom (.pset 12 1)) affineLoop
lemma affine_loop_correct (ω : PolySampIso.Streams) (xs ys : List ℝ) (hlen : ys.length=xs.length) (s : Store)
    (hbound : s.ptrs 12+(xs.length : ℤ)=s.ptrs 15+1)
    (hx : readArray s.mem (s.ptrs 3) xs.length=xs) (hy : readArray s.mem (s.ptrs 4) ys.length=ys)
    (hdisj : s.ptrs 4+(ys.length : ℤ) ≤ s.ptrs 3) :
    ∃ t, Eval ω affineLoop s t (2+11*xs.length) ∧
      t.mem=writeArray s.mem (s.ptrs 3) (List.zipWith (fun x y : ℝ => x*s.regs 32+y*s.regs 33) xs ys) ∧
      t.ptrs 3=s.ptrs 3+(xs.length : ℤ) ∧ t.ptrs 4=s.ptrs 4+(xs.length : ℤ) := by
  induction xs generalizing ys s with
  | nil =>
    have hh : ys=[] := List.length_eq_zero_iff.mp hlen
    subst ys
    refine ⟨s,Eval.loop_done ?_,rfl,by simp,by simp⟩
    change ¬s.ptrs 12 ≤ s.ptrs 15
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hbound
    omega
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : ys.length=xs.length := by simpa using hlen
      have hx' : s.mem (s.ptrs 3)=x ∧ readArray s.mem (s.ptrs 3+1) xs.length=xs := by
        simpa only [List.length_cons,readArray_cons,List.cons.injEq] using hx
      have hy' : s.mem (s.ptrs 4)=y ∧ readArray s.mem (s.ptrs 4+1) ys.length=ys := by
        simpa only [List.length_cons,readArray_cons,List.cons.injEq] using hy
      have hhead : Test.holds s (.pointer 12 15) := by
        change s.ptrs 12 ≤ s.ptrs 15
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
        omega
      let u := blockAct ω affineStep s
      have hu : Eval ω (.block affineStep) s u 9 := eval_block ω affineStep s
      have humem : u.mem=Function.update s.mem (s.ptrs 3) (x*s.regs 32+y*s.regs 33) := by
        simp [u,blockAct,affineStep,Op.act,hx'.1,hy'.1]
      have huptr : u.ptrs=Function.update (Function.update (Function.update s.ptrs 3 (s.ptrs 3+1)) 4 (s.ptrs 4+1)) 12 (s.ptrs 12+1) := by
        simp [u,blockAct,affineStep,Op.act]
      have hub : u.ptrs 12+(xs.length : ℤ)=u.ptrs 15+1 := by
        simp only [huptr,Function.update_apply]
        norm_num
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
        omega
      have hux : readArray u.mem (u.ptrs 3) xs.length=xs := by
        simp only [humem,huptr,Function.update_apply]
        norm_num
        rw [readArray_update_before _ _ _ _ _ (by omega)]
        exact hx'.2
      have huy : readArray u.mem (u.ptrs 4) ys.length=ys := by
        simp only [humem,huptr,Function.update_apply]
        norm_num
        rw [readArray_update_after _ _ _ _ _ (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hdisj; omega)]
        exact hy'.2
      have hudisj : u.ptrs 4+(ys.length : ℤ) ≤ u.ptrs 3 := by
        simp only [huptr,Function.update_apply]
        norm_num
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hdisj
        omega
      obtain ⟨t,he,hm,h3,h4⟩ := ih ys hlen' u hub hux huy hudisj
      have hall := Eval.loop_step hhead hu he
      refine ⟨t,?_,?_,?_,?_⟩
      · convert! hall using 1 <;> simp only [List.length_cons] <;> omega
      · rw [hm,humem,huptr]
        norm_num
        rw [writeArray_cons_sequential]
        rfl
      · rw [h3,huptr]
        norm_num
        push_cast
        ring
      · rw [h4,huptr]
        norm_num
        push_cast
        ring
lemma affine_command_correct (ω : PolySampIso.Streams) (xs ys : List ℝ) (hlen : ys.length=xs.length)
    (s : Store) (hn : s.ptrs 15=xs.length) (hx : readArray s.mem (s.ptrs 3) xs.length=xs)
    (hy : readArray s.mem (s.ptrs 4) ys.length=ys) (hdisj : s.ptrs 4+(ys.length : ℤ) ≤ s.ptrs 3) :
    ∃ t, Eval ω affineCommand s t (3+11*xs.length) ∧
      t.mem=writeArray s.mem (s.ptrs 3) (List.zipWith (fun x y : ℝ => x*s.regs 32+y*s.regs 33) xs ys) ∧
      t.ptrs 3=s.ptrs 3+(xs.length : ℤ) ∧ t.ptrs 4=s.ptrs 4+(xs.length : ℤ) ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 0 → r ≠ 1 → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := Op.act ω s (.pset 12 1)
  have hu : Eval ω (.atom (.pset 12 1)) s u 1 := Eval.atom s _
  have hub : u.ptrs 12+(xs.length : ℤ)=u.ptrs 15+1 := by simp [u,Op.act,hn,add_comm]
  obtain ⟨t,he,hm,h3,h4⟩ := affine_loop_correct ω xs ys hlen u hub
    (by simpa [u,Op.act] using hx) (by simpa [u,Op.act] using hy) (by simpa [u,Op.act] using hdisj)
  have hall : Eval ω affineCommand s t (3+11*xs.length) := by convert! Eval.seq hu he using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,?_,?_,?_,hc.1,hc.2,?_,?_⟩
  · simpa [u,Op.act] using hm
  · simpa [u,Op.act] using h3
  · simpa [u,Op.act] using h4
  · intro r hr0 hr1
    apply hall.register_preserved
    simp [affineCommand,affineLoop,affineStep,Cmd.block,Cmd.registers,Op.registers,hr0,hr1]
  · intro q hq
    apply hall.pointer_preserved
    simp [affineCommand,affineLoop,affineStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMVectorOperations
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma affine_vector_correct (ω : PolySampIso.Streams) (D : ℕ) (x y : Vec D) (s : Store)
    (hn : s.ptrs 15=D) (hx : readArray s.mem (s.ptrs 3) D=List.ofFn (fun i => x i))
    (hy : readArray s.mem (s.ptrs 4) D=List.ofFn (fun i => y i))
    (hdisj : s.ptrs 4+(D : ℤ) ≤ s.ptrs 3) :
    ∃ t, Eval ω affineCommand s t (3+11*D) ∧
      t.mem=writeArray s.mem (s.ptrs 3) (List.ofFn (fun i => (s.regs 32 • x+s.regs 33 • y) i)) ∧
      t.ptrs 3=s.ptrs 3+D ∧ t.ptrs 4=s.ptrs 4+D ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 0 → r ≠ 1 → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨t,he,hm,h3,h4,hgc,hec,hr,hp⟩ := affine_command_correct ω
    (List.ofFn (fun i => x i)) (List.ofFn (fun i => y i)) (by simp) s (by simpa using hn)
    (by simpa using hx) (by simpa using hy) (by simpa using hdisj)
  refine ⟨t,by simpa using he,?_,by simpa using h3,by simpa using h4,hgc,hec,hr,hp⟩
  rw [hm]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [PiLp.add_apply,PiLp.smul_apply,mul_comm]
lemma scale_vector_correct (ω : PolySampIso.Streams) (D : ℕ) (x : Vec D) (s : Store)
    (hn : s.ptrs 15=D) (hx : readArray s.mem (s.ptrs 3) D=List.ofFn (fun i => x i)) :
    ∃ t, Eval ω scaleCommand s t (3+7*D) ∧
      t.mem=writeArray s.mem (s.ptrs 3) (List.ofFn (fun i => (s.regs 32 • x) i)) ∧
      t.ptrs 3=s.ptrs 3+D ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 0 → t.regs r=s.regs r) ∧ (∀ q, q ≠ 3 → q ≠ 12 → t.ptrs q=s.ptrs q) := by
  obtain ⟨t,he,hm,h3,hgc,hec,hr,hp⟩ := scale_command_correct ω (List.ofFn (fun i => x i))
    s (by simpa using hn) (by simpa using hx)
  refine ⟨t,by simpa using he,?_,by simpa using h3,hgc,hec,hr,hp⟩
  rw [hm]
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext i
  simp [PiLp.smul_apply,mul_comm]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMCopyArray
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def copyStep : List Op := [.load 0 3,.store 5 0,.pinc 3,.pinc 5,.pinc 12]
def copyLoop : Cmd := .loop (.pointer 12 15) (.block copyStep)
def copyCommand : Cmd := .seq (.atom (.pset 12 1)) copyLoop
lemma copy_loop_correct (ω : PolySampIso.Streams) (xs : List ℝ) (s : Store)
    (hbound : s.ptrs 12+(xs.length : ℤ)=s.ptrs 15+1) (hx : readArray s.mem (s.ptrs 3) xs.length=xs)
    (hdisj : s.ptrs 3+(xs.length : ℤ) ≤ s.ptrs 5 ∨ s.ptrs 5+(xs.length : ℤ) ≤ s.ptrs 3) :
    ∃ t, Eval ω copyLoop s t (2+7*xs.length) ∧ t.mem=writeArray s.mem (s.ptrs 5) xs ∧
      t.ptrs 3=s.ptrs 3+(xs.length : ℤ) ∧ t.ptrs 5=s.ptrs 5+(xs.length : ℤ) := by
  induction xs generalizing s with
  | nil =>
    refine ⟨s,Eval.loop_done ?_,rfl,by simp,by simp⟩
    change ¬s.ptrs 12 ≤ s.ptrs 15
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hbound
    omega
  | cons x xs ih =>
    have hx' : s.mem (s.ptrs 3)=x ∧ readArray s.mem (s.ptrs 3+1) xs.length=xs := by
      simpa only [List.length_cons,readArray_cons,List.cons.injEq] using hx
    have hhead : Test.holds s (.pointer 12 15) := by
      change s.ptrs 12 ≤ s.ptrs 15
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
      omega
    let u := blockAct ω copyStep s
    have hu : Eval ω (.block copyStep) s u 5 := eval_block ω copyStep s
    have humem : u.mem=Function.update s.mem (s.ptrs 5) x := by simp [u,blockAct,copyStep,Op.act,hx'.1]
    have huptr : u.ptrs=Function.update (Function.update (Function.update s.ptrs 3 (s.ptrs 3+1)) 5 (s.ptrs 5+1)) 12 (s.ptrs 12+1) := by
      simp [u,blockAct,copyStep,Op.act]
    have hub : u.ptrs 12+(xs.length : ℤ)=u.ptrs 15+1 := by
      simp only [huptr,Function.update_apply]
      norm_num
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
      omega
    have hux : readArray u.mem (u.ptrs 3) xs.length=xs := by
      simp only [humem,huptr,Function.update_apply]
      norm_num
      rcases hdisj with h|h
      · rw [readArray_update_after _ _ _ _ _ (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at h; omega)]
        exact hx'.2
      · rw [readArray_update_before _ _ _ _ _ (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at h; omega)]
        exact hx'.2
    have hudisj : u.ptrs 3+(xs.length : ℤ) ≤ u.ptrs 5 ∨ u.ptrs 5+(xs.length : ℤ) ≤ u.ptrs 3 := by
      simp only [huptr,Function.update_apply]
      norm_num
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hdisj
      omega
    obtain ⟨t,he,hm,h3,h5⟩ := ih u hub hux hudisj
    have hall := Eval.loop_step hhead hu he
    refine ⟨t,?_,?_,?_,?_⟩
    · convert! hall using 1 <;> simp only [List.length_cons] <;> omega
    · rw [hm,humem,huptr]
      norm_num
      exact writeArray_cons_sequential _ _ _ _
    · rw [h3,huptr]
      norm_num
      push_cast
      ring
    · rw [h5,huptr]
      norm_num
      push_cast
      ring
lemma copy_command_correct (ω : PolySampIso.Streams) (xs : List ℝ) (s : Store) (hn : s.ptrs 15=xs.length)
    (hx : readArray s.mem (s.ptrs 3) xs.length=xs)
    (hdisj : s.ptrs 3+(xs.length : ℤ) ≤ s.ptrs 5 ∨ s.ptrs 5+(xs.length : ℤ) ≤ s.ptrs 3) :
    ∃ t, Eval ω copyCommand s t (3+7*xs.length) ∧ t.mem=writeArray s.mem (s.ptrs 5) xs ∧
      t.ptrs 3=s.ptrs 3+(xs.length : ℤ) ∧ t.ptrs 5=s.ptrs 5+(xs.length : ℤ) ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 0 → t.regs r=s.regs r) ∧ (∀ q, q ∉ ({3,5,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := Op.act ω s (.pset 12 1)
  have hu : Eval ω (.atom (.pset 12 1)) s u 1 := Eval.atom s _
  have hub : u.ptrs 12+(xs.length : ℤ)=u.ptrs 15+1 := by simp [u,Op.act,hn,add_comm]
  obtain ⟨t,he,hm,h3,h5⟩ := copy_loop_correct ω xs u hub (by simpa [u,Op.act] using hx) (by simpa [u,Op.act] using hdisj)
  have hall : Eval ω copyCommand s t (3+7*xs.length) := by convert! Eval.seq hu he using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,?_,?_,?_,hc.1,hc.2,?_,?_⟩
  · simpa [u,Op.act] using hm
  · simpa [u,Op.act] using h3
  · simpa [u,Op.act] using h5
  · intro r hr
    apply hall.register_preserved
    simp [copyCommand,copyLoop,copyStep,Cmd.block,Cmd.registers,Op.registers,hr]
  · intro q hq
    apply hall.pointer_preserved
    simp [copyCommand,copyLoop,copyStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMUnitProjection
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def projectionPrefix : List Op := [.pcopy 3 6,.pcopy 4 6]
def projectionNorm : List Op := [.sqrt 31 31,.literal 32 1,.sub 0 31 32]
def projectionFactor : Cmd := .cond (.real 0) .skip (.block [.div 32 32 31])
def projectionCommand : Cmd := .seq (.block projectionPrefix) (.seq dotCommand
  (.seq (.block projectionNorm) (.seq projectionFactor (.seq (.atom (.pcopy 3 6)) scaleCommand))))
lemma projection_command_correct (ω : PolySampIso.Streams) (D : ℕ) (x : Vec D) (s : Store)
    (hD : s.ptrs 15=D) (hx : readArray s.mem (s.ptrs 6) D=List.ofFn (fun i => x i)) :
    ∃ t k, k ≤ 16+16*D ∧ Eval ω projectionCommand s t k ∧
      t.mem=writeArray s.mem (s.ptrs 6) (List.ofFn (fun i => (unitProjection x) i)) ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31,32} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω projectionPrefix s
  have hu : Eval ω (.block projectionPrefix) s u 2 := eval_block ω projectionPrefix s
  have humem : u.mem=s.mem := rfl
  have hu15 : u.ptrs 15=D := by simpa [u,blockAct,projectionPrefix,Op.act] using hD
  have hu3 : u.ptrs 3=s.ptrs 6 := by simp [u,blockAct,projectionPrefix,Op.act]
  have hu4 : u.ptrs 4=s.ptrs 6 := by simp [u,blockAct,projectionPrefix,Op.act]
  obtain ⟨v,hv,h31,hmem,h3,h4,hgc,hec,hreg,hptr⟩ := dot_command_correct ω D x x u hu15
    (by simpa only [humem,hu3] using hx) (by simpa only [humem,hu4] using hx)
  let w := blockAct ω projectionNorm v
  have hw : Eval ω (.block projectionNorm) v w 3 := eval_block ω projectionNorm v
  have hw31 : w.regs 31=‖x‖ := by
    simp [w,blockAct,projectionNorm,Op.act,h31,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg x)]
  have hw32 : w.regs 32=1 := by simp [w,blockAct,projectionNorm,Op.act]
  have hw0 : w.regs 0=‖x‖-1 := by
    simp [w,blockAct,projectionNorm,Op.act,h31,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg x)]
  have hfactor : ∃ z k, k ≤ 3 ∧ Eval ω projectionFactor w z k ∧ z.mem=w.mem ∧ z.ptrs=w.ptrs ∧
      z.regs 32=(max 1 ‖x‖)⁻¹ := by
    by_cases hnorm : ‖x‖ ≤ 1
    · refine ⟨w,1,by omega,Eval.cond_yes (no := .block [.div 32 32 31]) ?_ (Eval.skip w),rfl,rfl,?_⟩
      · change w.regs 0 ≤ 0
        rw [hw0]
        linarith
      · rw [hw32,max_eq_left hnorm]
        norm_num
    · let z := blockAct ω [.div 32 32 31] w
      have he : Eval ω (.block [.div 32 32 31]) w z 1 := eval_block ω _ w
      refine ⟨z,3,by omega,Eval.cond_no (yes := .skip) ?_ he,rfl,rfl,?_⟩
      · change ¬w.regs 0 ≤ 0
        rw [hw0]
        linarith
      · simp [z,blockAct,Op.act,hw32,hw31,max_eq_right (by linarith : (1 : ℝ) ≤ ‖x‖)]
  obtain ⟨z,k,hk,hz,hzmem,hzptr,hz32⟩ := hfactor
  let a := Op.act ω z (.pcopy 3 6)
  have ha : Eval ω (.atom (.pcopy 3 6)) z a 1 := Eval.atom z _
  have hmemw : w.mem=s.mem := hmem.trans humem
  have hmema : a.mem=s.mem := hzmem.trans hmemw
  have hp6 : z.ptrs 6=s.ptrs 6 := by
    rw [hzptr]
    change v.ptrs 6=s.ptrs 6
    rw [hptr 6 (by simp)]
    simp [u,blockAct,projectionPrefix,Op.act]
  have ha3 : a.ptrs 3=s.ptrs 6 := by simp [a,Op.act,hp6]
  have ha15 : a.ptrs 15=(List.ofFn (fun i => x i)).length := by
    simp only [List.length_ofFn]
    change z.ptrs 15=(D : ℤ)
    rw [hzptr]
    change v.ptrs 15=(D : ℤ)
    rw [hptr 15 (by simp)]
    exact hu15
  obtain ⟨t,ht,htmem,ht3,htgc,htec,htreg,htptr⟩ := scale_command_correct ω (List.ofFn (fun i => x i)) a ha15
    (by simpa only [List.length_ofFn,hmema,ha3] using hx)
  have hall : Eval ω projectionCommand s t (2+(4+9*D)+(3+(k+(1+(3+7*D))))) := by
    convert! Eval.seq hu (Eval.seq hv (Eval.seq hw (Eval.seq hz (Eval.seq ha ht)))) using 1 <;> simp <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,2+(4+9*D)+(3+(k+(1+(3+7*D)))),by omega,hall,?_,hc.1,hc.2,?_,?_⟩
  · rw [htmem,hmema,ha3]
    congr 1
    simp only [List.map_ofFn,unitProjection,PiLp.smul_apply,smul_eq_mul]
    have ha32 : a.regs 32=(max 1 ‖x‖)⁻¹ := hz32
    simp only [ha32]
    congr 1
    funext i
    simp [Function.comp_apply,mul_comm]
  · intro r hr
    apply hall.register_preserved
    simp [projectionCommand,projectionPrefix,projectionNorm,projectionFactor,dotCommand,dotLoop,dotStep,
      scaleCommand,scaleLoop,scaleStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [projectionCommand,projectionPrefix,projectionNorm,projectionFactor,dotCommand,dotLoop,dotStep,
      scaleCommand,scaleLoop,scaleStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMVectorCalls
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def vectorMove (src dst : ℕ) : Cmd := .seq (.block [.pcopy 3 src,.pcopy 5 dst]) copyCommand
lemma vector_move_correct (ω : PolySampIso.Streams) (D src dst : ℕ) (x : Vec D) (s : Store)
    (hdst : dst ≠ 3) (hD : s.ptrs 15=D)
    (hx : readArray s.mem (s.ptrs src) D=List.ofFn (fun i => x i))
    (hdisj : s.ptrs src+(D : ℤ) ≤ s.ptrs dst ∨ s.ptrs dst+(D : ℤ) ≤ s.ptrs src) :
    ∃ t, Eval ω (vectorMove src dst) s t (5+7*D) ∧
      t.mem=writeArray s.mem (s.ptrs dst) (List.ofFn (fun i => x i)) ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 0 → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,5,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω [.pcopy 3 src,.pcopy 5 dst] s
  have hu : Eval ω (.block [.pcopy 3 src,.pcopy 5 dst]) s u 2 := eval_block ω _ s
  have um : u.mem=s.mem := rfl
  have u3 : u.ptrs 3=s.ptrs src := by simp [u,blockAct,Op.act]
  have u5 : u.ptrs 5=s.ptrs dst := by simp [u,blockAct,Op.act,hdst]
  obtain ⟨t,ht,hm,h3,h5,hgc,hec,hr,hp⟩ := copy_command_correct ω (List.ofFn (fun i => x i)) u
    (by simpa [u,blockAct,Op.act] using hD) (by simpa only [List.length_ofFn,um,u3] using hx)
    (by simpa only [List.length_ofFn,u3,u5] using hdisj)
  have hall : Eval ω (vectorMove src dst) s t (5+7*D) := by
    convert! Eval.seq hu ht using 1 <;> simp only [List.length_ofFn] <;> omega
  refine ⟨t,hall,?_,hgc,hec,?_,?_⟩
  · simpa only [um,u5] using hm
  · intro r h0
    exact hr r h0
  · intro q hq
    apply hall.pointer_preserved
    simp [vectorMove,copyCommand,copyLoop,copyStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
def vectorLinear (dst src ar br : ℕ) : Cmd := .seq (.block [.pcopy 3 dst,.pcopy 4 src,
  .literal 32 1,.mul 32 32 ar,.literal 33 1,.mul 33 33 br]) affineCommand
lemma vector_linear_correct (ω : PolySampIso.Streams) (D dst src ar br : ℕ) (x y : Vec D)
    (a b : ℝ) (s : Store) (hsrc : src ≠ 3) (har : ar ≠ 32) (hbr32 : br ≠ 32) (hbr33 : br ≠ 33)
    (hD : s.ptrs 15=D) (ha : s.regs ar=a) (hb : s.regs br=b)
    (hx : readArray s.mem (s.ptrs dst) D=List.ofFn (fun i => x i))
    (hy : readArray s.mem (s.ptrs src) D=List.ofFn (fun i => y i))
    (hdisj : s.ptrs src+(D : ℤ) ≤ s.ptrs dst) :
    ∃ t, Eval ω (vectorLinear dst src ar br) s t (9+11*D) ∧
      t.mem=writeArray s.mem (s.ptrs dst) (List.ofFn (fun i => (a • x+b • y) i)) ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,32,33} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let ops : List Op := [.pcopy 3 dst,.pcopy 4 src,.literal 32 1,.mul 32 32 ar,.literal 33 1,.mul 33 33 br]
  let u := blockAct ω ops s
  have hu : Eval ω (.block ops) s u 6 := eval_block ω _ s
  have um : u.mem=s.mem := rfl
  have u3 : u.ptrs 3=s.ptrs dst := by simp [u,ops,blockAct,Op.act]
  have u4 : u.ptrs 4=s.ptrs src := by simp [u,ops,blockAct,Op.act,hsrc]
  have u32 : u.regs 32=a := by simp [u,ops,blockAct,Op.act,har,ha]
  have u33 : u.regs 33=b := by simp [u,ops,blockAct,Op.act,hbr32,hbr33,hb]
  obtain ⟨t,ht,hm,h3,h4,hgc,hec,hr,hp⟩ := affine_vector_correct ω D x y u
    (by simpa [u,ops,blockAct,Op.act] using hD) (by simpa only [um,u3] using hx)
    (by simpa only [um,u4] using hy) (by simpa only [u3,u4] using hdisj)
  have hall : Eval ω (vectorLinear dst src ar br) s t (9+11*D) := by
    convert! Eval.seq hu ht using 1 <;> omega
  refine ⟨t,hall,?_,hgc,hec,?_,?_⟩
  · simpa only [um,u3,u32,u33] using hm
  · intro r hr
    apply hall.register_preserved
    simp [vectorLinear,affineCommand,affineLoop,affineStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [vectorLinear,affineCommand,affineLoop,affineStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
def vectorProject (q : ℕ) : Cmd := .seq (.atom (.pcopy 6 q)) projectionCommand
lemma vector_project_correct (ω : PolySampIso.Streams) (D q : ℕ) (x : Vec D) (s : Store)
    (hD : s.ptrs 15=D) (hx : readArray s.mem (s.ptrs q) D=List.ofFn (fun i => x i)) :
    ∃ t cost, Eval ω (vectorProject q) s t cost ∧ cost ≤ 17+16*D ∧
      t.mem=writeArray s.mem (s.ptrs q) (List.ofFn (fun i => unitProjection x i)) ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31,32} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ j, j ∉ ({3,4,6,12} : Finset ℕ) → t.ptrs j=s.ptrs j) := by
  let u := Op.act ω s (.pcopy 6 q)
  have hu : Eval ω (.atom (.pcopy 6 q)) s u 1 := Eval.atom s _
  obtain ⟨t,cost,hcost,ht,hm,hgc,hec,hr,hp⟩ := projection_command_correct ω D x u
    (by simpa [u,Op.act] using hD) (by simpa [u,Op.act] using hx)
  have hall : Eval ω (vectorProject q) s t (1+cost) := Eval.seq hu ht
  refine ⟨t,1+cost,hall,by omega,?_,hgc,hec,hr,?_⟩
  · simpa [u,Op.act] using hm
  · intro j hj
    rw [hp j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj ⊢; tauto)]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    simp [u,Op.act,hj.2.2.1]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMAcceleratedMidpoint
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def midpointCommand : Cmd := .seq (vectorMove 46 48) (vectorLinear 48 44 61 57)
lemma midpoint_command_correct (ω : PolySampIso.Streams) (D : ℕ) (x ag : Vec D) (α : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hα : s.regs 57=α) (ha : s.regs 61=1-α)
    (hx : readArray s.mem (s.ptrs 44) D=List.ofFn (fun i => x i))
    (hag : readArray s.mem (s.ptrs 46) D=List.ofFn (fun i => ag i))
    (hxm : s.ptrs 44+(D : ℤ) ≤ s.ptrs 48) (hagm : s.ptrs 46+(D : ℤ) ≤ s.ptrs 48) :
    ∃ t, Eval ω midpointCommand s t (14+18*D) ∧
      t.mem=writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => ((1-α) • ag+α • x) i)) ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,32,33} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,5,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨u,hu,hum,hugc,huec,hur,hup⟩ := vector_move_correct ω D 46 48 ag s (by omega) hD hag (Or.inl hagm)
  have u48 : u.ptrs 48=s.ptrs 48 := hup 48 (by decide)
  have u44 : u.ptrs 44=s.ptrs 44 := hup 44 (by decide)
  have uag : readArray u.mem (u.ptrs 48) D=List.ofFn (fun i => ag i) := by
    rw [hum,u48]
    simpa only [List.length_ofFn] using readArray_writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => ag i))
  have ux : readArray u.mem (u.ptrs 44) D=List.ofFn (fun i => x i) := by
    rw [hum,u44,readArray_write_after _ _ _ _ _ hxm]
    exact hx
  obtain ⟨t,ht,htm,htgc,htec,htr,htp⟩ := vector_linear_correct ω D 48 44 61 57 ag x (1-α) α u
    (by omega) (by omega) (by omega) (by omega) ((hup 15 (by decide)).trans hD)
    ((hur 61 (by omega)).trans ha) ((hur 57 (by omega)).trans hα) uag ux
    (by rwa [u48,u44])
  have hall : Eval ω midpointCommand s t (14+18*D) := by convert! Eval.seq hu ht using 1 <;> omega
  refine ⟨t,hall,?_,htgc.trans hugc,htec.trans huec,?_,?_⟩
  · rw [htm,hum,u48,writeArray_overwrite _ _ _ _ (by simp)]
  · intro r hr
    exact (htr r hr).trans (hur r (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr; tauto))
  · intro q hq
    exact (htp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)).trans
      (hup q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMGradientSample
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def signCommand : Cmd := .cond (.real 0) (.atom (.literal 33 1)) (.atom (.literal 33 (-1)))
lemma sign_command_correct (ω : PolySampIso.Streams) (s : Store) :
    ∃ t cost, Eval ω signCommand s t cost ∧ cost ≤ 3 ∧
      t={s with regs := Function.update s.regs 33 (thresholdStep 0 (-s.regs 0))} := by
  by_cases h : s.regs 0 ≤ 0
  · refine ⟨_,2,Eval.cond_yes (test := .real 0) (no := .atom (.literal 33 (-1))) h (Eval.atom s _),by omega,?_⟩
    simp [Op.act,thresholdStep,neg_nonneg.mpr h]
  · refine ⟨_,3,Eval.cond_no (test := .real 0) (yes := .atom (.literal 33 1)) h (Eval.atom s _),by omega,?_⟩
    simp [Op.act,thresholdStep,show ¬0 ≤ -s.regs 0 by linarith]
def gradientSamplePrefix : List Op := [.pcopy 54 52,.pcopy 3 48,.pcopy 4 54]
def gradientSampleMargin : List Op := [.load 0 4,.pinc 4,.load 1 4,.pinc 4,.pcopy 52 4,
  .load 2 42,.pinc 42,.sub 0 31 0,.mul 1 1 59,.mul 1 1 2,.add 0 0 1,
  .literal 3 0,.sub 0 3 0]
def gradientSampleSetup : List Op := [.literal 32 1,.pcopy 3 43,.pcopy 4 54]
def gradientSampleCommand : Cmd := .seq (.block gradientSamplePrefix) (.seq dotCommand
  (.seq (.block gradientSampleMargin) (.seq signCommand
    (.seq (.block gradientSampleSetup) (.seq affineCommand (.atom (.pinc 24)))))))
lemma gradient_sample_correct (ω : PolySampIso.Streams) (D : ℕ) (a v g : Vec D)
    (y b z r : ℝ) (s : Store) (hD : s.ptrs 15=D) (hr : s.regs 59=r)
    (ha : readArray s.mem (s.ptrs 52) D=List.ofFn (fun i => a i))
    (hy : s.mem (s.ptrs 52+D)=y) (hb : s.mem (s.ptrs 52+D+1)=b)
    (hz : s.mem (s.ptrs 42)=z)
    (hv : readArray s.mem (s.ptrs 48) D=List.ofFn (fun i => v i))
    (hg : readArray s.mem (s.ptrs 43) D=List.ofFn (fun i => g i))
    (hdisj : s.ptrs 52+(D : ℤ) ≤ s.ptrs 43) :
    ∃ t cost, Eval ω gradientSampleCommand s t cost ∧ cost ≤ 30+20*D ∧
      t.mem=writeArray s.mem (s.ptrs 43)
        (List.ofFn (fun i => (g+thresholdStep 0 (inner ℝ v a-y+r*b*z) • a) i)) ∧
      t.ptrs 52=s.ptrs 52+D+2 ∧ t.ptrs 42=s.ptrs 42+1 ∧ t.ptrs 24=s.ptrs 24+1 ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ∉ ({0,1,2,3,31,32,33} : Finset ℕ) → t.regs j=s.regs j) ∧
      (∀ q, q ∉ ({3,4,12,24,42,52,54} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω gradientSamplePrefix s
  have hu : Eval ω (.block gradientSamplePrefix) s u 3 := eval_block ω _ s
  have hum : u.mem=s.mem := rfl
  have hu3 : u.ptrs 3=s.ptrs 48 := by simp [u,blockAct,gradientSamplePrefix,Op.act]
  have hu4 : u.ptrs 4=s.ptrs 52 := by simp [u,blockAct,gradientSamplePrefix,Op.act]
  obtain ⟨w,hw,hw31,hwm,hw3,hw4,hwgc,hwec,hwr,hwp⟩ := dot_command_correct ω D v a u
    (by simpa [u,blockAct,gradientSamplePrefix,Op.act] using hD)
    (by simpa only [hum,hu3] using hv) (by simpa only [hum,hu4] using ha)
  have wm : w.mem=s.mem := hwm.trans hum
  have w4 : w.ptrs 4=s.ptrs 52+D := by simpa only [hu4] using hw4
  have w42 : w.ptrs 42=s.ptrs 42 := by rw [hwp 42 (by decide)]; rfl
  have w59 : w.regs 59=r := by rw [hwr 59 (by decide)]; exact hr
  let x := blockAct ω gradientSampleMargin w
  have hx : Eval ω (.block gradientSampleMargin) w x 13 := eval_block ω _ w
  have x0 : x.regs 0= -(inner ℝ v a-y+r*b*z) := by
    simp [x,blockAct,gradientSampleMargin,Op.act,wm,w4,hy,hb,w42,hz,hw31,w59]
    ring_nf
    simp
  have xm : x.mem=s.mem := wm
  have x42 : x.ptrs 42=s.ptrs 42+1 := by simp [x,blockAct,gradientSampleMargin,Op.act,w42]
  have x52 : x.ptrs 52=s.ptrs 52+D+2 := by simp [x,blockAct,gradientSampleMargin,Op.act,w4]; ring
  obtain ⟨f,cost,hf,hcost,hfeq⟩ := sign_command_correct ω x
  let astate := blockAct ω gradientSampleSetup f
  have has : Eval ω (.block gradientSampleSetup) f astate 3 := eval_block ω _ f
  have am : astate.mem=s.mem := by simp [astate,blockAct,gradientSampleSetup,Op.act,hfeq,xm]
  have a3 : astate.ptrs 3=s.ptrs 43 := by
    simp [astate,blockAct,gradientSampleSetup,Op.act,hfeq,x,blockAct,gradientSampleMargin,Op.act,
      hwp 43 (by decide),u,blockAct,gradientSamplePrefix]
  have a4 : astate.ptrs 4=s.ptrs 52 := by
    simp [astate,blockAct,gradientSampleSetup,Op.act,hfeq,x,blockAct,gradientSampleMargin,Op.act,
      hwp 54 (by decide),u,blockAct,gradientSamplePrefix]
  have a15 : astate.ptrs 15=D := by
    simp [astate,blockAct,gradientSampleSetup,Op.act,hfeq,x,blockAct,gradientSampleMargin,Op.act,
      hwp 15 (by decide),u,blockAct,gradientSamplePrefix,hD]
  have a32 : astate.regs 32=1 := by simp [astate,blockAct,gradientSampleSetup,Op.act]
  have a33 : astate.regs 33=thresholdStep 0 (inner ℝ v a-y+r*b*z) := by
    simp [astate,blockAct,gradientSampleSetup,Op.act,hfeq,x0]
  obtain ⟨j,hj,hjm,hj3,hj4,hjgc,hjec,hjr,hjp⟩ := affine_command_correct ω
    (List.ofFn (fun i => g i)) (List.ofFn (fun i => a i)) (by simp) astate
    (by simpa using a15) (by simpa only [am,a3,List.length_ofFn] using hg)
    (by simpa only [am,a4,List.length_ofFn] using ha)
    (by simpa only [a3,a4,List.length_ofFn] using hdisj)
  let t := Op.act ω j (.pinc 24)
  have ht : Eval ω (.atom (.pinc 24)) j t 1 := Eval.atom j _
  have hall : Eval ω gradientSampleCommand s t (3+(4+9*D)+(13+(cost+(3+(3+11*D+1))))) := by
    convert! Eval.seq hu (Eval.seq hw (Eval.seq hx (Eval.seq hf (Eval.seq has (Eval.seq hj ht))))) using 1 <;> simp only [List.length_ofFn] <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,_,hall,by omega,?_,?_,?_,?_,hc.1,hc.2,?_,?_⟩
  · change j.mem=_
    rw [hjm,am,a3,a32,a33]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [PiLp.add_apply,PiLp.smul_apply,mul_comm]
  · change j.ptrs 52=s.ptrs 52+D+2
    rw [hjp 52 (by decide)]
    simpa [astate,blockAct,gradientSampleSetup,Op.act,hfeq] using x52
  · change j.ptrs 42=s.ptrs 42+1
    rw [hjp 42 (by decide)]
    simpa [astate,blockAct,gradientSampleSetup,Op.act,hfeq] using x42
  · change j.ptrs 24+1=s.ptrs 24+1
    congr 1
    rw [hjp 24 (by decide)]
    simp [astate,blockAct,gradientSampleSetup,Op.act,hfeq,x,blockAct,gradientSampleMargin,Op.act,
      hwp 24 (by decide),u,blockAct,gradientSamplePrefix]
  · intro j hj
    apply hall.register_preserved
    simp [gradientSampleCommand,gradientSamplePrefix,gradientSampleMargin,gradientSampleSetup,signCommand,
      dotCommand,dotLoop,dotStep,affineCommand,affineLoop,affineStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [gradientSampleCommand,gradientSamplePrefix,gradientSampleMargin,gradientSampleSetup,signCommand,
      dotCommand,dotLoop,dotStep,affineCommand,affineLoop,affineStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMGradientLoop
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
noncomputable def gradientPartial {D : ℕ} (a : ℕ → Vec D) (y z : ℕ → ℝ) (v : Vec D) (r : ℝ) : ℕ → Vec D
  | 0 => 0
  | j+1 => gradientPartial a y z v r j+scalarSmoothedSubgradient r (a j) (y j) v (z j)
structure GradientInvariant (D : ℕ) (a : ℕ → Vec D) (y z : ℕ → ℝ) (v : Vec D) (r : ℝ)
    (s₀ : Store) (j : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ∈ ({15,16,43,48} : Finset ℕ) → s.ptrs q=s₀.ptrs q
  rowCursor : s.ptrs 52=s₀.ptrs 52+(j : ℤ)*((D : ℤ)+2)
  noiseCursor : s.ptrs 42=s₀.ptrs 42+(j : ℤ)
  counter : s.ptrs 24=(j : ℤ)+1
  parameter : s.regs 59=r
  memory : s.mem=writeArray s₀.mem (s₀.ptrs 43)
    (List.ofFn (fun i => gradientPartial a y z v r j i))
def gradientLoop : Cmd := .loop (.pointer 24 16) gradientSampleCommand
lemma gradient_invariant_step (ω : PolySampIso.Streams) (D n : ℕ) (a : ℕ → Vec D) (y z : ℕ → ℝ)
    (v : Vec D) (r : ℝ) (s₀ : Store)
    (hD : s₀.ptrs 15=D) (hn : s₀.ptrs 16=n)
    (hrows : s₀.ptrs 52+(n : ℤ)*((D : ℤ)+2) ≤ s₀.ptrs 43)
    (hnoise : s₀.ptrs 42+(n : ℤ) ≤ s₀.ptrs 43)
    (hquery : s₀.ptrs 43+(D : ℤ) ≤ s₀.ptrs 48)
    (ha : ∀ j, j<n → readArray s₀.mem (s₀.ptrs 52+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j<n → s₀.mem (s₀.ptrs 52+(j : ℤ)*((D : ℤ)+2)+D)=y j)
    (hb : ∀ j, j<n → s₀.mem (s₀.ptrs 52+(j : ℤ)*((D : ℤ)+2)+D+1)=‖a j‖)
    (hz : ∀ j, j<n → s₀.mem (s₀.ptrs 42+(j : ℤ))=z j)
    (hv : readArray s₀.mem (s₀.ptrs 48) D=List.ofFn (fun i => v i))
    (j : ℕ) (hj : j<n) (s : Store) (hs : GradientInvariant D a y z v r s₀ j s) :
    ∃ t cost, Eval ω gradientSampleCommand s t cost ∧ cost ≤ 30+20*D ∧
      GradientInvariant D a y z v r s₀ (j+1) t := by
  have h15 := (hs.fixedPointers 15 (by simp)).trans hD
  have h43 := hs.fixedPointers 43 (by simp)
  have h48 := hs.fixedPointers 48 (by simp)
  have hrow : s.ptrs 52+(D : ℤ)+2 ≤ s₀.ptrs 43 := by
    rw [hs.rowCursor]
    have hj' : (j : ℤ)+1 ≤ n := by exact_mod_cast (show j+1 ≤ n by omega)
    have hm := mul_le_mul_of_nonneg_right hj' (show (0 : ℤ) ≤ (D : ℤ)+2 by positivity)
    nlinarith only [hm,hrows]
  have hna : s.ptrs 42 < s₀.ptrs 43 := by rw [hs.noiseCursor]; omega
  have hread : readArray s.mem (s.ptrs 52) D=List.ofFn (fun i => a j i) := by
    rw [hs.memory,readArray_write_after _ _ _ _ _ (by omega),hs.rowCursor]
    exact ha j hj
  have hlabel : s.mem (s.ptrs 52+D)=y j := by
    rw [hs.memory,writeArray_outside _ _ _ _ (Or.inl (by omega)),hs.rowCursor]
    exact hy j hj
  have hnorm : s.mem (s.ptrs 52+D+1)=‖a j‖ := by
    rw [hs.memory,writeArray_outside _ _ _ _ (Or.inl (by omega)),hs.rowCursor]
    exact hb j hj
  have hzn : s.mem (s.ptrs 42)=z j := by
    rw [hs.memory,writeArray_outside _ _ _ _ (Or.inl hna),hs.noiseCursor]
    exact hz j hj
  have hq : readArray s.mem (s.ptrs 48) D=List.ofFn (fun i => v i) := by
    rw [hs.memory,h48,readArray_write_before _ _ _ _ _ (by simpa using hquery)]
    exact hv
  have hg : readArray s.mem (s.ptrs 43) D=List.ofFn (fun i => gradientPartial a y z v r j i) := by
    rw [hs.memory,h43]
    simpa only [List.length_ofFn] using readArray_writeArray s₀.mem (s₀.ptrs 43)
      (List.ofFn (fun i => gradientPartial a y z v r j i))
  obtain ⟨t,cost,he,hcost,hm,h52,h42,h24,hgc,hec,hreg,hptr⟩ := gradient_sample_correct ω D
    (a j) v (gradientPartial a y z v r j) (y j) ‖a j‖ (z j) r s h15 hs.parameter
    hread hlabel hnorm hzn hq hg (by rw [h43]; omega)
  refine ⟨t,cost,he,hcost,?_⟩
  constructor
  · intro q hq
    exact (hptr q (by simp only [Finset.mem_insert,Finset.mem_singleton] at hq; rcases hq with rfl|rfl|rfl|rfl <;> decide)).trans (hs.fixedPointers q hq)
  · rw [h52,hs.rowCursor]
    push_cast
    ring
  · rw [h42,hs.noiseCursor]
    push_cast
    ring
  · rw [h24,hs.counter]
    push_cast
    ring
  · exact (hreg 59 (by decide)).trans hs.parameter
  · rw [hm,hs.memory,h43,writeArray_overwrite _ _ _ _ (by simp)]
    rfl
lemma gradient_loop_correct (ω : PolySampIso.Streams) (D n : ℕ) (a : ℕ → Vec D) (y z : ℕ → ℝ)
    (v : Vec D) (r : ℝ) (s₀ s : Store)
    (hD : s₀.ptrs 15=D) (hn : s₀.ptrs 16=n)
    (hrows : s₀.ptrs 52+(n : ℤ)*((D : ℤ)+2) ≤ s₀.ptrs 43)
    (hnoise : s₀.ptrs 42+(n : ℤ) ≤ s₀.ptrs 43)
    (hquery : s₀.ptrs 43+(D : ℤ) ≤ s₀.ptrs 48)
    (ha : ∀ j, j<n → readArray s₀.mem (s₀.ptrs 52+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j<n → s₀.mem (s₀.ptrs 52+(j : ℤ)*((D : ℤ)+2)+D)=y j)
    (hb : ∀ j, j<n → s₀.mem (s₀.ptrs 52+(j : ℤ)*((D : ℤ)+2)+D+1)=‖a j‖)
    (hz : ∀ j, j<n → s₀.mem (s₀.ptrs 42+(j : ℤ))=z j)
    (hv : readArray s₀.mem (s₀.ptrs 48) D=List.ofFn (fun i => v i))
    (hs : GradientInvariant D a y z v r s₀ 0 s) :
    ∃ t cost, Eval ω gradientLoop s t cost ∧ cost ≤ 2+n*(32+20*D) ∧
      GradientInvariant D a y z v r s₀ n t := by
  have htrue : ∀ j, j<n → ∀ u, GradientInvariant D a y z v r s₀ j u → Test.holds u (.pointer 24 16) := by
    intro j hj u hu
    change u.ptrs 24 ≤ u.ptrs 16
    rw [hu.counter,hu.fixedPointers 16 (by simp),hn]
    omega
  have hfalse : ∀ u, GradientInvariant D a y z v r s₀ n u → ¬Test.holds u (.pointer 24 16) := by
    intro u hu
    change ¬u.ptrs 24 ≤ u.ptrs 16
    rw [hu.counter,hu.fixedPointers 16 (by simp),hn]
    omega
  have hbody : ∀ j, j<n → ∀ u, GradientInvariant D a y z v r s₀ j u →
      ∃ t cost, cost ≤ 30+20*D ∧ Eval ω gradientSampleCommand u t cost ∧ GradientInvariant D a y z v r s₀ (j+1) t := by
    intro j hj u hu
    obtain ⟨t,cost,he,hcost,ht⟩ := gradient_invariant_step ω D n a y z v r s₀ hD hn hrows hnoise hquery ha hy hb hz hv j hj u hu
    exact ⟨t,cost,hcost,he,ht⟩
  obtain ⟨t,cost,hcost,he,ht⟩ := eval_loop_invariant ω (.pointer 24 16) gradientSampleCommand
    n (30+20*D) (GradientInvariant D a y z v r s₀) htrue hfalse hbody s hs
  refine ⟨t,cost,he,?_,ht⟩
  convert! hcost using 1 <;> ring
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMGradientSum
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def gradientSumPrefix : List Op := [.pcopy 5 43,.literal 32 0,.pset 24 1]
def gradientSumCommand : Cmd := .seq (.block gradientSumPrefix) (.seq fillCommand gradientLoop)
lemma gradient_sum_correct (ω : PolySampIso.Streams) (D n : ℕ) (a : ℕ → Vec D) (y z : ℕ → ℝ)
    (v : Vec D) (r : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hn : s.ptrs 16=n) (hr : s.regs 59=r)
    (hrows : s.ptrs 52+(n : ℤ)*((D : ℤ)+2) ≤ s.ptrs 43)
    (hnoise : s.ptrs 42+(n : ℤ) ≤ s.ptrs 43)
    (hquery : s.ptrs 43+(D : ℤ) ≤ s.ptrs 48)
    (ha : ∀ j, j<n → readArray s.mem (s.ptrs 52+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j<n → s.mem (s.ptrs 52+(j : ℤ)*((D : ℤ)+2)+D)=y j)
    (hb : ∀ j, j<n → s.mem (s.ptrs 52+(j : ℤ)*((D : ℤ)+2)+D+1)=‖a j‖)
    (hz : ∀ j, j<n → s.mem (s.ptrs 42+(j : ℤ))=z j)
    (hv : readArray s.mem (s.ptrs 48) D=List.ofFn (fun i => v i)) :
    ∃ t cost, Eval ω gradientSumCommand s t cost ∧ cost ≤ 8+5*D+n*(32+20*D) ∧
      t.mem=writeArray s.mem (s.ptrs 43) (List.ofFn (fun i => gradientPartial a y z v r n i)) ∧
      t.ptrs 52=s.ptrs 52+(n : ℤ)*((D : ℤ)+2) ∧ t.ptrs 42=s.ptrs 42+n ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ∉ ({0,1,2,3,31,32,33} : Finset ℕ) → t.regs j=s.regs j) ∧
      (∀ q, q ∉ ({3,4,5,12,24,42,52,54} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω gradientSumPrefix s
  have hu : Eval ω (.block gradientSumPrefix) s u 3 := eval_block ω _ s
  have hu5 : u.ptrs 5=s.ptrs 43 := by simp [u,blockAct,gradientSumPrefix,Op.act]
  have hu32 : u.regs 32=0 := by simp [u,blockAct,gradientSumPrefix,Op.act]
  obtain ⟨w,hw,hwm,hw5,hwr,hwgc,hwec,hwp⟩ := fill_command_correct ω D u
    (by simpa [u,blockAct,gradientSumPrefix,Op.act] using hD)
  have hinit : GradientInvariant D a y z v r s 0 w := by
    constructor
    · intro q hq
      rw [hwp q (by simp only [Finset.mem_insert,Finset.mem_singleton] at hq; rcases hq with rfl|rfl|rfl|rfl <;> omega)
        (by simp only [Finset.mem_insert,Finset.mem_singleton] at hq; rcases hq with rfl|rfl|rfl|rfl <;> omega)]
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> simp [u,blockAct,gradientSumPrefix,Op.act]
    · rw [hwp 52 (by omega) (by omega)]
      simp [u,blockAct,gradientSumPrefix,Op.act]
    · rw [hwp 42 (by omega) (by omega)]
      simp [u,blockAct,gradientSumPrefix,Op.act]
    · rw [hwp 24 (by omega) (by omega)]
      simp [u,blockAct,gradientSumPrefix,Op.act]
    · rw [hwr]
      exact hr
    · rw [hwm,hu5,hu32]
      change writeArray s.mem (s.ptrs 43) (List.replicate D 0)=_
      congr 1
      simp [gradientPartial,List.ofFn_const]
  obtain ⟨t,cost,he,hcost,ht⟩ := gradient_loop_correct ω D n a y z v r s w hD hn hrows hnoise hquery
    ha hy hb hz hv hinit
  have hall : Eval ω gradientSumCommand s t (3+(3+5*D)+cost) := by
    convert! Eval.seq hu (Eval.seq hw he) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,_,hall,by omega,ht.memory,ht.rowCursor,ht.noiseCursor,hc.1,hc.2,?_,?_⟩
  · intro j hj
    apply hall.register_preserved
    simp [gradientSumCommand,gradientSumPrefix,gradientLoop,gradientSampleCommand,gradientSamplePrefix,
      gradientSampleMargin,gradientSampleSetup,signCommand,fillCommand,fillLoop,fillStep,
      dotCommand,dotLoop,dotStep,affineCommand,affineLoop,affineStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [gradientSumCommand,gradientSumPrefix,gradientLoop,gradientSampleCommand,gradientSamplePrefix,
      gradientSampleMargin,gradientSampleSetup,signCommand,fillCommand,fillLoop,fillStep,
      dotCommand,dotLoop,dotStep,affineCommand,affineLoop,affineStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMGradientFinish
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def gradientScaleSetup : List Op := [.pcopy 3 43,.literal 32 1,.mul 32 32 59]
def gradientNoiseSetup : List Op := [.pcopy 3 43,.pcopy 4 42,.literal 32 1,.literal 33 1,.mul 33 33 50]
def gradientFinishCommand : Cmd := .seq (.block gradientScaleSetup) (.seq scaleCommand
  (.seq (.block gradientNoiseSetup) (.seq affineCommand (.atom (.pcopy 42 4)))))
lemma gradient_finish_correct (ω : PolySampIso.Streams) (D : ℕ) (g η : Vec D) (r τ : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hr : s.regs 59=r) (hτ : s.regs 50=τ)
    (hg : readArray s.mem (s.ptrs 43) D=List.ofFn (fun i => g i))
    (hη : readArray s.mem (s.ptrs 42) D=List.ofFn (fun i => η i))
    (hdisj : s.ptrs 42+(D : ℤ) ≤ s.ptrs 43) :
    ∃ t, Eval ω gradientFinishCommand s t (15+18*D) ∧
      t.mem=writeArray s.mem (s.ptrs 43) (List.ofFn (fun i => (r • g+τ • η) i)) ∧
      t.ptrs 42=s.ptrs 42+D ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ∉ ({0,1,32,33} : Finset ℕ) → t.regs j=s.regs j) ∧
      (∀ q, q ∉ ({3,4,12,42} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω gradientScaleSetup s
  have hu : Eval ω (.block gradientScaleSetup) s u 3 := eval_block ω _ s
  have um : u.mem=s.mem := rfl
  have u3 : u.ptrs 3=s.ptrs 43 := by simp [u,blockAct,gradientScaleSetup,Op.act]
  have u32 : u.regs 32=r := by simp [u,blockAct,gradientScaleSetup,Op.act,hr]
  obtain ⟨v,hv,hvm,hv3,hvgc,hvec,hvr,hvp⟩ := scale_vector_correct ω D g u
    (by simpa [u,blockAct,gradientScaleSetup,Op.act] using hD) (by simpa only [um,u3] using hg)
  have vm : v.mem=writeArray s.mem (s.ptrs 43) (List.ofFn (fun i => (r • g) i)) := by
    simpa only [um,u3,u32] using hvm
  have v43 : v.ptrs 43=s.ptrs 43 := by rw [hvp 43 (by omega) (by omega)]; rfl
  have v42 : v.ptrs 42=s.ptrs 42 := by rw [hvp 42 (by omega) (by omega)]; rfl
  let w := blockAct ω gradientNoiseSetup v
  have hw : Eval ω (.block gradientNoiseSetup) v w 5 := eval_block ω _ v
  have wm : w.mem=v.mem := rfl
  have w3 : w.ptrs 3=s.ptrs 43 := by simp [w,blockAct,gradientNoiseSetup,Op.act,v43]
  have w4 : w.ptrs 4=s.ptrs 42 := by simp [w,blockAct,gradientNoiseSetup,Op.act,v42]
  have w32 : w.regs 32=1 := by simp [w,blockAct,gradientNoiseSetup,Op.act]
  have w33 : w.regs 33=τ := by
    simp [w,blockAct,gradientNoiseSetup,Op.act,hvr 50 (by omega),u,blockAct,gradientScaleSetup,hτ]
  have wg : readArray w.mem (w.ptrs 3) D=List.ofFn (fun i => (r • g) i) := by
    rw [wm,vm,w3]
    simpa only [List.length_ofFn] using readArray_writeArray s.mem (s.ptrs 43) (List.ofFn (fun i => (r • g) i))
  have wη : readArray w.mem (w.ptrs 4) D=List.ofFn (fun i => η i) := by
    rw [wm,vm,w4,readArray_write_after _ _ _ _ _ hdisj]
    exact hη
  have w15 : w.ptrs 15=D := by
    simp [w,blockAct,gradientNoiseSetup,Op.act,hvp 15 (by omega) (by omega),u,blockAct,gradientScaleSetup,hD]
  obtain ⟨j,hj,hjm,hj3,hj4,hjgc,hjec,hjr,hjp⟩ := affine_vector_correct ω D (r • g) η w w15 wg wη
    (by simpa only [w3,w4] using hdisj)
  let t := Op.act ω j (.pcopy 42 4)
  have ht : Eval ω (.atom (.pcopy 42 4)) j t 1 := Eval.atom j _
  have hall : Eval ω gradientFinishCommand s t (15+18*D) := by
    convert! Eval.seq hu (Eval.seq hv (Eval.seq hw (Eval.seq hj ht))) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,?_,?_,hc.1,hc.2,?_,?_⟩
  · change j.mem=_
    rw [hjm,wm,vm,w3,w32,w33,one_smul,writeArray_overwrite _ _ _ _ (by simp)]
  · change j.ptrs 4=s.ptrs 42+D
    simpa only [w4] using hj4
  · intro j hj
    apply hall.register_preserved
    simp [gradientFinishCommand,gradientScaleSetup,gradientNoiseSetup,scaleCommand,scaleLoop,scaleStep,
      affineCommand,affineLoop,affineStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [gradientFinishCommand,gradientScaleSetup,gradientNoiseSetup,scaleCommand,scaleLoop,scaleStep,
      affineCommand,affineLoop,affineStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMFullGradient
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
open scoped BigOperators
def fullGradientCommand : Cmd := .seq gradientSumCommand gradientFinishCommand
lemma full_gradient_correct (ω : PolySampIso.Streams) (D n : ℕ) (a : ℕ → Vec D) (y z : ℕ → ℝ)
    (v η : Vec D) (r τ : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hn : s.ptrs 16=n) (hr : s.regs 59=r) (hτ : s.regs 50=τ)
    (hrows : s.ptrs 52+(n : ℤ)*((D : ℤ)+2) ≤ s.ptrs 43)
    (hnoise : s.ptrs 42+(n : ℤ)+(D : ℤ) ≤ s.ptrs 43)
    (hquery : s.ptrs 43+(D : ℤ) ≤ s.ptrs 48)
    (ha : ∀ j, j<n → readArray s.mem (s.ptrs 52+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j<n → s.mem (s.ptrs 52+(j : ℤ)*((D : ℤ)+2)+D)=y j)
    (hb : ∀ j, j<n → s.mem (s.ptrs 52+(j : ℤ)*((D : ℤ)+2)+D+1)=‖a j‖)
    (hz : ∀ j, j<n → s.mem (s.ptrs 42+(j : ℤ))=z j)
    (hη : readArray s.mem (s.ptrs 42+n) D=List.ofFn (fun i => η i))
    (hv : readArray s.mem (s.ptrs 48) D=List.ofFn (fun i => v i)) :
    ∃ t cost, Eval ω fullGradientCommand s t cost ∧ cost ≤ 23+23*D+n*(32+20*D) ∧
      t.mem=writeArray s.mem (s.ptrs 43) (List.ofFn (fun i => (r • gradientPartial a y z v r n+τ • η) i)) ∧
      t.ptrs 52=s.ptrs 52+(n : ℤ)*((D : ℤ)+2) ∧ t.ptrs 42=s.ptrs 42+n+D ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ∉ ({0,1,2,3,31,32,33} : Finset ℕ) → t.regs j=s.regs j) ∧
      (∀ q, q ∉ ({3,4,5,12,24,42,52,54} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨u,cost,hu,hcost,hum,hu52,hu42,hugc,huec,hur,hup⟩ := gradient_sum_correct ω D n a y z v r s
    hD hn hr hrows (by omega) hquery ha hy hb hz hv
  have u43 : u.ptrs 43=s.ptrs 43 := hup 43 (by decide)
  have ug : readArray u.mem (u.ptrs 43) D=List.ofFn (fun i => gradientPartial a y z v r n i) := by
    rw [hum,u43]
    simpa only [List.length_ofFn] using readArray_writeArray s.mem (s.ptrs 43)
      (List.ofFn (fun i => gradientPartial a y z v r n i))
  have uη : readArray u.mem (u.ptrs 42) D=List.ofFn (fun i => η i) := by
    rw [hum,hu42,readArray_write_after _ _ _ _ _ hnoise]
    exact hη
  obtain ⟨t,ht,htm,ht42,htgc,htec,htr,htp⟩ := gradient_finish_correct ω D (gradientPartial a y z v r n) η r τ u
    ((hup 15 (by decide)).trans hD) ((hur 59 (by decide)).trans hr) ((hur 50 (by decide)).trans hτ) ug uη
    (by rw [u43,hu42]; exact hnoise)
  have hall : Eval ω fullGradientCommand s t (cost+(15+18*D)) := Eval.seq hu ht
  refine ⟨t,_,hall,by omega,?_,?_,?_,htgc.trans hugc,htec.trans huec,?_,?_⟩
  · rw [htm,hum,u43,writeArray_overwrite _ _ _ _ (by simp)]
  · rw [htp 52 (by decide)]
    exact hu52
  · rw [ht42,hu42]
  · intro j hj
    exact (htr j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj ⊢; tauto)).trans (hur j hj)
  · intro q hq
    exact (htp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)).trans (hup q hq)
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMFiniteGradient
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
open scoped BigOperators
noncomputable def extendFin {n : ℕ} {α : Type*} (x : Fin n → α) (a : α) (j : ℕ) : α :=
  if h : j<n then x ⟨j,h⟩ else a
@[simp] lemma extendFin_val {n : ℕ} {α : Type*} (x : Fin n → α) (a : α) (i : Fin n) :
    extendFin x a i.val=x i := by simp [extendFin,i.isLt]
lemma gradientPartial_sum {D : ℕ} (a : ℕ → Vec D) (y z : ℕ → ℝ) (v : Vec D) (r : ℝ) (n : ℕ) :
    gradientPartial a y z v r n=∑ j ∈ Finset.range n, scalarSmoothedSubgradient r (a j) (y j) v (z j) := by
  induction n with
  | zero => simp [gradientPartial]
  | succ n ih => rw [gradientPartial,Finset.sum_range_succ,ih]
lemma gradientPartial_finite {D n : ℕ} (a : Fin n → Vec D) (y z : Fin n → ℝ) (v : Vec D) (r : ℝ) :
    gradientPartial (extendFin a 0) (extendFin y 0) (extendFin z 0) v r n=
      ∑ i : Fin n, scalarSmoothedSubgradient r (a i) (y i) v (z i) := by
  rw [gradientPartial_sum,Finset.sum_range]
  simp
lemma finite_gradient_correct (ω : PolySampIso.Streams) (D n : ℕ) (a : Fin n → Vec D) (y : Fin n → ℝ)
    (v : Vec D) (noise : RegressionNoise n D) (τ : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hn : s.ptrs 16=n) (hr : s.regs 59=(n : ℝ)⁻¹) (hτ : s.regs 50=τ)
    (hrows : s.ptrs 52+(n : ℤ)*((D : ℤ)+2) ≤ s.ptrs 43)
    (hnoise : s.ptrs 42+(n : ℤ)+(D : ℤ) ≤ s.ptrs 43)
    (hquery : s.ptrs 43+(D : ℤ) ≤ s.ptrs 48)
    (ha : ∀ j : Fin n, readArray s.mem (s.ptrs 52+(j.val : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j : Fin n, s.mem (s.ptrs 52+(j.val : ℤ)*((D : ℤ)+2)+D)=y j)
    (hb : ∀ j : Fin n, s.mem (s.ptrs 52+(j.val : ℤ)*((D : ℤ)+2)+D+1)=‖a j‖)
    (hz : ∀ j : Fin n, s.mem (s.ptrs 42+(j.val : ℤ))=noise.1 j)
    (hη : readArray s.mem (s.ptrs 42+n) D=List.ofFn (fun i => noise.2 i))
    (hv : readArray s.mem (s.ptrs 48) D=List.ofFn (fun i => v i)) :
    ∃ t cost, Eval ω fullGradientCommand s t cost ∧ cost ≤ 23+23*D+n*(32+20*D) ∧
      t.mem=writeArray s.mem (s.ptrs 43)
        (List.ofFn (fun i => noisyRegressionOracle ((n : ℝ)⁻¹) τ a y v noise i)) ∧
      t.ptrs 52=s.ptrs 52+(n : ℤ)*((D : ℤ)+2) ∧ t.ptrs 42=s.ptrs 42+n+D ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ∉ ({0,1,2,3,31,32,33} : Finset ℕ) → t.regs j=s.regs j) ∧
      (∀ q, q ∉ ({3,4,5,12,24,42,52,54} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨t,cost,he,hcost,hm,h52,h42,hgc,hec,hreg,hptr⟩ := full_gradient_correct ω D n (extendFin a 0)
    (extendFin y 0) (extendFin noise.1 0) v noise.2 ((n : ℝ)⁻¹) τ s hD hn hr hτ hrows hnoise hquery
    (fun j hj => by simpa [extendFin,hj] using ha ⟨j,hj⟩)
    (fun j hj => by simpa [extendFin,hj] using hy ⟨j,hj⟩)
    (fun j hj => by simpa [extendFin,hj] using hb ⟨j,hj⟩)
    (fun j hj => by simpa [extendFin,hj] using hz ⟨j,hj⟩) hη hv
  refine ⟨t,cost,he,hcost,?_,h52,h42,hgc,hec,hreg,hptr⟩
  rw [hm,gradientPartial_finite]
  rfl
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMProjectedStep
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def projectedStep (q negStepReg : ℕ) : Cmd := .seq (vectorLinear q 43 55 negStepReg) (vectorProject q)
lemma projected_step_correct (ω : PolySampIso.Streams) (D q stepReg : ℕ) (hq : 40 ≤ q) (hstep : 50 ≤ stepReg)
    (x g : Vec D) (lam : ℝ) (s : Store) (hD : s.ptrs 15=D) (h1 : s.regs 55=1) (hlam : s.regs stepReg= -lam)
    (hx : readArray s.mem (s.ptrs q) D=List.ofFn (fun i => x i))
    (hg : readArray s.mem (s.ptrs 43) D=List.ofFn (fun i => g i))
    (hdisj : s.ptrs 43+(D : ℤ) ≤ s.ptrs q) :
    ∃ t cost, Eval ω (projectedStep q stepReg) s t cost ∧ cost ≤ 26+27*D ∧
      t.mem=writeArray s.mem (s.ptrs q) (List.ofFn (fun i => unitProjection (x-lam • g) i)) ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31,32,33} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ j, j ∉ ({3,4,6,12} : Finset ℕ) → t.ptrs j=s.ptrs j) := by
  obtain ⟨u,hu,hum,hugc,huec,hur,hup⟩ := vector_linear_correct ω D q 43 55 stepReg x g 1 (-lam) s
    (by omega) (by omega) (by omega) (by omega) hD h1 hlam hx hg hdisj
  have uq : u.ptrs q=s.ptrs q := hup q (by simp; omega)
  have um : u.mem=writeArray s.mem (s.ptrs q) (List.ofFn (fun i => (x-lam • g) i)) := by
    simpa only [one_smul,neg_smul,sub_eq_add_neg] using hum
  have ux : readArray u.mem (u.ptrs q) D=List.ofFn (fun i => (x-lam • g) i) := by
    rw [um,uq]
    simpa only [List.length_ofFn] using readArray_writeArray s.mem (s.ptrs q) (List.ofFn (fun i => (x-lam • g) i))
  obtain ⟨t,cost,ht,hcost,htm,htgc,htec,htr,htp⟩ := vector_project_correct ω D q (x-lam • g) u
    ((hup 15 (by decide)).trans hD) ux
  have hall : Eval ω (projectedStep q stepReg) s t (9+11*D+cost) := Eval.seq hu ht
  refine ⟨t,_,hall,by omega,?_,htgc.trans hugc,htec.trans huec,?_,?_⟩
  · rw [htm,um,uq,writeArray_overwrite _ _ _ _ (by simp)]
  · intro r hr
    exact (htr r (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr ⊢; tauto)).trans
      (hur r (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr ⊢; tauto))
  · intro j hj
    exact (htp j hj).trans (hup j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj ⊢; tauto))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMAcceleratedUpdate
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def acceleratedUpdateCommand : Cmd := .seq (projectedStep 44 62)
  (.seq (vectorMove 48 46) (projectedStep 46 63))
lemma accelerated_update_correct (ω : PolySampIso.Streams) (D : ℕ) (x md g : Vec D) (lam β : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (h1 : s.regs 55=1) (hlam : s.regs 62= -lam) (hβ : s.regs 63= -β)
    (hx : readArray s.mem (s.ptrs 44) D=List.ofFn (fun i => x i))
    (hmd : readArray s.mem (s.ptrs 48) D=List.ofFn (fun i => md i))
    (hg : readArray s.mem (s.ptrs 43) D=List.ofFn (fun i => g i))
    (hgx : s.ptrs 43+(D : ℤ) ≤ s.ptrs 44) (hxag : s.ptrs 44+(D : ℤ) ≤ s.ptrs 46)
    (hagm : s.ptrs 46+(D : ℤ) ≤ s.ptrs 48) :
    ∃ t cost, Eval ω acceleratedUpdateCommand s t cost ∧ cost ≤ 57+61*D ∧
      t.mem=writeArray (writeArray s.mem (s.ptrs 44) (List.ofFn (fun i => unitProjection (x-lam • g) i)))
        (s.ptrs 46) (List.ofFn (fun i => unitProjection (md-β • g) i)) ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31,32,33} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,5,6,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨u,cu,hu,hcu,hum,hugc,huec,hur,hup⟩ := projected_step_correct ω D 44 62 (by omega) (by omega)
    x g lam s hD h1 hlam hx hg hgx
  have u48 : u.ptrs 48=s.ptrs 48 := hup 48 (by decide)
  have u46 : u.ptrs 46=s.ptrs 46 := hup 46 (by decide)
  have umd : readArray u.mem (u.ptrs 48) D=List.ofFn (fun i => md i) := by
    rw [hum,u48,readArray_write_before _ _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    exact hmd
  obtain ⟨v,hv,hvm,hvgc,hvec,hvr,hvp⟩ := vector_move_correct ω D 48 46 md u (by omega)
    ((hup 15 (by decide)).trans hD) umd (Or.inr (by rwa [u48,u46]))
  have v46 : v.ptrs 46=s.ptrs 46 := (hvp 46 (by decide)).trans u46
  have v43 : v.ptrs 43=s.ptrs 43 := (hvp 43 (by decide)).trans (hup 43 (by decide))
  have vmd : readArray v.mem (v.ptrs 46) D=List.ofFn (fun i => md i) := by
    rw [hvm,v46,u46]
    simpa only [List.length_ofFn] using readArray_writeArray u.mem (s.ptrs 46) (List.ofFn (fun i => md i))
  have vg : readArray v.mem (v.ptrs 43) D=List.ofFn (fun i => g i) := by
    rw [hvm,v43,u46,readArray_write_after _ _ _ _ _ (by omega),hum,
      readArray_write_after _ _ _ _ _ hgx]
    exact hg
  obtain ⟨t,ct,ht,hct,htm,htgc,htec,htr,htp⟩ := projected_step_correct ω D 46 63 (by omega) (by omega)
    md g β v ((hvp 15 (by decide)).trans ((hup 15 (by decide)).trans hD))
    ((hvr 55 (by omega)).trans ((hur 55 (by decide)).trans h1))
    ((hvr 63 (by omega)).trans ((hur 63 (by decide)).trans hβ)) vmd vg
    (by rw [v43,v46]; omega)
  have hall : Eval ω acceleratedUpdateCommand s t (cu+(5+7*D)+ct) := by
    convert! Eval.seq hu (Eval.seq hv ht) using 1 <;> omega
  refine ⟨t,_,hall,by omega,?_,htgc.trans (hvgc.trans hugc),htec.trans (hvec.trans huec),?_,?_⟩
  · rw [htm,hvm,v46,u46,writeArray_overwrite _ _ _ _ (by simp),hum]
  · intro r hr
    exact (htr r hr).trans ((hvr r (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr; tauto)).trans (hur r hr))
  · intro q hq
    exact (htp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)).trans
      ((hvp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)).trans
        (hup q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMAcceleratedStep
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
def acceleratedStepCommand : Cmd := .seq (.block acceleratedParameters) (.seq midpointCommand
  (.seq (.atom (.pcopy 52 53)) (.seq fullGradientCommand
    (.seq acceleratedUpdateCommand (.atom (.pinc 21))))))
lemma accelerated_step_correct (ω : PolySampIso.Streams) (D n k : ℕ) (a : Fin n → Vec D) (y : Fin n → ℝ)
    (noise : RegressionNoise n D) (x ag : Vec D) (τ β : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hn : s.ptrs 16=n) (hk : s.ptrs 21=k)
    (hτ : s.regs 50=τ) (hβ : s.regs 51=β) (h1 : s.regs 55=1) (h2 : s.regs 56=2) (hr : s.regs 59=(n : ℝ)⁻¹)
    (hx : readArray s.mem (s.ptrs 44) D=List.ofFn (fun i => x i))
    (hag : readArray s.mem (s.ptrs 46) D=List.ofFn (fun i => ag i))
    (hgx : s.ptrs 43+(D : ℤ) ≤ s.ptrs 44) (hxag : s.ptrs 44+(D : ℤ) ≤ s.ptrs 46)
    (hagm : s.ptrs 46+(D : ℤ) ≤ s.ptrs 48)
    (hrows : s.ptrs 53+(n : ℤ)*((D : ℤ)+2) ≤ s.ptrs 43)
    (hnoise : s.ptrs 42+(n : ℤ)+(D : ℤ) ≤ s.ptrs 43)
    (ha : ∀ j : Fin n, readArray s.mem (s.ptrs 53+(j.val : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j : Fin n, s.mem (s.ptrs 53+(j.val : ℤ)*((D : ℤ)+2)+D)=y j)
    (hb : ∀ j : Fin n, s.mem (s.ptrs 53+(j.val : ℤ)*((D : ℤ)+2)+D+1)=‖a j‖)
    (hz : ∀ j : Fin n, s.mem (s.ptrs 42+(j.val : ℤ))=noise.1 j)
    (hη : readArray s.mem (s.ptrs 42+n) D=List.ofFn (fun i => noise.2 i)) :
    let md := (1-accelAlpha k) • ag+accelAlpha k • x
    let g := noisyRegressionOracle ((n : ℝ)⁻¹) τ a y md noise
    ∃ t cost, Eval ω acceleratedStepCommand s t cost ∧ cost ≤ 105+102*D+n*(32+20*D) ∧
      t.mem=writeArray (writeArray (writeArray (writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => md i)))
        (s.ptrs 43) (List.ofFn (fun i => g i)))
        (s.ptrs 44) (List.ofFn (fun i => unitProjection (x-accelLambda β k • g) i)))
        (s.ptrs 46) (List.ofFn (fun i => unitProjection (md-β • g) i)) ∧
      t.ptrs 42=s.ptrs 42+n+D ∧ t.ptrs 21=s.ptrs 21+1 ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ∉ ({0,1,2,3,31,32,33,57,58,60,61,62,63} : Finset ℕ) → t.regs j=s.regs j) ∧
      (∀ q, q ∉ ({3,4,5,6,12,21,24,42,52,54} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  dsimp only
  let md := (1-accelAlpha k) • ag+accelAlpha k • x
  let g := noisyRegressionOracle ((n : ℝ)⁻¹) τ a y md noise
  let u := blockAct ω acceleratedParameters s
  obtain ⟨hu,hum,hup,hu57,hu58,hu61,hu62,hu63,hur⟩ := accelerated_parameters_correct ω k β s hk hβ h1 h2
  obtain ⟨w,hw,hwm,hwgc,hwec,hwr,hwp⟩ := midpoint_command_correct ω D x ag (accelAlpha k) u
    (by rw [hup]; exact hD) hu57 hu61 (by rwa [hum,hup]) (by rwa [hum,hup])
    (by rw [hup]; omega) (by rwa [hup])
  have wp (q : ℕ) (hq : q ∉ ({3,4,5,12} : Finset ℕ)) : w.ptrs q=s.ptrs q := (hwp q hq).trans (congrFun hup q)
  have wm : w.mem=writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => md i)) := by
    rw [show u.mem=s.mem from hum,show u.ptrs=s.ptrs from hup] at hwm
    exact hwm
  let b := Op.act ω w (.pcopy 52 53)
  have hbstate : Eval ω (.atom (.pcopy 52 53)) w b 1 := Eval.atom w _
  have bp (q : ℕ) (hq : q ∉ ({3,4,5,12,52} : Finset ℕ)) : b.ptrs q=s.ptrs q := by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    simp only [b,Op.act,Function.update_of_ne hq.2.2.2.2]
    exact wp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; tauto)
  have b52 : b.ptrs 52=s.ptrs 53 := by simp [b,Op.act,wp 53 (by decide)]
  have bm : b.mem=writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => md i)) := wm
  have br (j : ℕ) (hj : j ∉ ({0,1,32,33,57,58,60,61,62,63} : Finset ℕ)) : b.regs j=s.regs j := by
    change w.regs j=s.regs j
    exact (hwr j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj ⊢; tauto)).trans
      (hur j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj ⊢; tauto))
  have bmd : readArray b.mem (b.ptrs 48) D=List.ofFn (fun i => md i) := by
    rw [bm,bp 48 (by decide)]
    simpa only [List.length_ofFn] using readArray_writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => md i))
  have rowsRead (j : Fin n) : readArray b.mem (b.ptrs 52+(j.val : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i) := by
    rw [bm,b52,readArray_write_after _ _ _ _ _ ?_]
    · exact ha j
    · have hbound := encoded_index_interval (s.ptrs 53) (D+2) j.val n (D+1) j.isLt (by omega)
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hbound
      omega
  have rowCell (j : Fin n) (i : ℕ) (hi : i<D+2) :
      b.mem (b.ptrs 52+(j.val : ℤ)*((D : ℤ)+2)+i)=s.mem (s.ptrs 53+(j.val : ℤ)*((D : ℤ)+2)+i) := by
    rw [bm,b52,writeArray_outside _ _ _ _ (Or.inl ?_)]
    have hbound := encoded_index_interval (s.ptrs 53) (D+2) j.val n i j.isLt hi
    simp only [Nat.cast_add,Nat.cast_ofNat] at hbound
    omega
  have bn (j : Fin n) : b.mem (b.ptrs 42+(j.val : ℤ))=noise.1 j := by
    rw [bm,bp 42 (by decide),writeArray_outside _ _ _ _ (Or.inl (by have hj := j.isLt; omega))]
    exact hz j
  have bη : readArray b.mem (b.ptrs 42+n) D=List.ofFn (fun i => noise.2 i) := by
    rw [bm,bp 42 (by decide),readArray_write_after _ _ _ _ _ (by omega)]
    exact hη
  obtain ⟨f,cf,hf,hcf,hfm,hf52,hf42,hfgc,hfec,hfr,hfp⟩ := finite_gradient_correct ω D n a y md noise τ b
    ((bp 15 (by decide)).trans hD) ((bp 16 (by decide)).trans hn) ((br 59 (by decide)).trans hr)
    ((br 50 (by decide)).trans hτ)
    (by rwa [b52,bp 43 (by decide)]) (by rwa [bp 42 (by decide),bp 43 (by decide)])
    (by rw [bp 43 (by decide),bp 48 (by decide)]; omega) rowsRead
    (fun j => (rowCell j D (by omega)).trans (hy j))
    (fun j => by
      have hh := rowCell j (D+1) (by omega)
      simp only [Nat.cast_add,Nat.cast_one,add_assoc] at hh
      simpa only [add_assoc] using hh.trans (by simpa only [add_assoc] using hb j)) bn bη bmd
  have fp (q : ℕ) (hq : q ∉ ({3,4,5,12,24,42,52,54} : Finset ℕ)) : f.ptrs q=s.ptrs q :=
    (hfp q hq).trans (bp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto))
  have fm : f.mem=writeArray (writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => md i)))
      (s.ptrs 43) (List.ofFn (fun i => g i)) := by simpa only [bm,bp 43 (by decide)] using hfm
  have fx : readArray f.mem (f.ptrs 44) D=List.ofFn (fun i => x i) := by
    rw [fm,fp 44 (by decide),readArray_write_before _ _ _ _ _ (by simpa using hgx),
      readArray_write_after _ _ _ _ _ (by omega)]
    exact hx
  have fmd : readArray f.mem (f.ptrs 48) D=List.ofFn (fun i => md i) := by
    rw [fm,fp 48 (by decide),readArray_write_before _ _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simpa only [List.length_ofFn] using readArray_writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => md i))
  have fg : readArray f.mem (f.ptrs 43) D=List.ofFn (fun i => g i) := by
    rw [fm,fp 43 (by decide)]
    simpa only [List.length_ofFn] using readArray_writeArray
      (writeArray s.mem (s.ptrs 48) (List.ofFn (fun i => md i))) (s.ptrs 43) (List.ofFn (fun i => g i))
  have f55 : f.regs 55=1 := (hfr 55 (by decide)).trans ((br 55 (by decide)).trans h1)
  have f62 : f.regs 62= -accelLambda β k := (hfr 62 (by decide)).trans ((hwr 62 (by decide)).trans hu62)
  have f63 : f.regs 63= -β := (hfr 63 (by decide)).trans ((hwr 63 (by decide)).trans hu63)
  obtain ⟨j,cj,hj,hcj,hjm,hjgc,hjec,hjr,hjp⟩ := accelerated_update_correct ω D x md g (accelLambda β k) β f
    ((fp 15 (by decide)).trans hD) f55 f62 f63 fx fmd fg
    (by rwa [fp 43 (by decide),fp 44 (by decide)]) (by rwa [fp 44 (by decide),fp 46 (by decide)])
    (by rwa [fp 46 (by decide),fp 48 (by decide)])
  let t := Op.act ω j (.pinc 21)
  have ht : Eval ω (.atom (.pinc 21)) j t 1 := Eval.atom j _
  have hall : Eval ω acceleratedStepCommand s t (9+14+18*D+1+cf+cj+1) := by
    convert! Eval.seq hu (Eval.seq hw (Eval.seq hbstate (Eval.seq hf (Eval.seq hj ht)))) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,_,hall,by omega,?_,?_,?_,hc.1,hc.2,?_,?_⟩
  · change j.mem=_
    rw [hjm,fm,fp 44 (by decide),fp 46 (by decide)]
  · change j.ptrs 42=s.ptrs 42+n+D
    rw [hjp 42 (by decide),hf42,bp 42 (by decide)]
  · change j.ptrs 21+1=s.ptrs 21+1
    rw [hjp 21 (by decide),fp 21 (by decide)]
  · intro l hl
    exact (hjr l (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hl ⊢; tauto)).trans
      ((hfr l (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hl ⊢; tauto)).trans
        (br l (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hl ⊢; tauto)))
  · intro q hq
    have hqt : t.ptrs q=j.ptrs q := by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
      simp [t,Op.act,hq.2.2.2.2.2.1]
    rw [hqt]
    exact (hjp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)).trans
      (fp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMTrainingInvariant
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry NonconvexAG.StochComposite
noncomputable def regressionPath {D n : ℕ} (τ β : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ)
    (noise : ℕ → RegressionNoise n D) (j : ℕ) : Vec D × Vec D :=
  rsagPath (noisyRegressionOracle ((n : ℝ)⁻¹) τ a y) (fun x g c => unitProjection (x-c • g))
    accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) 0 noise j
structure TrainingInvariant (D n : ℕ) (τ β : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ)
    (noise : ℕ → RegressionNoise n D) (s₀ : Store) (j : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ∉ ({3,4,5,6,12,21,24,42,52,54} : Finset ℕ) → s.ptrs q=s₀.ptrs q
  fixedRegisters : ∀ r, r ∉ ({0,1,2,3,31,32,33,57,58,60,61,62,63} : Finset ℕ) → s.regs r=s₀.regs r
  counter : s.ptrs 21=(j : ℤ)+1
  noiseCursor : s.ptrs 42=s₀.ptrs 42+(j : ℤ)*((n : ℤ)+D)
  xvalue : readArray s.mem (s₀.ptrs 44) D=List.ofFn (fun i => (regressionPath τ β a y noise j).1 i)
  agvalue : readArray s.mem (s₀.ptrs 46) D=List.ofFn (fun i => (regressionPath τ β a y noise j).2 i)
  memoryFrame : ∀ z, z<s₀.ptrs 43 ∨ s₀.ptrs 48+(D : ℤ)≤z → s.mem z=s₀.mem z
lemma training_invariant_step (ω : PolySampIso.Streams) (D n : ℕ) (τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (noise : ℕ → RegressionNoise n D) (s₀ : Store)
    (hD : s₀.ptrs 15=D) (hn : s₀.ptrs 16=n)
    (hτ : s₀.regs 50=τ) (hβ : s₀.regs 51=β) (h1 : s₀.regs 55=1) (h2 : s₀.regs 56=2) (hr : s₀.regs 59=(n : ℝ)⁻¹)
    (hgx : s₀.ptrs 43+(D : ℤ) ≤ s₀.ptrs 44) (hxag : s₀.ptrs 44+(D : ℤ) ≤ s₀.ptrs 46)
    (hagm : s₀.ptrs 46+(D : ℤ) ≤ s₀.ptrs 48)
    (hrows : s₀.ptrs 53+(n : ℤ)*((D : ℤ)+2) ≤ s₀.ptrs 43)
    (hnoise : s₀.ptrs 42+(n : ℤ)*((n : ℤ)+D) ≤ s₀.ptrs 43)
    (ha : ∀ i : Fin n, readArray s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun l => a i l))
    (hy : ∀ i : Fin n, s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+D)=y i)
    (hb : ∀ i : Fin n, s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+D+1)=‖a i‖)
    (hz : ∀ j, j<n → ∀ i : Fin n, s₀.mem (s₀.ptrs 42+(j : ℤ)*((n : ℤ)+D)+i.val)=(noise (j+1)).1 i)
    (hη : ∀ j, j<n → readArray s₀.mem (s₀.ptrs 42+(j : ℤ)*((n : ℤ)+D)+n) D=List.ofFn (fun l => (noise (j+1)).2 l))
    (j : ℕ) (hj : j<n) (s : Store) (hs : TrainingInvariant D n τ β a y noise s₀ j s) :
    ∃ t cost, Eval ω acceleratedStepCommand s t cost ∧ cost ≤ 105+102*D+n*(32+20*D) ∧
      TrainingInvariant D n τ β a y noise s₀ (j+1) t := by
  have hp := hs.fixedPointers
  have hhrow (i : Fin n) (l : ℕ) (hl : l<D+2) :
      s.mem (s.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+l)=s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+l) := by
    rw [hp 53 (by decide)]
    apply hs.memoryFrame
    left
    have hh := encoded_index_interval (s₀.ptrs 53) (D+2) i.val n l i.isLt hl
    simp only [Nat.cast_add,Nat.cast_ofNat] at hh
    omega
  have hdata (i : Fin n) : readArray s.mem (s.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun l => a i l) := by
    rw [hp 53 (by decide)]
    calc
      _ = readArray s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)) D := by
        apply readArray_congr
        intro l hl
        simpa only [hp 53 (by decide)] using hhrow i l (by omega)
      _ = _ := ha i
  have hnoisec : s.ptrs 42+(n : ℤ)+D ≤ s₀.ptrs 43 := by
    rw [hs.noiseCursor]
    have hj' : (j : ℤ)+1 ≤ n := by exact_mod_cast (show j+1≤n by omega)
    have hm := mul_le_mul_of_nonneg_right hj' (show (0 : ℤ)≤(n : ℤ)+D by positivity)
    nlinarith only [hm,hnoise]
  have hzn (i : Fin n) : s.mem (s.ptrs 42+i.val)=(noise (j+1)).1 i := by
    rw [hs.memoryFrame _ (Or.inl (by have hi := i.isLt; omega)),hs.noiseCursor]
    exact hz j hj i
  have hηn : readArray s.mem (s.ptrs 42+n) D=List.ofFn (fun l => (noise (j+1)).2 l) := by
    calc
      _ = readArray s₀.mem (s.ptrs 42+n) D := by
        apply readArray_congr
        intro l hl
        apply hs.memoryFrame
        left
        have hl' : (l : ℤ)<D := by exact_mod_cast hl
        omega
      _ = _ := by rw [hs.noiseCursor]; exact hη j hj
  obtain ⟨t,cost,he,hcost,hm,h42,h21,hgc,hec,hreg,hptr⟩ := accelerated_step_correct ω D n (j+1) a y (noise (j+1))
    (regressionPath τ β a y noise j).1 (regressionPath τ β a y noise j).2 τ β s
    ((hp 15 (by decide)).trans hD) ((hp 16 (by decide)).trans hn) (by simpa using hs.counter)
    ((hs.fixedRegisters 50 (by decide)).trans hτ) ((hs.fixedRegisters 51 (by decide)).trans hβ)
    ((hs.fixedRegisters 55 (by decide)).trans h1) ((hs.fixedRegisters 56 (by decide)).trans h2)
    ((hs.fixedRegisters 59 (by decide)).trans hr)
    (by rw [hp 44 (by decide)]; exact hs.xvalue) (by rw [hp 46 (by decide)]; exact hs.agvalue)
    (by rwa [hp 43 (by decide),hp 44 (by decide)]) (by rwa [hp 44 (by decide),hp 46 (by decide)])
    (by rwa [hp 46 (by decide),hp 48 (by decide)]) (by rwa [hp 53 (by decide),hp 43 (by decide)])
    (by rw [hp 43 (by decide)]; exact hnoisec) hdata
    (fun i => (hhrow i D (by omega)).trans (hy i))
    (fun i => by have hh := hhrow i (D+1) (by omega); simp only [Nat.cast_add,Nat.cast_one,add_assoc] at hh; simpa only [add_assoc] using hh.trans (by simpa only [add_assoc] using hb i))
    hzn hηn
  refine ⟨t,cost,he,hcost,?_⟩
  constructor
  · intro q hq
    exact (hptr q hq).trans (hp q hq)
  · intro r hr
    exact (hreg r hr).trans (hs.fixedRegisters r hr)
  · rw [h21,hs.counter]
    push_cast
    ring
  · rw [h42,hs.noiseCursor]
    push_cast
    ring
  · rw [hm,hp 43 (by decide),hp 44 (by decide),hp 46 (by decide),hp 48 (by decide),
      readArray_write_after _ _ _ _ _ hxag]
    rw [show (regressionPath τ β a y noise (j+1)).1=unitProjection ((regressionPath τ β a y noise j).1-
      accelLambda β (j+1) • noisyRegressionOracle ((n : ℝ)⁻¹) τ a y
        ((1-accelAlpha (j+1)) • (regressionPath τ β a y noise j).2+accelAlpha (j+1) • (regressionPath τ β a y noise j).1) (noise (j+1))) from
      by simp only [regressionPath,rsagPath,sampleAvg_one _ (j+1) (by omega)]]
    simp only [readArray_write_ofFn]
  · rw [hm,hp 43 (by decide),hp 44 (by decide),hp 46 (by decide),hp 48 (by decide)]
    rw [show (regressionPath τ β a y noise (j+1)).2=unitProjection (
      ((1-accelAlpha (j+1)) • (regressionPath τ β a y noise j).2+accelAlpha (j+1) • (regressionPath τ β a y noise j).1)-
      β • noisyRegressionOracle ((n : ℝ)⁻¹) τ a y
        ((1-accelAlpha (j+1)) • (regressionPath τ β a y noise j).2+accelAlpha (j+1) • (regressionPath τ β a y noise j).1) (noise (j+1))) from
      by simp only [regressionPath,rsagPath,sampleAvg_one _ (j+1) (by omega)]]
    simp only [readArray_write_ofFn]
  · intro z hzoutside
    rw [hm,hp 43 (by decide),hp 44 (by decide),hp 46 (by decide),hp 48 (by decide)]
    rw [writeArray_outside _ _ _ z (by simp only [List.length_ofFn]; rcases hzoutside with hz|hz <;> omega),
      writeArray_outside _ _ _ z (by simp only [List.length_ofFn]; rcases hzoutside with hz|hz <;> omega),
      writeArray_outside _ _ _ z (by simp only [List.length_ofFn]; rcases hzoutside with hz|hz <;> omega),
      writeArray_outside _ _ _ z (by simp only [List.length_ofFn]; rcases hzoutside with hz|hz <;> omega)]
    exact hs.memoryFrame z hzoutside
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMTrainingLoop
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
def trainingLoop : Cmd := .loop (.pointer 21 16) acceleratedStepCommand
lemma training_loop_correct (ω : PolySampIso.Streams) (D n : ℕ) (τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (noise : ℕ → RegressionNoise n D) (s₀ s : Store)
    (hD : s₀.ptrs 15=D) (hn : s₀.ptrs 16=n)
    (hτ : s₀.regs 50=τ) (hβ : s₀.regs 51=β) (h1 : s₀.regs 55=1) (h2 : s₀.regs 56=2) (hr : s₀.regs 59=(n : ℝ)⁻¹)
    (hgx : s₀.ptrs 43+(D : ℤ) ≤ s₀.ptrs 44) (hxag : s₀.ptrs 44+(D : ℤ) ≤ s₀.ptrs 46)
    (hagm : s₀.ptrs 46+(D : ℤ) ≤ s₀.ptrs 48)
    (hrows : s₀.ptrs 53+(n : ℤ)*((D : ℤ)+2) ≤ s₀.ptrs 43)
    (hnoise : s₀.ptrs 42+(n : ℤ)*((n : ℤ)+D) ≤ s₀.ptrs 43)
    (ha : ∀ i : Fin n, readArray s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun l => a i l))
    (hy : ∀ i : Fin n, s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+D)=y i)
    (hb : ∀ i : Fin n, s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+D+1)=‖a i‖)
    (hz : ∀ j, j<n → ∀ i : Fin n, s₀.mem (s₀.ptrs 42+(j : ℤ)*((n : ℤ)+D)+i.val)=(noise (j+1)).1 i)
    (hη : ∀ j, j<n → readArray s₀.mem (s₀.ptrs 42+(j : ℤ)*((n : ℤ)+D)+n) D=List.ofFn (fun l => (noise (j+1)).2 l))
    (hs : TrainingInvariant D n τ β a y noise s₀ 0 s) :
    ∃ t cost, Eval ω trainingLoop s t cost ∧ cost ≤ 2+n*(107+102*D+n*(32+20*D)) ∧
      TrainingInvariant D n τ β a y noise s₀ n t := by
  have htrue : ∀ j, j<n → ∀ u, TrainingInvariant D n τ β a y noise s₀ j u → Test.holds u (.pointer 21 16) := by
    intro j hj u hu
    change u.ptrs 21 ≤ u.ptrs 16
    rw [hu.counter,hu.fixedPointers 16 (by decide),hn]
    omega
  have hfalse : ∀ u, TrainingInvariant D n τ β a y noise s₀ n u → ¬Test.holds u (.pointer 21 16) := by
    intro u hu
    change ¬u.ptrs 21 ≤ u.ptrs 16
    rw [hu.counter,hu.fixedPointers 16 (by decide),hn]
    omega
  have hbody : ∀ j, j<n → ∀ u, TrainingInvariant D n τ β a y noise s₀ j u →
      ∃ t cost, cost ≤ 105+102*D+n*(32+20*D) ∧ Eval ω acceleratedStepCommand u t cost ∧
        TrainingInvariant D n τ β a y noise s₀ (j+1) t := by
    intro j hj u hu
    obtain ⟨t,cost,he,hcost,ht⟩ := training_invariant_step ω D n τ β a y noise s₀ hD hn hτ hβ h1 h2 hr
      hgx hxag hagm hrows hnoise ha hy hb hz hη j hj u hu
    exact ⟨t,cost,hcost,he,ht⟩
  obtain ⟨t,cost,hcost,he,ht⟩ := eval_loop_invariant ω (.pointer 21 16) acceleratedStepCommand n
    (105+102*D+n*(32+20*D)) (TrainingInvariant D n τ β a y noise s₀) htrue hfalse hbody s hs
  refine ⟨t,cost,he,?_,ht⟩
  convert! hcost using 1 <;> ring
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMTrainingInit
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
def trainingInitCommand : Cmd := .seq (.block [.literal 32 0,.pcopy 5 44]) (.seq fillCommand
  (.seq (.atom (.pcopy 5 46)) (.seq fillCommand (.atom (.pset 21 1)))))
lemma training_init_correct (ω : PolySampIso.Streams) (D n : ℕ) (τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (noise : ℕ → RegressionNoise n D) (s : Store)
    (hD : s.ptrs 15=D) (hgx : s.ptrs 43+(D : ℤ) ≤ s.ptrs 44)
    (hxag : s.ptrs 44+(D : ℤ) ≤ s.ptrs 46) (hagm : s.ptrs 46+(D : ℤ) ≤ s.ptrs 48) :
    ∃ t, Eval ω trainingInitCommand s t (10+10*D) ∧ TrainingInvariant D n τ β a y noise s 0 t := by
  let u := blockAct ω [.literal 32 0,.pcopy 5 44] s
  have hu : Eval ω (.block [.literal 32 0,.pcopy 5 44]) s u 2 := eval_block ω _ s
  have u5 : u.ptrs 5=s.ptrs 44 := by simp [u,blockAct,Op.act]
  have u32 : u.regs 32=0 := by simp [u,blockAct,Op.act]
  have um : u.mem=s.mem := rfl
  obtain ⟨v,hv,hvm,hv5,hvr,hvgc,hvec,hvp⟩ := fill_command_correct ω D u (by simpa [u,blockAct,Op.act] using hD)
  let w := Op.act ω v (.pcopy 5 46)
  have hw : Eval ω (.atom (.pcopy 5 46)) v w 1 := Eval.atom v _
  have w15 : w.ptrs 15=D := by simp [w,Op.act,hvp 15 (by omega) (by omega),u,blockAct,Op.act,hD]
  have w5 : w.ptrs 5=s.ptrs 46 := by simp [w,Op.act,hvp 46 (by omega) (by omega),u,blockAct,Op.act]
  have w32 : w.regs 32=0 := by change v.regs 32=0; rw [hvr,u32]
  obtain ⟨j,hj,hjm,hj5,hjr,hjgc,hjec,hjp⟩ := fill_command_correct ω D w w15
  let t := Op.act ω j (.pset 21 1)
  have ht : Eval ω (.atom (.pset 21 1)) j t 1 := Eval.atom j _
  have hall : Eval ω trainingInitCommand s t (10+10*D) := by
    convert! Eval.seq hu (Eval.seq hv (Eval.seq hw (Eval.seq hj ht))) using 1 <;> omega
  have tm : t.mem=writeArray (writeArray s.mem (s.ptrs 44) (List.replicate D 0))
      (s.ptrs 46) (List.replicate D 0) := by
    change j.mem=_
    rw [hjm,w5,w32]
    change writeArray v.mem (s.ptrs 46) (List.replicate D 0)=_
    rw [hvm,u5,u32,um]
  refine ⟨t,hall,?_⟩
  constructor
  · intro q hq
    apply hall.pointer_preserved
    simp [trainingInitCommand,fillCommand,fillLoop,fillStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
  · intro r hr
    apply hall.register_preserved
    simp [trainingInitCommand,fillCommand,fillLoop,fillStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · simp [t,Op.act]
  · have hp : t.ptrs 42=s.ptrs 42 := hall.pointer_preserved (by decide)
    simpa using hp
  · rw [tm,readArray_write_after _ _ _ _ _ hxag]
    have hz : List.replicate D (0 : ℝ)=List.ofFn (fun i : Fin D => (0 : Vec D) i) := by simp [List.ofFn_const]
    rw [hz,readArray_write_ofFn]
    rfl
  · rw [tm]
    have hz : List.replicate D (0 : ℝ)=List.ofFn (fun i : Fin D => (0 : Vec D) i) := by simp [List.ofFn_const]
    rw [hz,readArray_write_ofFn]
    rfl
  · intro z hz
    rw [tm,writeArray_outside _ _ _ z (by simp only [List.length_replicate]; rcases hz with hz|hz <;> omega),
      writeArray_outside _ _ _ z (by simp only [List.length_replicate]; rcases hz with hz|hz <;> omega)]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMTraining
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
def trainingCommand : Cmd := .seq trainingInitCommand trainingLoop
lemma training_command_correct (ω : PolySampIso.Streams) (D n : ℕ) (τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (noise : ℕ → RegressionNoise n D) (s₀ : Store)
    (hD : s₀.ptrs 15=D) (hn : s₀.ptrs 16=n)
    (hτ : s₀.regs 50=τ) (hβ : s₀.regs 51=β) (h1 : s₀.regs 55=1) (h2 : s₀.regs 56=2) (hr : s₀.regs 59=(n : ℝ)⁻¹)
    (hgx : s₀.ptrs 43+(D : ℤ) ≤ s₀.ptrs 44) (hxag : s₀.ptrs 44+(D : ℤ) ≤ s₀.ptrs 46)
    (hagm : s₀.ptrs 46+(D : ℤ) ≤ s₀.ptrs 48)
    (hrows : s₀.ptrs 53+(n : ℤ)*((D : ℤ)+2) ≤ s₀.ptrs 43)
    (hnoise : s₀.ptrs 42+(n : ℤ)*((n : ℤ)+D) ≤ s₀.ptrs 43)
    (ha : ∀ i : Fin n, readArray s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun l => a i l))
    (hy : ∀ i : Fin n, s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+D)=y i)
    (hb : ∀ i : Fin n, s₀.mem (s₀.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+D+1)=‖a i‖)
    (hz : ∀ j, j<n → ∀ i : Fin n, s₀.mem (s₀.ptrs 42+(j : ℤ)*((n : ℤ)+D)+i.val)=(noise (j+1)).1 i)
    (hη : ∀ j, j<n → readArray s₀.mem (s₀.ptrs 42+(j : ℤ)*((n : ℤ)+D)+n) D=List.ofFn (fun l => (noise (j+1)).2 l))
    :
    ∃ t cost, Eval ω trainingCommand s₀ t cost ∧ cost ≤ 12+10*D+n*(107+102*D+n*(32+20*D)) ∧
      TrainingInvariant D n τ β a y noise s₀ n t := by
  obtain ⟨u,hu,hinit⟩ := training_init_correct ω D n τ β a y noise s₀ hD hgx hxag hagm
  obtain ⟨t,cost,he,hcost,ht⟩ := training_loop_correct ω D n τ β a y noise s₀ u hD hn hτ hβ h1 h2 hr
    hgx hxag hagm hrows hnoise ha hy hb hz hη hinit
  refine ⟨t,10+10*D+cost,Eval.seq hu he,by omega,ht⟩
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMRecordCoefficient
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def recordCoefficientCommand : Cmd := .seq (vectorMove 46 50) (advanceCommand 50 15)
lemma record_coefficient_correct (ω : PolySampIso.Streams) (D : ℕ) (v : Vec D) (s : Store)
    (hD : s.ptrs 15=D) (hv : readArray s.mem (s.ptrs 46) D=List.ofFn (fun i => v i))
    (hdisj : s.ptrs 46+(D : ℤ) ≤ s.ptrs 50) :
    ∃ t, Eval ω recordCoefficientCommand s t (8+11*D) ∧
      t.mem=writeArray s.mem (s.ptrs 50) (List.ofFn (fun i => v i)) ∧
      t.ptrs 50=s.ptrs 50+D ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 0 → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,5,12,50} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨u,hu,hum,hugc,huec,hur,hup⟩ := vector_move_correct ω D 46 50 v s (by omega) hD hv (Or.inl hdisj)
  obtain ⟨t,ht,ht50,htm,htr,htgc,htec,htp⟩ := advance_command_correct ω 50 15 D
    (by omega) (by omega) (by omega) u ((hup 15 (by decide)).trans hD)
  have hall : Eval ω recordCoefficientCommand s t (8+11*D) := by convert! Eval.seq hu ht using 1 <;> omega
  refine ⟨t,hall,htm.trans hum,?_,htgc.trans hugc,htec.trans huec,?_,?_⟩
  · rw [ht50,hup 50 (by decide)]
  · intro r hr
    rw [htr]
    exact hur r hr
  · intro q hq
    exact (htp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq; tauto)
      (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq; tauto)).trans
      (hup q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMBlockCursors
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def skipNoiseRecordCommand : Cmd := .seq (advanceCommand 42 16) (advanceCommand 42 15)
lemma skip_noise_record_correct (ω : PolySampIso.Streams) (n D : ℕ) (s : Store)
    (hn : s.ptrs 16=n) (hD : s.ptrs 15=D) :
    ∃ t, Eval ω skipNoiseRecordCommand s t (6+4*n+4*D) ∧
      t.ptrs 42=s.ptrs 42+n+D ∧ t.mem=s.mem ∧ t.regs=s.regs ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ q, q ≠ 42 → q ≠ 12 → t.ptrs q=s.ptrs q) := by
  obtain ⟨u,hu,hu42,hum,hur,hugc,huec,hup⟩ := advance_command_correct ω 42 16 n (by omega) (by omega) (by omega) s hn
  obtain ⟨t,ht,ht42,htm,htr,htgc,htec,htp⟩ := advance_command_correct ω 42 15 D (by omega) (by omega) (by omega) u
    ((hup 15 (by omega) (by omega)).trans hD)
  have hall : Eval ω skipNoiseRecordCommand s t (6+4*n+4*D) := by convert! Eval.seq hu ht using 1 <;> omega
  refine ⟨t,hall,?_,htm.trans hum,htr.trans hur,htgc.trans hugc,htec.trans huec,?_⟩
  · rw [ht42,hu42]
  · intro q hq hq12
    exact (htp q hq hq12).trans (hup q hq hq12)
def advanceBlockCommand : Cmd := .seq (advanceCommand 53 17) (.atom (.pinc 22))
lemma advance_block_correct (ω : PolySampIso.Streams) (stride : ℕ) (s : Store) (hs : s.ptrs 17=stride) :
    ∃ t, Eval ω advanceBlockCommand s t (4+4*stride) ∧
      t.ptrs 53=s.ptrs 53+stride ∧ t.ptrs 22=s.ptrs 22+1 ∧ t.mem=s.mem ∧ t.regs=s.regs ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧ (∀ q, q ∉ ({12,22,53} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  obtain ⟨u,hu,hu53,hum,hur,hugc,huec,hup⟩ := advance_command_correct ω 53 17 stride (by omega) (by omega) (by omega) s hs
  let t := Op.act ω u (.pinc 22)
  have ht : Eval ω (.atom (.pinc 22)) u t 1 := Eval.atom u _
  have hall : Eval ω advanceBlockCommand s t (4+4*stride) := by convert! Eval.seq hu ht using 1 <;> omega
  refine ⟨t,hall,?_,?_,hum,hur,hugc,huec,?_⟩
  · exact hu53
  · change u.ptrs 22+1=s.ptrs 22+1
    rw [hup 22 (by omega) (by omega)]
  · intro q hq
    apply hall.pointer_preserved
    simp [advanceBlockCommand,advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMTrainRecord
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
def trainRecordCommand : Cmd := .seq skipNoiseRecordCommand (.seq trainingCommand
  (.seq recordCoefficientCommand advanceBlockCommand))
lemma train_record_correct (ω : PolySampIso.Streams) (D n : ℕ) (τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (noise : Fin (n+1) → RegressionNoise n D) (s : Store)
    (hD : s.ptrs 15=D) (hn : s.ptrs 16=n) (hstride : s.ptrs 17=n*(D+2))
    (hτ : s.regs 50=τ) (hβ : s.regs 51=β) (h1 : s.regs 55=1) (h2 : s.regs 56=2) (hr : s.regs 59=(n : ℝ)⁻¹)
    (hgx : s.ptrs 43+(D : ℤ) ≤ s.ptrs 44) (hxag : s.ptrs 44+(D : ℤ) ≤ s.ptrs 46)
    (hagm : s.ptrs 46+(D : ℤ) ≤ s.ptrs 48) (hbank : s.ptrs 48+(D : ℤ) ≤ s.ptrs 50)
    (hrows : s.ptrs 53+(n : ℤ)*((D : ℤ)+2) ≤ s.ptrs 43)
    (hnoise : s.ptrs 42+((n : ℤ)+1)*((n : ℤ)+D) ≤ s.ptrs 43)
    (ha : ∀ i : Fin n, readArray s.mem (s.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun l => a i l))
    (hy : ∀ i : Fin n, s.mem (s.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+D)=y i)
    (hb : ∀ i : Fin n, s.mem (s.ptrs 53+(i.val : ℤ)*((D : ℤ)+2)+D+1)=‖a i‖)
    (hz : ∀ j : Fin (n+1), ∀ i : Fin n,
      s.mem (s.ptrs 42+(j.val : ℤ)*((n : ℤ)+D)+i.val)=(noise j).1 i)
    (hη : ∀ j : Fin (n+1), readArray s.mem (s.ptrs 42+(j.val : ℤ)*((n : ℤ)+D)+n) D=
      List.ofFn (fun l => (noise j).2 l)) :
    let out := regressionVectorOutput ((n : ℝ)⁻¹) τ β a y noise
    ∃ t cost, Eval ω trainRecordCommand s t cost ∧
      cost ≤ 30+25*D+4*n+4*(n*(D+2))+n*(107+102*D+n*(32+20*D)) ∧
      readArray t.mem (s.ptrs 50) D=List.ofFn (fun i => out i) ∧
      t.ptrs 42=s.ptrs 42+((n : ℤ)+1)*((n : ℤ)+D) ∧
      t.ptrs 50=s.ptrs 50+D ∧ t.ptrs 53=s.ptrs 53+(n : ℤ)*((D : ℤ)+2) ∧ t.ptrs 22=s.ptrs 22+1 ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ z, (z<s.ptrs 43 ∨ s.ptrs 48+(D : ℤ)≤z) →
        (z<s.ptrs 50 ∨ s.ptrs 50+(D : ℤ)≤z) → t.mem z=s.mem z) ∧
      (∀ r, r ∉ ({0,1,2,3,31,32,33,57,58,60,61,62,63} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,5,6,12,21,22,24,42,50,52,53,54} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  dsimp only
  let out := regressionVectorOutput ((n : ℝ)⁻¹) τ β a y noise
  let seq := finiteNoiseSequence (0,0) noise
  obtain ⟨u,hu,hu42,hum,hur,hugc,huec,hup⟩ := skip_noise_record_correct ω n D s hn hD
  have up (q : ℕ) (hq42 : q ≠ 42) (hq12 : q ≠ 12) : u.ptrs q=s.ptrs q := hup q hq42 hq12
  have unoise : u.ptrs 42+(n : ℤ)*((n : ℤ)+D)≤u.ptrs 43 := by
    rw [hu42,up 43 (by omega) (by omega)]
    nlinarith only [hnoise]
  have uz (j : ℕ) (hj : j<n) (i : Fin n) :
      u.mem (u.ptrs 42+(j : ℤ)*((n : ℤ)+D)+i.val)=(seq (j+1)).1 i := by
    dsimp only [seq]
    rw [hum,hu42,finiteNoiseSequence_apply (0,0) noise (j+1) (by omega)]
    convert! hz ⟨j+1,by omega⟩ i using 1 <;> push_cast <;> ring
  have uη (j : ℕ) (hj : j<n) : readArray u.mem (u.ptrs 42+(j : ℤ)*((n : ℤ)+D)+n) D=
      List.ofFn (fun l => (seq (j+1)).2 l) := by
    dsimp only [seq]
    rw [hum,hu42,finiteNoiseSequence_apply (0,0) noise (j+1) (by omega)]
    convert! hη ⟨j+1,by omega⟩ using 1 <;> push_cast <;> ring
  obtain ⟨v,cv,hv,hcv,hvInv⟩ := training_command_correct ω D n τ β a y seq u
    ((up 15 (by omega) (by omega)).trans hD) ((up 16 (by omega) (by omega)).trans hn)
    (by rw [hur]; exact hτ) (by rw [hur]; exact hβ) (by rw [hur]; exact h1) (by rw [hur]; exact h2) (by rw [hur]; exact hr)
    (by rwa [up 43 (by omega) (by omega),up 44 (by omega) (by omega)])
    (by rwa [up 44 (by omega) (by omega),up 46 (by omega) (by omega)])
    (by rwa [up 46 (by omega) (by omega),up 48 (by omega) (by omega)])
    (by rwa [up 53 (by omega) (by omega),up 43 (by omega) (by omega)]) unoise
    (fun i => by rw [hum,up 53 (by omega) (by omega)]; exact ha i)
    (fun i => by rw [hum,up 53 (by omega) (by omega)]; exact hy i)
    (fun i => by rw [hum,up 53 (by omega) (by omega)]; exact hb i) uz uη
  have vp (q : ℕ) (hq : q ∉ ({3,4,5,6,12,21,24,42,52,54} : Finset ℕ)) : v.ptrs q=s.ptrs q :=
    (hvInv.fixedPointers q hq).trans (up q
      (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq; tauto)
      (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq; tauto))
  have vag : readArray v.mem (v.ptrs 46) D=List.ofFn (fun i => out i) := by
    rw [hvInv.fixedPointers 46 (by decide)]
    exact hvInv.agvalue
  obtain ⟨w,hw,hwm,hw50,hwgc,hwec,hwr,hwp⟩ := record_coefficient_correct ω D out v
    ((vp 15 (by decide)).trans hD) vag (by rw [vp 46 (by decide),vp 50 (by decide)]; omega)
  obtain ⟨t,ht,ht53,ht22,htm,htr,htgc,htec,htp⟩ := advance_block_correct ω (n*(D+2)) w
    ((hwp 17 (by decide)).trans ((vp 17 (by decide)).trans hstride))
  have hall : Eval ω trainRecordCommand s t ((6+4*n+4*D)+cv+(8+11*D)+(4+4*(n*(D+2)))) := by
    convert! Eval.seq hu (Eval.seq hv (Eval.seq hw ht)) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,_,hall,by omega,?_,?_,?_,?_,?_,hc.1,hc.2,?_,?_,?_⟩
  · rw [htm,hwm,vp 50 (by decide),readArray_write_ofFn]
  · rw [htp 42 (by decide),hwp 42 (by decide),hvInv.noiseCursor,hu42]
    ring
  · rw [htp 50 (by decide),hw50,vp 50 (by decide)]
  · rw [ht53,hwp 53 (by decide),vp 53 (by decide)]
    push_cast
    rfl
  · rw [ht22,hwp 22 (by decide),vp 22 (by decide)]
  · intro z hzWork hzBank
    rw [htm,hwm,writeArray_outside _ _ _ z (by simp only [List.length_ofFn]; simpa only [vp 50 (by decide)] using hzBank)]
    rw [hvInv.memoryFrame z (by simpa only [up 43 (by omega) (by omega),up 48 (by omega) (by omega)] using hzWork),hum]
  · intro r hr
    rw [htr,hwr r (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr; tauto)]
    exact (hvInv.fixedRegisters r hr).trans (congrFun hur r)
  · intro q hq
    exact (htp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)).trans
      ((hwp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)).trans
        (vp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)))
end PrivateAgnosticHalfspace.Gaussian.RAM
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

end PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure
namespace PrivateAgnosticHalfspace.Gaussian.AlgorithmInfrastructure
noncomputable def selectionLaw (d p k M m : ℕ) (ε : ℝ)
    (v : Fin k → UnitBall d p) (V : Fin m → Example d) : Measure (Output d p M) :=
  let w := fun jl : Fin k × Fin M =>
    Real.exp (-ε * m * empiricalError V (candidate d p M (v jl.1).val jl.2) / 2)
  ∑ jl : Fin k × Fin M,
    ENNReal.ofReal (w jl / ∑ il : Fin k × Fin M, w il) • Measure.dirac (v jl.1, jl.2)

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
-- Solutions.RAMGaussianLaw
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
local instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
lemma normal_coordinates_preserving {ι : Type*} [Fintype ι] (f : ι → ℕ) (hf : Function.Injective f) :
    MeasurePreserving (fun ω : PolySampIso.Streams => fun i => ω.1 (f i)) PolySampIso.tape
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hp : MeasurePreserving (fun ω : ℕ → ℝ => fun i => ω (f i))
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj hf,Measure.infinitePi_eq_pi]
  exact hp.comp measurePreserving_fst
noncomputable def normalRecord (n D : ℕ) (z : Fin (n+D) → ℝ) : RegressionNoise n D :=
  ((fun i => z (Fin.castAdd D i)),WithLp.toLp 2 (fun i => z (Fin.natAdd n i)))
lemma normalRecord_preserving (n D : ℕ) : MeasurePreserving (normalRecord n D)
    (Measure.pi (fun _ : Fin (n+D) => gaussianReal 0 1)) (regressionNoiseLaw n D) := by
  have h1 := measurePreserving_piCongrLeft (fun _ : Fin n ⊕ Fin D => gaussianReal 0 1)
    (finSumFinEquiv : Fin n ⊕ Fin D ≃ Fin (n+D)).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin D => gaussianReal 0 1)
  have hvec : MeasurePreserving (WithLp.toLp 2 : (Fin D → ℝ) → Vec D)
      (Measure.pi (fun _ : Fin D => gaussianReal 0 1)) (gaussian D) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have h3 := (MeasurePreserving.id (Measure.pi (fun _ : Fin n => gaussianReal 0 1))).prod hvec
  convert! h3.comp (h2.comp h1) using 1
  funext z
  apply Prod.ext
  · funext i
    simp [normalRecord,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi,Equiv.sumPiEquivProdPi,Function.comp_def,Prod.map_apply]
  · apply PiLp.ext
    intro i
    simp [normalRecord,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi,Equiv.sumPiEquivProdPi,Function.comp_def,Prod.map_apply]
noncomputable def normalNoiseDraw (n D offset : ℕ) (ω : PolySampIso.Streams) : Fin (n+1) → RegressionNoise n D :=
  fun j => normalRecord n D (fun i => ω.1 (offset+j.val*(n+D)+i.val))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMGaussianBlocks
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
noncomputable def normalBlockDraw (k n D offset : ℕ) (ω : PolySampIso.Streams) :
    Fin k → Fin (n+1) → RegressionNoise n D :=
  fun b => normalNoiseDraw n D (offset+b.val*(n+1)*(n+D)) ω
lemma normalBlockDraw_preserving (k n D offset : ℕ) : MeasurePreserving (normalBlockDraw k n D offset)
    PolySampIso.tape (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D))) := by
  let f : (Fin k × Fin (n+1)) × Fin (n+D) → ℕ := fun q =>
    offset+q.1.1.val*(n+1)*(n+D)+q.1.2.val*(n+D)+q.2.val
  have hf : Function.Injective f := by
    intro a b hab
    let e₁ : Fin k × Fin (n+1) ≃ Fin (k*(n+1)) := finProdFinEquiv
    let e₂ : Fin (k*(n+1)) × Fin (n+D) ≃ Fin (k*(n+1)*(n+D)) := finProdFinEquiv
    have he (q : (Fin k × Fin (n+1)) × Fin (n+D)) :
        (e₂ (e₁ q.1,q.2)).val=q.1.1.val*(n+1)*(n+D)+q.1.2.val*(n+D)+q.2.val := by
      simp [e₁,e₂,finProdFinEquiv]
      ring
    have hval : (e₂ (e₁ a.1,a.2)).val=(e₂ (e₁ b.1,b.2)).val := by rw [he,he]; dsimp only [f] at hab; omega
    have h := e₂.injective (Fin.ext hval)
    have hfirst := e₁.injective (congrArg Prod.fst h)
    apply Prod.ext
    · exact hfirst
    · exact congrArg (fun q : Fin (k*(n+1)) × Fin (n+D) => q.2) h
  have h1 := normal_coordinates_preserving f hf
  have h2 := finite_curry_preserving (ι := Fin k × Fin (n+1)) (κ := Fin (n+D)) (gaussianReal 0 1)
  have h3 := measurePreserving_pi (fun _ : Fin k × Fin (n+1) => Measure.pi (fun _ : Fin (n+D) => gaussianReal 0 1))
    (fun _ : Fin k × Fin (n+1) => regressionNoiseLaw n D) (fun _ => normalRecord_preserving n D)
  have h4 := finite_curry_preserving (ι := Fin k) (κ := Fin (n+1)) (regressionNoiseLaw n D)
  convert! h4.comp (h3.comp (h2.comp h1)) using 1
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMEncodedCoordinates
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma encoded_row_coordinates (d p : ℕ) (x : Vec d) (y : Bool) (mem : ℤ → ℝ) (base : ℤ)
    (hrow : readArray mem base (featureDimension d p+2)=encodedRow d p x y) :
    readArray mem base (featureDimension d p)=List.ofFn (fun i => (coefficientIsometry d p (clipped d p x)) i) ∧
      mem (base+featureDimension d p)=label y ∧
      mem (base+featureDimension d p+1)=‖coefficientIsometry d p (clipped d p x)‖ := by
  have hlen : (encodedRow d p x y).length=featureDimension d p+2 := by simp [encodedRow]
  have hcell := (readArray_eq_iff mem base (encodedRow d p x y)).mp (by simpa only [hlen] using hrow)
  refine ⟨?_,?_,?_⟩
  · apply List.ext_getElem
    · simp [readArray]
    · intro i hi hj
      have hi' : i<featureDimension d p := by simpa [readArray] using hi
      have hh := hcell i (by rw [hlen]; omega)
      simpa [readArray,encodedRow,hi'] using hh
  · have hh := hcell (featureDimension d p) (by rw [hlen]; omega)
    simpa [encodedRow] using hh
  · have hh := hcell (featureDimension d p+1) (by rw [hlen]; omega)
    simpa [encodedRow,Nat.cast_add,add_assoc,(coefficientIsometry d p).norm_map] using hh
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMTrainingBlocks
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry AlgorithmInfrastructure
noncomputable def trainedVectors (d p k n m : ℕ) (ε δ : ℝ) (S : Fin (k*n+m) → Example d)
    (ω : PolySampIso.Streams) (b : Fin k) : Vec (featureDimension d p) :=
  regressionVectorOutput ((n : ℝ)⁻¹) (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ)
    (coefficientFeatures d p (trainingBlocks d k n m S b)) (coefficientLabels (trainingBlocks d k n m S b))
    (normalBlockDraw k n (featureDimension d p) 0 ω b)
lemma trainedVectors_eq_optimizerDraw (d p k n m : ℕ) (ε δ : ℝ) (S : Fin (k*n+m) → Example d)
    (ω : PolySampIso.Streams) (b : Fin k) :
    trainedVectors d p k n m ε δ S ω b=coefficientIsometry d p
      (optimizerDraw d p n ε δ (trainingBlocks d k n m S b) (normalBlockDraw k n (featureDimension d p) 0 ω b)).val := by
  simp only [optimizerDraw,LinearIsometryEquiv.apply_symm_apply]
  rfl
structure BlocksInvariant (d p k M n m : ℕ) (ε δ : ℝ) (S : Fin (k*n+m) → Example d)
    (ω : PolySampIso.Streams) (s₀ : Store) (r : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ∉ ({3,4,5,6,12,21,22,24,42,50,52,53,54} : Finset ℕ) → s.ptrs q=s₀.ptrs q
  fixedRegisters : ∀ a, a ∉ ({0,1,2,3,31,32,33,57,58,60,61,62,63} : Finset ℕ) → s.regs a=s₀.regs a
  counter : s.ptrs 22=(r : ℤ)+1
  blockCursor : s.ptrs 53=s₀.ptrs 53+(r : ℤ)*(n : ℤ)*((featureDimension d p : ℤ)+2)
  noiseCursor : s.ptrs 42=s₀.ptrs 42+(r : ℤ)*((n : ℤ)+1)*((n : ℤ)+featureDimension d p)
  bankCursor : s.ptrs 50=s₀.ptrs 50+(r : ℤ)*featureDimension d p
  written : ∀ b : Fin k, b.val<r → readArray s.mem (s₀.ptrs 50+(b.val : ℤ)*featureDimension d p)
    (featureDimension d p)=List.ofFn (fun i => trainedVectors d p k n m ε δ S ω b i)
  memoryFrame : ∀ z, (z<s₀.ptrs 43 ∨ s₀.ptrs 48+(featureDimension d p : ℤ)≤z) →
    (z<s₀.ptrs 50 ∨ s₀.ptrs 50+(r : ℤ)*featureDimension d p≤z) → s.mem z=s₀.mem z
lemma BlocksInvariant.initial (d p k M n m : ℕ) (ε δ : ℝ) (S : Fin (k*n+m) → Example d)
    (ω : PolySampIso.Streams) (s : Store) (hc : s.ptrs 22=1) :
    BlocksInvariant d p k M n m ε δ S ω s 0 s := by
  constructor <;> simp_all
lemma BlocksInvariant.memory_before_gradient {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {s₀ s : Store} {r : ℕ}
    (hready : ReadyHeap d p k M n m ε δ S ω s₀) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ r s)
    (z : ℤ) (hz : z<gradientAddress d p k n m) : s.mem z=s₀.mem z := by
  apply hs.memoryFrame z (Or.inl (by rwa [hready.gradient]))
  left
  rw [hready.bankCursor]
  omega
lemma noise_flat_index_bound (k n D r j i : ℕ) (hr : r<k) (hj : j<n+1) (hi : i<n+D) :
    r*(n+1)*(n+D)+j*(n+D)+i<noiseCount k n D := by
  have hm := Nat.mul_le_mul_right (n+1) (show r+1≤k by omega)
  have hb : r*(n+1)+j+1≤k*(n+1) := by nlinarith only [hm,hj]
  have hl := Nat.mul_le_mul_right (n+D) hb
  dsimp only [noiseCount]
  nlinarith only [hl,hi]
lemma BlocksInvariant.noise_cell {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {s₀ s : Store} {r : ℕ}
    (hready : ReadyHeap d p k M n m ε δ S ω s₀) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ r s)
    (hr : r<k) (j i : ℕ) (hj : j<n+1) (hi : i<n+featureDimension d p) :
    s.mem (s.ptrs 42+(j : ℤ)*((n : ℤ)+featureDimension d p)+i)=
      ω.1 (r*(n+1)*(n+featureDimension d p)+j*(n+featureDimension d p)+i) := by
  let q := r*(n+1)*(n+featureDimension d p)+j*(n+featureDimension d p)+i
  have hq : q<noiseCount k n (featureDimension d p) := noise_flat_index_bound k n (featureDimension d p) r j i hr hj hi
  have haddr : s.ptrs 42+(j : ℤ)*((n : ℤ)+featureDimension d p)+i=noiseAddress d p (k*n+m)+(q : ℤ) := by
    rw [hs.noiseCursor,hready.noiseCursor]
    dsimp only [q]
    push_cast
    ring
  have hbefore : noiseAddress d p (k*n+m)+(q : ℤ)<gradientAddress d p k n m := by
    dsimp only [gradientAddress]
    have hqi : (q : ℤ)<(noiseCount k n (featureDimension d p) : ℤ) := by exact_mod_cast hq
    omega
  rw [haddr,hs.memory_before_gradient hready _ hbefore]
  exact hready.noise ⟨q,hq⟩
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMBlockData
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry AlgorithmInfrastructure
lemma BlocksInvariant.encoded_row {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {s₀ s : Store} {r : ℕ}
    (hready : ReadyHeap d p k M n m ε δ S ω s₀) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ r s)
    (hr : r<k) (i : Fin n) :
    readArray s.mem (s.ptrs 53+(i.val : ℤ)*((featureDimension d p : ℤ)+2)) (featureDimension d p+2)=
      encodedRow d p (trainingBlocks d k n m S ⟨r,hr⟩ i).1 (trainingBlocks d k n m S ⟨r,hr⟩ i).2 := by
  let idx : Fin (k*n+m) := ⟨r*n+i.val,by
    have hm := Nat.mul_le_mul_right n (show r+1≤k by omega)
    have hi := i.isLt
    nlinarith⟩
  have addr : s.ptrs 53+(i.val : ℤ)*((featureDimension d p : ℤ)+2)=
      matrixAddress d (k*n+m)+(idx.val : ℤ)*((featureDimension d p : ℤ)+2) := by
    rw [hs.blockCursor,hready.blockBase]
    dsimp only [idx]
    push_cast
    ring
  rw [addr]
  have hmem : readArray s.mem (matrixAddress d (k*n+m)+(idx.val : ℤ)*((featureDimension d p : ℤ)+2))
      (featureDimension d p+2)=readArray s₀.mem (matrixAddress d (k*n+m)+(idx.val : ℤ)*((featureDimension d p : ℤ)+2))
      (featureDimension d p+2) := by
    apply readArray_congr
    intro l hl
    apply hs.memory_before_gradient hready
    have hbound := encoded_index_interval (matrixAddress d (k*n+m)) (featureDimension d p+2) idx.val (k*n+m) l idx.isLt hl
    simp only [Nat.cast_add,Nat.cast_ofNat] at hbound
    dsimp only [gradientAddress,noiseAddress]
    have hpos : 0≤(noiseCount k n (featureDimension d p) : ℤ) := by positivity
    simp only [noiseCount,Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hbound hpos ⊢
    omega
  rw [hmem,hready.rows idx]
  rfl
lemma BlocksInvariant.training_data {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {s₀ s : Store} {r : ℕ}
    (hready : ReadyHeap d p k M n m ε δ S ω s₀) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ r s)
    (hr : r<k) :
    let a := coefficientFeatures d p (trainingBlocks d k n m S ⟨r,hr⟩)
    let y := coefficientLabels (trainingBlocks d k n m S ⟨r,hr⟩)
    (∀ i : Fin n, readArray s.mem (s.ptrs 53+(i.val : ℤ)*((featureDimension d p : ℤ)+2))
      (featureDimension d p)=List.ofFn (fun l => a i l)) ∧
    (∀ i : Fin n, s.mem (s.ptrs 53+(i.val : ℤ)*((featureDimension d p : ℤ)+2)+featureDimension d p)=y i) ∧
    (∀ i : Fin n, s.mem (s.ptrs 53+(i.val : ℤ)*((featureDimension d p : ℤ)+2)+featureDimension d p+1)=‖a i‖) := by
  dsimp only
  have hcells (i : Fin n) := encoded_row_coordinates d p (trainingBlocks d k n m S ⟨r,hr⟩ i).1
    (trainingBlocks d k n m S ⟨r,hr⟩ i).2 s.mem _ (hs.encoded_row hready hr i)
  exact ⟨fun i => (hcells i).1,fun i => (hcells i).2.1,fun i => (hcells i).2.2⟩
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMBlockNoise
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma BlocksInvariant.noise_data {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {s₀ s : Store} {r : ℕ}
    (hready : ReadyHeap d p k M n m ε δ S ω s₀) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ r s)
    (hr : r < k) :
    (∀ j : Fin (n+1), ∀ i : Fin n,
      s.mem (s.ptrs 42+(j.val : ℤ)*((n : ℤ)+featureDimension d p)+i.val)=
        (normalBlockDraw k n (featureDimension d p) 0 ω ⟨r,hr⟩ j).1 i) ∧
    (∀ j : Fin (n+1), readArray s.mem (s.ptrs 42+(j.val : ℤ)*((n : ℤ)+featureDimension d p)+n)
      (featureDimension d p)=List.ofFn (fun l => (normalBlockDraw k n (featureDimension d p) 0 ω ⟨r,hr⟩ j).2 l)) := by
  constructor
  · intro j i
    have hh := hs.noise_cell hready hr j.val i.val j.isLt (by have hi := i.isLt; omega)
    simpa [normalBlockDraw,normalNoiseDraw,normalRecord] using hh
  · intro j
    apply List.ext_getElem
    · simp [readArray]
    · intro l hl hl'
      have hlD : l < featureDimension d p := by simpa [readArray] using hl
      have hh := hs.noise_cell hready hr j.val (n+l) j.isLt (by omega)
      simpa [readArray,normalBlockDraw,normalNoiseDraw,normalRecord,Nat.cast_add,add_assoc] using hh
lemma BlocksInvariant.noise_bound {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {s₀ s : Store} {r : ℕ}
    (hready : ReadyHeap d p k M n m ε δ S ω s₀) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ r s)
    (hr : r < k) :
    s.ptrs 42+((n : ℤ)+1)*((n : ℤ)+featureDimension d p)  ≤  s.ptrs 43 := by
  rw [hs.noiseCursor,hready.noiseCursor,hs.fixedPointers 43 (by decide),hready.gradient]
  dsimp only [gradientAddress,noiseCount]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hr' : (r : ℤ)+1  ≤  k := by exact_mod_cast (show r+1 ≤ k by omega)
  have hm := mul_le_mul_of_nonneg_right hr' (show (0 : ℤ) ≤ ((n : ℤ)+1)*((n : ℤ)+featureDimension d p) by positivity)
  nlinarith only [hm]
lemma BlocksInvariant.rows_bound {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {s₀ s : Store} {r : ℕ}
    (hready : ReadyHeap d p k M n m ε δ S ω s₀) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ r s)
    (hr : r < k) :
    s.ptrs 53+(n : ℤ)*((featureDimension d p : ℤ)+2)  ≤  s.ptrs 43 := by
  rw [hs.blockCursor,hready.blockBase,hs.fixedPointers 43 (by decide),hready.gradient]
  dsimp only [gradientAddress,noiseAddress]
  have hm := mul_le_mul_of_nonneg_right
    (show ((r : ℤ)+1)*(n : ℤ) ≤ (k*n+m : ℕ) by
      have hr' : (r : ℤ)+1 ≤ k := by exact_mod_cast (show r+1 ≤ k by omega)
      have h := mul_le_mul_of_nonneg_right hr' (show (0 : ℤ) ≤ n by positivity)
      push_cast
      have hm0 : (0 : ℤ) ≤ m := by positivity
      nlinarith only [h,hm0])
    (show (0 : ℤ) ≤ (featureDimension d p : ℤ)+2 by positivity)
  have hT : 0 ≤ (noiseCount k n (featureDimension d p) : ℤ) := by positivity
  nlinarith only [hm,hT]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMBlocksStep
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry AlgorithmInfrastructure
lemma blocks_invariant_step (ω : PolySampIso.Streams) (d p k M n m : ℕ) (ε δ : ℝ)
    (S : Fin (k*n+m) → Example d) (s₀ : Store) (hready : ReadyHeap d p k M n m ε δ S ω s₀)
    (r : ℕ) (hr : r < k) (s : Store) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ r s) :
    ∃ t cost, Eval ω trainRecordCommand s t cost ∧
      cost ≤ 30+25*featureDimension d p+4*n+4*(n*(featureDimension d p+2))+
        n*(107+102*featureDimension d p+n*(32+20*featureDimension d p)) ∧
      BlocksInvariant d p k M n m ε δ S ω s₀ (r+1) t := by
  let b : Fin k := ⟨r,hr⟩
  have hp := hs.fixedPointers
  have hreg := hs.fixedRegisters
  rcases hready.parameters with ⟨hτ,hβ,hN,hε,hδ,h1,h2,hinv⟩
  obtain ⟨ha,hy,hb⟩ := hs.training_data hready hr
  obtain ⟨hz,hη⟩ := hs.noise_data hready hr
  have h43 : s.ptrs 43=gradientAddress d p k n m := (hp 43 (by decide)).trans hready.gradient
  have h44 : s.ptrs 44=gradientAddress d p k n m+featureDimension d p := (hp 44 (by decide)).trans hready.xbase
  have h46 : s.ptrs 46=gradientAddress d p k n m+2*featureDimension d p := (hp 46 (by decide)).trans hready.agbase
  have h48 : s.ptrs 48=gradientAddress d p k n m+3*featureDimension d p := (hp 48 (by decide)).trans hready.midpoint
  have h50 : s.ptrs 50=gradientAddress d p k n m+4*featureDimension d p+(r : ℤ)*featureDimension d p := by rw [hs.bankCursor,hready.bankCursor]
  have hrD : 0≤(r : ℤ)*(featureDimension d p : ℤ) := by positivity
  obtain ⟨t,cost,he,hcost,hstored,h42,h50next,h53,h22,hgc,hec,hframe,hregs,hptr⟩ := train_record_correct ω
    (featureDimension d p) n (regressionTau (radius d p) n ε δ) (optimizerStep d p n ε δ)
    (coefficientFeatures d p (trainingBlocks d k n m S b)) (coefficientLabels (trainingBlocks d k n m S b))
    (normalBlockDraw k n (featureDimension d p) 0 ω b) s
    ((hp 15 (by decide)).trans hready.dimension) ((hp 16 (by decide)).trans hready.trainingSize)
    ((hp 17 (by decide)).trans hready.stride)
    ((hreg 50 (by decide)).trans hτ) ((hreg 51 (by decide)).trans hβ)
    ((hreg 55 (by decide)).trans h1) ((hreg 56 (by decide)).trans h2) ((hreg 59 (by decide)).trans hinv)
    (by rw [h43,h44]) (by rw [h44,h46]; omega) (by rw [h46,h48]; omega)
    (by rw [h48,h50]; omega) (hs.rows_bound hready hr) (hs.noise_bound hready hr) ha hy hb hz hη
  refine ⟨t,cost,he,hcost,?_⟩
  constructor
  · intro q hq
    exact (hptr q hq).trans (hp q hq)
  · intro q hq
    exact (hregs q hq).trans (hreg q hq)
  · rw [h22,hs.counter]
    push_cast
    ring
  · rw [h53,hs.blockCursor]
    push_cast
    ring
  · rw [h42,hs.noiseCursor]
    push_cast
    ring
  · rw [h50next,hs.bankCursor]
    push_cast
    ring
  · intro i hi
    rcases Nat.lt_or_eq_of_le (show i.val≤r by omega) with hir|hir
    · have hm : readArray t.mem (s₀.ptrs 50+(i.val : ℤ)*featureDimension d p) (featureDimension d p)=
          readArray s.mem (s₀.ptrs 50+(i.val : ℤ)*featureDimension d p) (featureDimension d p) := by
        apply readArray_congr
        intro l hl
        apply hframe
        · right
          rw [h48,hready.bankCursor]
          have hiD : 0≤(i.val : ℤ)*(featureDimension d p : ℤ) := by positivity
          omega
        · left
          rw [hs.bankCursor]
          exact encoded_index_interval (s₀.ptrs 50) (featureDimension d p) i.val r l hir hl
      rw [hm]
      exact hs.written i hir
    · have hib : i=b := Fin.ext hir
      subst i
      rw [← hs.bankCursor]
      exact hstored
  · intro z hzWork hzBank
    have hzOld : z<s₀.ptrs 50 ∨ s₀.ptrs 50+(r : ℤ)*featureDimension d p≤z := by
      rcases hzBank with h|h
      · exact Or.inl h
      · right
        have he : ((r+1 : ℕ) : ℤ)*(featureDimension d p : ℤ)=(r : ℤ)*featureDimension d p+featureDimension d p := by push_cast; ring
        rw [he] at h
        omega
    rw [hframe z (by simpa only [hp 43 (by decide),hp 48 (by decide)] using hzWork) ?_]
    · exact hs.memoryFrame z hzWork hzOld
    · rw [hs.bankCursor]
      rcases hzBank with h|h
      · left
        omega
      · right
        push_cast at h
        nlinarith only [h]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMBlocksLoop
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def trainingBlocksCommand : Cmd := .loop (.pointer 22 19) trainRecordCommand
abbrev trainBlockCost (D n : ℕ) : ℕ := 30+25*D+4*n+4*(n*(D+2))+n*(107+102*D+n*(32+20*D))
lemma training_blocks_correct (ω : PolySampIso.Streams) (d p k M n m : ℕ) (ε δ : ℝ)
    (S : Fin (k*n+m) → Example d) (s : Store) (hs : ReadyHeap d p k M n m ε δ S ω s) :
    ∃ t cost, Eval ω trainingBlocksCommand s t cost ∧ cost≤2+k*(2+trainBlockCost (featureDimension d p) n) ∧
      BlocksInvariant d p k M n m ε δ S ω s k t := by
  have htrue : ∀ r, r<k → ∀ u, BlocksInvariant d p k M n m ε δ S ω s r u → Test.holds u (.pointer 22 19) := by
    intro r hr u hu
    change u.ptrs 22≤u.ptrs 19
    rw [hu.counter,hu.fixedPointers 19 (by decide),hs.blocks]
    omega
  have hfalse : ∀ u, BlocksInvariant d p k M n m ε δ S ω s k u → ¬Test.holds u (.pointer 22 19) := by
    intro u hu
    change ¬u.ptrs 22≤u.ptrs 19
    rw [hu.counter,hu.fixedPointers 19 (by decide),hs.blocks]
    omega
  have hbody : ∀ r, r<k → ∀ u, BlocksInvariant d p k M n m ε δ S ω s r u →
      ∃ t cost, cost≤trainBlockCost (featureDimension d p) n ∧ Eval ω trainRecordCommand u t cost ∧
        BlocksInvariant d p k M n m ε δ S ω s (r+1) t := by
    intro r hr u hu
    obtain ⟨t,cost,he,hcost,ht⟩ := blocks_invariant_step ω d p k M n m ε δ S s hs r hr u hu
    exact ⟨t,cost,hcost,he,ht⟩
  obtain ⟨t,cost,hcost,he,ht⟩ := eval_loop_invariant ω (.pointer 22 19) trainRecordCommand k
    (trainBlockCost (featureDimension d p) n) (BlocksInvariant d p k M n m ε δ S ω s) htrue hfalse hbody s
    (BlocksInvariant.initial d p k M n m ε δ S ω s hs.counter)
  exact ⟨t,cost,he,hcost,ht⟩
lemma trainBlockCost_bound (D n : ℕ) (hD : 1≤D) (hn : 1≤n) : trainBlockCost D n≤400*n^2*D := by
  have hn2 : n≤n^2 := by nlinarith
  have hnQ : n≤n^2*D := hn2.trans (Nat.le_mul_of_pos_right _ hD)
  have hDQ : D≤n^2*D := by have := Nat.mul_le_mul_right D (show 1≤n^2 by nlinarith); simpa using this
  have hNQ : n^2≤n^2*D := Nat.le_mul_of_pos_right _ hD
  have hnd : n*D≤n^2*D := Nat.mul_le_mul_right D hn2
  have hQ : 1≤n^2*D := hn.trans hnQ
  unfold trainBlockCost
  nlinarith only [hnQ,hDQ,hNQ,hnd,hQ]
lemma trainingBlocks_cost_bound (k D n : ℕ) (hk : 1≤k) (hD : 1≤D) (hn : 1≤n) :
    2+k*(2+trainBlockCost D n)≤500*k*n^2*D := by
  have hb := trainBlockCost_bound D n hD hn
  have hQ : 1≤n^2*D := by have hm := Nat.mul_le_mul_right D (show 1≤n^2 by nlinarith); nlinarith
  have hmult := Nat.mul_le_mul_left k hb
  have hkQ : k≤k*(n^2*D) := Nat.le_mul_of_pos_right _ hQ
  have h1Q : 1≤k*(n^2*D) := hk.trans hkQ
  nlinarith only [hmult,hkQ,h1Q]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMActiveTraining
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
abbrev matrixWork (d p k n m : ℕ) : ℕ :=
  60+6*(n+k+m)+(k*n+m)*(2+120*featureDimension d p*(d+p+1))
abbrev heapWork (d p k n m : ℕ) : ℕ :=
  70+12*noiseCount k n (featureDimension d p)+16*featureDimension d p+
    6*(n*(featureDimension d p+2))+10*(k*featureDimension d p)
abbrev blocksWork (d p k n : ℕ) : ℕ := 2+k*(2+trainBlockCost (featureDimension d p) n)
abbrev activeTrainingWork (d p k n m : ℕ) : ℕ := matrixWork d p k n m+heapWork d p k n m+blocksWork d p k n
def activeTrainingCommand : Cmd := .seq prepareMatrixCommand (.seq readyHeapCommand trainingBlocksCommand)
lemma active_training_correct (ω : PolySampIso.Streams) (d p k M n m : ℕ) (hn : 0 < n) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) (input : ℕ → ℝ)
    (S : Fin (k*n+m) → Example d) (hS : InputRows d (k*n+m) S input)
    (h4 : input 4=n) (h2 : input 2=k) (h5 : input 5=m) (h6 : input 6=ε) (h7 : input 7=δ)
    (s : Store) (hs : PreparedShape d p M (k*n+m) n input s)
    (hDn : featureDimension d p ≤ n) (hgc : s.gc=0) (hec : s.ec=0) :
    ∃ seed t cost, Eval ω activeTrainingCommand s t cost ∧ cost ≤ activeTrainingWork d p k n m ∧
      ReadyHeap d p k M n m ε δ S ω seed ∧ BlocksInvariant d p k M n m ε δ S ω seed k t ∧ t.ec=0 := by
  obtain ⟨u,cu,hu,hcu,huMatrix⟩ := prepare_matrix_correct ω d p k M n m hn ε δ hε hδ input S hS h4 h2 h5 h6 h7 s hs hDn hgc hec
  obtain ⟨seed,hseed,hReady⟩ := ready_heap_correct ω d p k M n m ε δ input S u huMatrix
  obtain ⟨t,ct,ht,hct,hInv⟩ := training_blocks_correct ω d p k M n m ε δ S seed hReady
  have hall : Eval ω activeTrainingCommand s t (cu+heapWork d p k n m+ct) := by
    convert! Eval.seq hu (Eval.seq hseed ht) using 1 <;> simp only [heapWork] <;> omega
  have hcur := ht.cursors_preserved (by decide)
  refine ⟨seed,t,_,hall,?_,hReady,hInv,hcur.2.trans hReady.exponentialCursor⟩
  dsimp only [activeTrainingWork,matrixWork,heapWork,blocksWork] at hcu hct ⊢
  omega
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMValidationRows
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open AlgorithmInfrastructure
lemma BlocksInvariant.validation_rows {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {s₀ s : Store}
    (hready : ReadyHeap d p k M n m ε δ S ω s₀) (hs : BlocksInvariant d p k M n m ε δ S ω s₀ k s)
    (i : Fin m) :
    readArray s.mem (s.ptrs 53+(i.val : ℤ)*((featureDimension d p : ℤ)+2)) (featureDimension d p+2)=
      encodedRow d p (validationBlock d k n m S i).1 (validationBlock d k n m S i).2 := by
  let idx : Fin (k*n+m) := ⟨k*n+i.val,by have hi := i.isLt; omega⟩
  have addr : s.ptrs 53+(i.val : ℤ)*((featureDimension d p : ℤ)+2)=
      matrixAddress d (k*n+m)+(idx.val : ℤ)*((featureDimension d p : ℤ)+2) := by
    rw [hs.blockCursor,hready.blockBase]
    dsimp only [idx]
    push_cast
    ring
  rw [addr]
  have hmem : readArray s.mem (matrixAddress d (k*n+m)+(idx.val : ℤ)*((featureDimension d p : ℤ)+2))
      (featureDimension d p+2)=readArray s₀.mem (matrixAddress d (k*n+m)+(idx.val : ℤ)*((featureDimension d p : ℤ)+2))
      (featureDimension d p+2) := by
    apply readArray_congr
    intro l hl
    apply hs.memory_before_gradient hready
    have hbound := encoded_index_interval (matrixAddress d (k*n+m)) (featureDimension d p+2) idx.val (k*n+m) l idx.isLt hl
    simp only [Nat.cast_add,Nat.cast_ofNat] at hbound
    dsimp only [gradientAddress,noiseAddress]
    have hpos : 0 ≤ (noiseCount k n (featureDimension d p) : ℤ) := by positivity
    simp only [noiseCount,Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hbound hpos ⊢
    omega
  rw [hmem,hready.rows idx]
  rfl
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMPostTraining
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open AlgorithmInfrastructure
lemma post_training_bank {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {seed s : Store}
    (hReady : ReadyHeap d p k M n m ε δ S ω seed) (hs : BlocksInvariant d p k M n m ε δ S ω seed k s)
    (j : Fin k) :
    readArray s.mem (s.ptrs 49+(j.val : ℤ)*featureDimension d p) (featureDimension d p)=
      List.ofFn (fun i => coefficientIsometry d p
        (optimizerDraw d p n ε δ (trainingBlocks d k n m S j) (normalBlockDraw k n (featureDimension d p) 0 ω j)).val i) := by
  have hb : seed.ptrs 50=seed.ptrs 49 := by rw [hReady.bankCursor,hReady.bankBase]
  rw [hs.fixedPointers 49 (by decide),← hb]
  simpa only [trainedVectors_eq_optimizerDraw] using hs.written j j.isLt
lemma post_training_geometry {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {seed s : Store}
    (hReady : ReadyHeap d p k M n m ε δ S ω seed) (hs : BlocksInvariant d p k M n m ε δ S ω seed k s) :
    0 ≤ s.ptrs 49 ∧ s.ptrs 49+(k : ℤ)*featureDimension d p ≤ s.ptrs 13 ∧
      s.ptrs 53+(m : ℤ)*((featureDimension d p : ℤ)+2) ≤ s.ptrs 13 := by
  have h49 : s.ptrs 49=gradientAddress d p k n m+4*featureDimension d p :=
    (hs.fixedPointers 49 (by decide)).trans hReady.bankBase
  have h13 : s.ptrs 13=gradientAddress d p k n m+4*featureDimension d p+(k : ℤ)*featureDimension d p :=
    (hs.fixedPointers 13 (by decide)).trans hReady.freeBase
  have hval : s.ptrs 53+(m : ℤ)*((featureDimension d p : ℤ)+2)=noiseAddress d p (k*n+m) := by
    rw [hs.blockCursor,hReady.blockBase]
    dsimp only [noiseAddress]
    push_cast
    ring
  refine ⟨?_,?_,?_⟩
  · rw [h49]
    dsimp only [gradientAddress,noiseAddress,matrixAddress,workspaceBase]
    positivity
  · rw [h49,h13]
  · rw [hval,h13]
    dsimp only [gradientAddress]
    have hT : 0 ≤ (noiseCount k n (featureDimension d p) : ℤ) := by positivity
    have hD : 0 ≤ (featureDimension d p : ℤ) := by positivity
    have hkD : 0 ≤ (k : ℤ)*(featureDimension d p : ℤ) := by positivity
    omega
lemma post_training_parameters {d p k M n m : ℕ} {ε δ : ℝ} {S : Fin (k*n+m) → Example d}
    {ω : PolySampIso.Streams} {seed s : Store}
    (hReady : ReadyHeap d p k M n m ε δ S ω seed) (hs : BlocksInvariant d p k M n m ε δ S ω seed k s) :
    s.ptrs 15=featureDimension d p ∧ s.ptrs 2=M ∧ s.ptrs 19=k ∧ s.ptrs 20=m ∧ s.regs 53=ε := by
  refine ⟨(hs.fixedPointers 15 (by decide)).trans hReady.dimension,
    (hs.fixedPointers 2 (by decide)).trans hReady.thresholds,
    (hs.fixedPointers 19 (by decide)).trans hReady.blocks,
    (hs.fixedPointers 20 (by decide)).trans hReady.validationSize,?_⟩
  exact (hs.fixedRegisters 53 (by decide)).trans hReady.parameters.2.2.2.1
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMValidationInit
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def validationCountPrefix : List Op := [.pointerReal 0 19,.pointerReal 1 2,.mul 40 0 1]
def validationInitTail : List Op := [.pset 25 1,.pset 26 1,.pcopy 55 49,.pcopy 51 53,
  .pcopy 56 13,.pcopy 57 13,.literal 66 0]
def validationInitCommand : Cmd := .seq (.block validationCountPrefix) (.seq (naturalCommand 24) (.block validationInitTail))
lemma validation_init_correct (ω : PolySampIso.Streams) (k M : ℕ) (s : Store)
    (hk : s.ptrs 19=k) (hM : s.ptrs 2=M) :
    ∃ t, Eval ω validationInitCommand s t (17+6*(k*M)) ∧
      t.ptrs 24=k*M ∧ t.ptrs 25=1 ∧ t.ptrs 26=1 ∧ t.ptrs 55=s.ptrs 49 ∧
      t.ptrs 51=s.ptrs 53 ∧ t.ptrs 56=s.ptrs 13 ∧ t.ptrs 57=s.ptrs 13 ∧ t.regs 66=0 ∧
      t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,40,41,43,44,66} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({24,25,26,51,55,56,57} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω validationCountPrefix s
  have hu : Eval ω (.block validationCountPrefix) s u 3 := eval_block ω _ s
  have u40 : u.regs 40=(k*M : ℕ) := by simp [u,blockAct,validationCountPrefix,Op.act,hk,hM,Nat.cast_mul]
  obtain ⟨v,hv,hv24,hvm,hvgc,hvec,hvr,hvp⟩ := natural_command_correct ω (k*M) 24 u u40
  let t := blockAct ω validationInitTail v
  have ht : Eval ω (.block validationInitTail) v t 7 := eval_block ω _ v
  have hall : Eval ω validationInitCommand s t (17+6*(k*M)) := by
    convert! Eval.seq hu (Eval.seq hv ht) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,?_,?_,?_,?_,?_,?_,?_,?_,hvm,hc.1,hc.2,?_,?_⟩
  · simpa [t,blockAct,validationInitTail,Op.act] using hv24
  · simp [t,blockAct,validationInitTail,Op.act]
  · simp [t,blockAct,validationInitTail,Op.act]
  · simp [t,blockAct,validationInitTail,Op.act,hvp 49 (by omega),u,blockAct,validationCountPrefix]
  · simp [t,blockAct,validationInitTail,Op.act,hvp 53 (by omega),u,blockAct,validationCountPrefix]
  · simp [t,blockAct,validationInitTail,Op.act,hvp 13 (by omega),u,blockAct,validationCountPrefix]
  · simp [t,blockAct,validationInitTail,Op.act,hvp 13 (by omega),u,blockAct,validationCountPrefix]
  · simp [t,blockAct,validationInitTail,Op.act]
  · intro r hr
    apply hall.register_preserved
    simp [validationInitCommand,validationCountPrefix,validationInitTail,naturalCommand,naturalLoop,naturalInit,naturalStep,
      Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [validationInitCommand,validationCountPrefix,validationInitTail,naturalCommand,naturalLoop,naturalInit,naturalStep,
      Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMValidationSample
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def countErrorCommand : Cmd := .cond (.real 0) .skip (.block [.literal 0 1,.add 65 65 0])
lemma count_error_correct (ω : PolySampIso.Streams) (s : Store) :
    ∃ t cost, Eval ω countErrorCommand s t cost ∧ cost ≤ 4 ∧
      t.regs 65=s.regs 65+(if s.regs 0 ≤ 0 then 0 else 1) ∧
      t.mem=s.mem ∧ t.ptrs=s.ptrs := by
  by_cases h : s.regs 0 ≤ 0
  · refine ⟨s,1,Eval.cond_yes (test := .real 0) (no := .block [.literal 0 1,.add 65 65 0]) h (Eval.skip s),by omega,?_,rfl,rfl⟩
    simp [h]
  · let t := blockAct ω [.literal 0 1,.add 65 65 0] s
    have ht : Eval ω (.block [.literal 0 1,.add 65 65 0]) s t 2 := eval_block ω _ s
    refine ⟨t,4,Eval.cond_no (test := .real 0) (yes := .skip) h ht,by omega,?_,rfl,rfl⟩
    simp [t,blockAct,Op.act,h]
def validationSamplePrefix : List Op := [.pcopy 3 55,.pcopy 4 58]
def validationSampleMargin : List Op := [.load 64 4,.pinc 4,.pinc 4,.pcopy 58 4,
  .sub 0 31 68,.literal 1 0,.sub 0 1 0]
def validationSampleCompare : List Op := [.sub 0 33 64,.mul 0 0 0]
def validationSampleCommand : Cmd := .seq (.block validationSamplePrefix) (.seq dotCommand
  (.seq (.block validationSampleMargin) (.seq signCommand (.seq (.block validationSampleCompare)
    (.seq countErrorCommand (.atom (.pinc 59)))))))
lemma validation_sample_correct (ω : PolySampIso.Streams) (D : ℕ) (v a : Vec D) (y : Bool) (θ : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hθ : s.regs 68=θ)
    (hv : readArray s.mem (s.ptrs 55) D=List.ofFn (fun i => v i))
    (ha : readArray s.mem (s.ptrs 58) D=List.ofFn (fun i => a i))
    (hy : s.mem (s.ptrs 58+D)=label y) :
    ∃ t cost, Eval ω validationSampleCommand s t cost ∧ cost ≤ 23+9*D ∧
      t.regs 65=s.regs 65+(if sign (inner ℝ v a-θ)=y then 0 else 1) ∧
      t.ptrs 58=s.ptrs 58+D+2 ∧ t.ptrs 59=s.ptrs 59+1 ∧ t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31,33,64,65} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12,58,59} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω validationSamplePrefix s
  have hu : Eval ω (.block validationSamplePrefix) s u 2 := eval_block ω _ s
  have um : u.mem=s.mem := rfl
  have u3 : u.ptrs 3=s.ptrs 55 := by simp [u,blockAct,validationSamplePrefix,Op.act]
  have u4 : u.ptrs 4=s.ptrs 58 := by simp [u,blockAct,validationSamplePrefix,Op.act]
  obtain ⟨w,hw,hw31,hwm,hw3,hw4,hwgc,hwec,hwr,hwp⟩ := dot_command_correct ω D v a u
    (by simpa [u,blockAct,validationSamplePrefix,Op.act] using hD)
    (by simpa only [um,u3] using hv) (by simpa only [um,u4] using ha)
  have wm : w.mem=s.mem := hwm.trans um
  have w4 : w.ptrs 4=s.ptrs 58+D := by simpa only [u4] using hw4
  have w68 : w.regs 68=θ := (hwr 68 (by decide)).trans hθ
  let x := blockAct ω validationSampleMargin w
  have hx : Eval ω (.block validationSampleMargin) w x 7 := eval_block ω _ w
  have x0 : x.regs 0= -(inner ℝ v a-θ) := by simp [x,blockAct,validationSampleMargin,Op.act,hw31,w68]
  have x64 : x.regs 64=label y := by simp [x,blockAct,validationSampleMargin,Op.act,wm,w4,hy]
  obtain ⟨f,cf,hf,hcf,hfeq⟩ := sign_command_correct ω x
  let b := blockAct ω validationSampleCompare f
  have hb : Eval ω (.block validationSampleCompare) f b 2 := eval_block ω _ f
  have b0 : b.regs 0=(thresholdStep 0 (inner ℝ v a-θ)-label y)^2 := by
    simp [b,blockAct,validationSampleCompare,Op.act,hfeq,x0,x64,pow_two]
  have b65 : b.regs 65=s.regs 65 := by
    simp [b,blockAct,validationSampleCompare,Op.act,hfeq,x,blockAct,validationSampleMargin,hwr 65 (by decide),u,blockAct,validationSamplePrefix]
  have htest : b.regs 0 ≤ 0 ↔ sign (inner ℝ v a-θ)=y := by
    rw [b0]
    cases y <;> by_cases h : 0 ≤ inner ℝ v a-θ <;> simp [thresholdStep,sign,label,h] <;> norm_num
  obtain ⟨j,cj,hj,hcj,hj65,hjm,hjp⟩ := count_error_correct ω b
  let t := Op.act ω j (.pinc 59)
  have ht : Eval ω (.atom (.pinc 59)) j t 1 := Eval.atom j _
  have hall : Eval ω validationSampleCommand s t (2+(4+9*D)+(7+(cf+(2+(cj+1))))) := by
    convert! Eval.seq hu (Eval.seq hw (Eval.seq hx (Eval.seq hf (Eval.seq hb (Eval.seq hj ht))))) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,_,hall,by omega,?_,?_,?_,?_,hc.1,hc.2,?_,?_⟩
  · change j.regs 65=_
    rw [hj65,b65]
    simp only [htest]
  · change j.ptrs 58=s.ptrs 58+D+2
    rw [hjp]
    simp [b,blockAct,validationSampleCompare,Op.act,hfeq,x,blockAct,validationSampleMargin,w4]
    ring
  · change j.ptrs 59+1=s.ptrs 59+1
    rw [hjp]
    simp [b,blockAct,validationSampleCompare,Op.act,hfeq,x,blockAct,validationSampleMargin,
      hwp 59 (by decide),u,blockAct,validationSamplePrefix]
  · change j.mem=s.mem
    rw [hjm]
    simp [b,blockAct,validationSampleCompare,Op.act,hfeq,x,blockAct,validationSampleMargin,wm]
  · intro r hr
    apply hall.register_preserved
    simp [validationSampleCommand,validationSamplePrefix,validationSampleMargin,validationSampleCompare,countErrorCommand,
      signCommand,dotCommand,dotLoop,dotStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [validationSampleCommand,validationSamplePrefix,validationSampleMargin,validationSampleCompare,countErrorCommand,
      signCommand,dotCommand,dotLoop,dotStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMValidationLoop
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open scoped BigOperators
noncomputable def validationPartial {D : ℕ} (v : Vec D) (a : ℕ → Vec D) (y : ℕ → Bool) (θ : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, if sign (inner ℝ v (a j)-θ)=y j then 0 else 1
structure ValidationInvariant (D : ℕ) (v : Vec D) (a : ℕ → Vec D) (y : ℕ → Bool) (θ : ℝ)
    (s₀ : Store) (r : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ∈ ({15,20,55} : Finset ℕ) → s.ptrs q=s₀.ptrs q
  rowCursor : s.ptrs 58=s₀.ptrs 58+(r : ℤ)*((D : ℤ)+2)
  counter : s.ptrs 59=(r : ℤ)+1
  errorCount : s.regs 65=s₀.regs 65+validationPartial v a y θ r
  threshold : s.regs 68=θ
  memory : s.mem=s₀.mem
def validationLoop : Cmd := .loop (.pointer 59 20) validationSampleCommand
lemma validation_loop_correct (ω : PolySampIso.Streams) (D m : ℕ) (v : Vec D) (a : ℕ → Vec D) (y : ℕ → Bool)
    (θ : ℝ) (s : Store) (hD : s.ptrs 15=D) (hm : s.ptrs 20=m) (hθ : s.regs 68=θ) (hcount : s.ptrs 59=1)
    (hv : readArray s.mem (s.ptrs 55) D=List.ofFn (fun i => v i))
    (ha : ∀ j, j < m → readArray s.mem (s.ptrs 58+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j < m → s.mem (s.ptrs 58+(j : ℤ)*((D : ℤ)+2)+D)=label (y j)) :
    ∃ t cost, Eval ω validationLoop s t cost ∧ cost ≤ 2+m*(25+9*D) ∧
      t.regs 65=s.regs 65+validationPartial v a y θ m ∧ t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31,33,64,65} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12,58,59} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let Inv := ValidationInvariant D v a y θ s
  have hinit : Inv 0 s := by
    constructor <;> simp_all [validationPartial]
  have htrue : ∀ j, j < m → ∀ u, Inv j u → Test.holds u (.pointer 59 20) := by
    intro j hj u hu
    change u.ptrs 59 ≤ u.ptrs 20
    rw [hu.counter,hu.fixedPointers 20 (by simp),hm]
    omega
  have hfalse : ∀ u, Inv m u → ¬Test.holds u (.pointer 59 20) := by
    intro u hu
    change ¬u.ptrs 59 ≤ u.ptrs 20
    rw [hu.counter,hu.fixedPointers 20 (by simp),hm]
    omega
  have hbody : ∀ j, j < m → ∀ u, Inv j u → ∃ t cost, cost ≤ 23+9*D ∧ Eval ω validationSampleCommand u t cost ∧ Inv (j+1) t := by
    intro j hj u hu
    have u15 := (hu.fixedPointers 15 (by simp)).trans hD
    have u55 := hu.fixedPointers 55 (by simp)
    obtain ⟨t,cost,he,hcost,h65,h58,h59,htm,htgc,htec,htr,htp⟩ := validation_sample_correct ω D v (a j) (y j) θ u
      u15 hu.threshold (by rwa [hu.memory,u55])
      (by rw [hu.memory,hu.rowCursor]; exact ha j hj)
      (by rw [hu.memory,hu.rowCursor]; exact hy j hj)
    refine ⟨t,cost,hcost,he,?_⟩
    constructor
    · intro q hq
      exact (htp q (by simp only [Finset.mem_insert,Finset.mem_singleton] at hq; rcases hq with rfl|rfl|rfl <;> decide)).trans (hu.fixedPointers q hq)
    · rw [h58,hu.rowCursor]
      push_cast
      ring
    · rw [h59,hu.counter]
      push_cast
      ring
    · rw [h65,hu.errorCount]
      simp only [validationPartial,Finset.sum_range_succ]
      ring
    · exact (htr 68 (by decide)).trans hu.threshold
    · exact htm.trans hu.memory
  obtain ⟨t,cost,hcost,he,ht⟩ := eval_loop_invariant ω (.pointer 59 20) validationSampleCommand m (23+9*D)
    Inv htrue hfalse hbody s hinit
  have hc := he.cursors_preserved (by decide)
  refine ⟨t,cost,he,?_,ht.errorCount,ht.memory,hc.1,hc.2,?_,?_⟩
  · convert! hcost using 1 <;> ring
  · intro r hr
    apply he.register_preserved
    simp [validationSampleCommand,validationSamplePrefix,validationSampleMargin,validationSampleCompare,countErrorCommand,
      signCommand,dotCommand,dotLoop,dotStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply he.pointer_preserved
    simp [validationSampleCommand,validationSamplePrefix,validationSampleMargin,validationSampleCompare,countErrorCommand,
      signCommand,dotCommand,dotLoop,dotStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMCandidateWeight
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def candidateWeightPrefix : List Op := [.pointerReal 0 26,.literal 1 2,.mul 0 0 1,.literal 1 1,
  .sub 0 0 1,.pointerReal 1 2,.div 0 0 1,.literal 1 1,.sub 68 0 1,
  .pcopy 58 51,.pset 59 1,.literal 65 0]
def candidateWeightTail : List Op := [.mul 0 53 65,.literal 1 2,.div 0 0 1,.literal 1 0,
  .sub 0 1 0,.exp 0 0,.store 57 0,.add 66 66 0,.pinc 57,.pinc 26]
def candidateWeightCommand : Cmd := .seq (.block candidateWeightPrefix)
  (.seq validationLoop (.block candidateWeightTail))
lemma candidate_weight_correct (ω : PolySampIso.Streams) (D m M l : ℕ) (v : Vec D)
    (a : ℕ → Vec D) (y : ℕ → Bool) (ε : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hm : s.ptrs 20=m) (hM : s.ptrs 2=M) (hl : s.ptrs 26=l+1) (hε : s.regs 53=ε)
    (hv : readArray s.mem (s.ptrs 55) D=List.ofFn (fun i => v i))
    (ha : ∀ j, j < m → readArray s.mem (s.ptrs 51+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j < m → s.mem (s.ptrs 51+(j : ℤ)*((D : ℤ)+2)+D)=label (y j)) :
    let θ := -1+(2*(l : ℝ)+1)/M
    let weight := Real.exp (-ε*validationPartial v a y θ m/2)
    ∃ t cost, Eval ω candidateWeightCommand s t cost ∧ cost ≤ 24+m*(25+9*D) ∧
      t.mem=Function.update s.mem (s.ptrs 57) weight ∧ t.regs 66=s.regs 66+weight ∧
      t.ptrs 57=s.ptrs 57+1 ∧ t.ptrs 26=s.ptrs 26+1 ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ∉ ({0,1,31,33,64,65,66,68} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({3,4,12,26,57,58,59} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  dsimp only
  let θ : ℝ := -1+(2*(l : ℝ)+1)/M
  let weight := Real.exp (-ε*validationPartial v a y θ m/2)
  let u := blockAct ω candidateWeightPrefix s
  have hu : Eval ω (.block candidateWeightPrefix) s u 12 := eval_block ω _ s
  have uθ : u.regs 68=θ := by
    simp [u,blockAct,candidateWeightPrefix,Op.act,hM,hl,θ]
    push_cast
    ring
  have umem : u.mem=s.mem := rfl
  have u58 : u.ptrs 58=s.ptrs 51 := by simp [u,blockAct,candidateWeightPrefix,Op.act]
  obtain ⟨w,cw,hw,hcw,hw65,hwm,hwgc,hwec,hwr,hwp⟩ := validation_loop_correct ω D m v a y θ u
    (by simpa [u,blockAct,candidateWeightPrefix,Op.act] using hD)
    (by simpa [u,blockAct,candidateWeightPrefix,Op.act] using hm) uθ
    (by simp [u,blockAct,candidateWeightPrefix,Op.act])
    (by simpa [u,blockAct,candidateWeightPrefix,Op.act] using hv)
    (fun j hj => by simpa only [umem,u58] using ha j hj)
    (fun j hj => by simpa only [umem,u58] using hy j hj)
  have w65 : w.regs 65=validationPartial v a y θ m := by
    simpa [u,blockAct,candidateWeightPrefix,Op.act] using hw65
  have w53 : w.regs 53=ε := by
    rw [hwr 53 (by decide)]
    exact hε
  have w66 : w.regs 66=s.regs 66 := by
    rw [hwr 66 (by decide)]
    rfl
  have w57 : w.ptrs 57=s.ptrs 57 := by rw [hwp 57 (by decide)]; rfl
  have w26 : w.ptrs 26=s.ptrs 26 := by rw [hwp 26 (by decide)]; rfl
  have wm : w.mem=s.mem := hwm.trans umem
  let t := blockAct ω candidateWeightTail w
  have ht : Eval ω (.block candidateWeightTail) w t 10 := eval_block ω _ w
  have hall : Eval ω candidateWeightCommand s t (12+cw+10) := by
    convert! Eval.seq hu (Eval.seq hw ht) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,_,hall,by omega,?_,?_,?_,?_,hc.1,hc.2,?_,?_⟩
  · simp [t,blockAct,candidateWeightTail,Op.act,wm,w57,w53,w65,weight,θ,neg_div]
  · simp [t,blockAct,candidateWeightTail,Op.act,w66,w53,w65,weight,θ,neg_div]
  · simp [t,blockAct,candidateWeightTail,Op.act,w57]
  · simp [t,blockAct,candidateWeightTail,Op.act,w26]
  · intro r hr
    apply hall.register_preserved
    simp [candidateWeightCommand,candidateWeightPrefix,candidateWeightTail,validationLoop,
      validationSampleCommand,validationSamplePrefix,validationSampleMargin,validationSampleCompare,countErrorCommand,
      signCommand,dotCommand,dotLoop,dotStep,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [candidateWeightCommand,candidateWeightPrefix,candidateWeightTail,validationLoop,
      validationSampleCommand,validationSamplePrefix,validationSampleMargin,validationSampleCompare,countErrorCommand,
      signCommand,dotCommand,dotLoop,dotStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMCandidateCarry
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def candidateCarryCommand : Cmd := .seq (.cond (.pointer 26 2) .skip
  (.seq (.atom (.pset 26 1)) (advanceCommand 55 15))) (.atom (.pinc 25))
lemma candidate_carry_correct (ω : PolySampIso.Streams) (D M l : ℕ) (s : Store)
    (hD : s.ptrs 15=D) (hM : s.ptrs 2=M) (hl : s.ptrs 26=l+2) :
    ∃ t cost, Eval ω candidateCarryCommand s t cost ∧ cost ≤ 7+4*D ∧
      t.ptrs 26=(if l+1 < M then (l : ℤ)+2 else 1) ∧
      t.ptrs 55=s.ptrs 55+(if l+1 < M then (0 : ℤ) else D) ∧ t.ptrs 25=s.ptrs 25+1 ∧
      t.mem=s.mem ∧ t.regs=s.regs ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ q, q ∉ ({12,25,26,55} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  have hc : ∃ u cost, Eval ω (.cond (.pointer 26 2) .skip
      (.seq (.atom (.pset 26 1)) (advanceCommand 55 15))) s u cost ∧ cost ≤ 6+4*D ∧
      u.ptrs 26=(if l+1 < M then (l : ℤ)+2 else 1) ∧
      u.ptrs 55=s.ptrs 55+(if l+1 < M then (0 : ℤ) else D) := by
    by_cases h : l+1 < M
    · refine ⟨s,1,Eval.cond_yes (no := .seq (.atom (.pset 26 1)) (advanceCommand 55 15)) ?_ (Eval.skip s),by omega,?_,?_⟩
      · change s.ptrs 26 ≤ s.ptrs 2
        rw [hl,hM]
        omega
      · simp [h,hl]
      · simp [h]
    · let v := Op.act ω s (.pset 26 1)
      have hv : Eval ω (.atom (.pset 26 1)) s v 1 := Eval.atom s _
      obtain ⟨u,hu,hu55,hum,hur,hugc,huec,hup⟩ := advance_command_correct ω 55 15 D
        (by omega) (by omega) (by omega) v (by simpa [v,Op.act] using hD)
      refine ⟨u,6+4*D,?_,by omega,?_,?_⟩
      · convert! Eval.cond_no (test := .pointer 26 2) (yes := .skip) ?_ (Eval.seq hv hu) using 1 <;> try omega
        change ¬s.ptrs 26 ≤ s.ptrs 2
        rw [hl,hM]
        omega
      · rw [hup 26 (by omega) (by omega)]
        simp [v,Op.act,h]
      · simpa [v,Op.act,h] using hu55
  obtain ⟨u,cost,hu,hcost,hu26,hu55⟩ := hc
  let t := Op.act ω u (.pinc 25)
  have ht : Eval ω (.atom (.pinc 25)) u t 1 := Eval.atom u _
  have hall : Eval ω candidateCarryCommand s t (cost+1) := Eval.seq hu ht
  have hcur := hall.cursors_preserved (by decide)
  refine ⟨t,cost+1,hall,by omega,hu26,hu55,?_,?_,?_,hcur.1,hcur.2,?_⟩
  · change u.ptrs 25+1=s.ptrs 25+1
    have hh := hu.pointer_preserved (q := 25) (by simp [advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers])
    rw [hh]
  · exact hall.memory_preserved (by decide)
  · funext r
    exact hall.register_preserved (by simp [candidateCarryCommand,advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.registers,Op.registers])
  · intro q hq
    apply hall.pointer_preserved
    simp [candidateCarryCommand,advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.GridCounterArithmetic
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma grid_counter_succ (M i : ℕ) (hM : 0 < M) :
    (i+1)%M=(if i%M+1 < M then i%M+1 else 0) ∧
      (i+1)/M=(if i%M+1 < M then i/M else i/M+1) := by
  have hi := Nat.mod_lt i hM
  have he : i+1=(i%M+1)+M*(i/M) := by have := Nat.mod_add_div i M; omega
  rw [he,Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ hM]
  by_cases h : i%M+1 < M
  · simp [h,Nat.mod_eq_of_lt h,Nat.div_eq_of_lt h]
  · have hh : i%M+1=M := by omega
    simp [h,hh,Nat.div_self hM,Nat.add_comm]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RAMCandidateBody
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def candidateBodyCommand : Cmd := .seq candidateWeightCommand candidateCarryCommand
lemma candidate_body_correct (ω : PolySampIso.Streams) (D m M r : ℕ) (hMpos : 0 < M) (B : ℤ) (v : Vec D)
    (a : ℕ → Vec D) (y : ℕ → Bool) (ε : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hm : s.ptrs 20=m) (hM : s.ptrs 2=M) (hl : s.ptrs 26=(r%M : ℕ)+1)
    (hB : s.ptrs 55=B+((r/M : ℕ) : ℤ)*D) (hε : s.regs 53=ε)
    (hv : readArray s.mem (s.ptrs 55) D=List.ofFn (fun i => v i))
    (ha : ∀ j, j < m → readArray s.mem (s.ptrs 51+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j < m → s.mem (s.ptrs 51+(j : ℤ)*((D : ℤ)+2)+D)=label (y j)) :
    let θ := -1+(2*((r%M : ℕ) : ℝ)+1)/M
    let weight := Real.exp (-ε*validationPartial v a y θ m/2)
    ∃ t cost, Eval ω candidateBodyCommand s t cost ∧ cost ≤ 31+4*D+m*(25+9*D) ∧
      t.mem=Function.update s.mem (s.ptrs 57) weight ∧ t.regs 66=s.regs 66+weight ∧
      t.ptrs 57=s.ptrs 57+1 ∧ t.ptrs 26=(((r+1)%M : ℕ) : ℤ)+1 ∧
      t.ptrs 55=B+(((r+1)/M : ℕ) : ℤ)*D ∧ t.ptrs 25=s.ptrs 25+1 ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ∉ ({0,1,31,33,64,65,66,68} : Finset ℕ) → t.regs j=s.regs j) ∧
      (∀ q, q ∉ ({3,4,12,25,26,55,57,58,59} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  dsimp only
  obtain ⟨u,cu,hu,hcu,hum,hu66,hu57,hu26,hugc,huec,hur,hup⟩ := candidate_weight_correct ω D m M (r%M) v a y ε s hD hm hM hl hε hv ha hy
  have u26 : u.ptrs 26=(r%M : ℕ)+2 := by rw [hu26,hl]; omega
  obtain ⟨t,ct,ht,hct,ht26,ht55,ht25,htm,htr,htgc,htec,htp⟩ := candidate_carry_correct ω D M (r%M) u
    ((hup 15 (by decide)).trans hD) ((hup 2 (by decide)).trans hM) u26
  have hall : Eval ω candidateBodyCommand s t (cu+ct) := Eval.seq hu ht
  obtain ⟨hmod,hdiv⟩ := grid_counter_succ M r hMpos
  refine ⟨t,_,hall,by omega,htm.trans hum,?_,?_,?_,?_,?_,htgc.trans hugc,htec.trans huec,?_,?_⟩
  · rw [htr]
    exact hu66
  · rw [htp 57 (by decide)]
    exact hu57
  · rw [ht26,hmod]
    split_ifs <;> push_cast <;> omega
  · rw [ht55,hup 55 (by decide),hB,hdiv]
    split_ifs <;> push_cast <;> ring
  · rw [ht25,hup 25 (by decide)]
  · intro j hj
    rw [htr]
    exact hur j hj
  · intro q hq
    exact (htp q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto)).trans
      (hup q (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq ⊢; tauto))
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMWriteAppend
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma writeArray_snoc (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ) (a : ℝ) :
    Function.update (writeArray mem base xs) (base+(xs.length : ℤ)) a=writeArray mem base (xs++[a]) := by
  induction xs generalizing base with
  | nil => simp [writeArray]
  | cons x xs ih =>
    have hz : base+(↑(x::xs).length : ℤ)=(base+1)+(xs.length : ℤ) := by simp; ring
    rw [writeArray,hz]
    rw [← Function.update_comm (by omega : base+1+(xs.length : ℤ)≠base) a x (writeArray mem (base+1) xs)]
    rw [ih]
    rfl
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.ExponentialUniform
open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def exponentialUniform (z : ℝ) : ℝ := Real.exp (-max 0 z)
lemma exponentialUniform_measurable : Measurable exponentialUniform := by
  unfold exponentialUniform
  fun_prop
lemma exponentialUniform_pos (z : ℝ) : 0<exponentialUniform z := Real.exp_pos _
lemma exponentialUniform_lt_iff (t : ℝ) (ht : 0<t) (ht1 : t≤1) (z : ℝ) :
    exponentialUniform z<t ↔ -Real.log t<z := by
  unfold exponentialUniform
  rw [← Real.lt_log_iff_exp_lt ht]
  have hlog : Real.log t≤0 := Real.log_nonpos ht.le ht1
  have heq : -max 0 z<Real.log t ↔ -Real.log t < max 0 z := by constructor <;> intro h <;> linarith
  rw [heq,lt_max_iff]
  have hn : ¬-Real.log t<0 := by linarith
  simp [hn]
lemma exponentialUniform_cdf (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    (expMeasure 1).real {z | exponentialUniform z<t}=t := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  rcases eq_or_lt_of_le ht with h0|hpos
  · subst t
    have he : {z | exponentialUniform z<0}=(∅ : Set ℝ) := by ext z; simp [not_lt.mpr (exponentialUniform_pos z).le]
    rw [he]
    simp
  · have he : {z | exponentialUniform z<t}=(Iic (-Real.log t))ᶜ := by
      ext z
      simp only [mem_setOf_eq,mem_compl_iff,mem_Iic,not_le,exponentialUniform_lt_iff t hpos ht1]
    rw [he,measureReal_compl measurableSet_Iic,probReal_univ,← cdf_eq_real,
      cdf_expMeasure_eq (by norm_num)]
    have hlog : Real.log t≤0 := Real.log_nonpos hpos.le ht1
    rw [if_pos (by linarith : 0≤ -Real.log t)]
    simp [Real.exp_log hpos]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteWeightCDF
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def weightPrefix {K : ℕ} (w : Fin K → ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin K, if i.val < r then w i else 0
@[simp] lemma weightPrefix_zero {K : ℕ} (w : Fin K → ℝ) : weightPrefix w 0=0 := by simp [weightPrefix]
@[simp] lemma weightPrefix_total {K : ℕ} (w : Fin K → ℝ) : weightPrefix w K=∑ i, w i := by simp [weightPrefix]
lemma weightPrefix_mono {K : ℕ} (w : Fin K → ℝ) (hw : ∀ i,0 ≤ w i) : Monotone (weightPrefix w) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro i hi
  by_cases ha : i.val < a
  · have hb : i.val < b := lt_of_lt_of_le ha hab
    simp [ha,hb]
  · by_cases hb : i.val < b
    · simpa [ha,hb] using hw i
    · simp [ha,hb]
lemma weightPrefix_succ {K : ℕ} (w : Fin K → ℝ) (i : Fin K) :
    weightPrefix w (i.val+1)=weightPrefix w i.val+w i := by
  classical
  calc
    _ = weightPrefix w i.val+∑ j : Fin K, if j=i then w i else 0 := by
      unfold weightPrefix
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases he : j=i
      · subst j
        simp
      · have hv : j.val≠i.val := fun h => he (Fin.ext h)
        by_cases hl : j.val < i.val
        · simp [he,hl,show j.val < i.val+1 by omega]
        · simp [he,hl,show ¬j.val < i.val+1 by omega]
    _ = _ := by simp
noncomputable def weightChoices {K : ℕ} (w : Fin K → ℝ) (u : ℝ) : Finset (Fin K) :=
  univ.filter (fun i => u < weightPrefix w (i.val+1))
noncomputable def pickWeight {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (u : ℝ) : Fin K :=
  if h : (weightChoices w u).Nonempty then (weightChoices w u).min' h else ⟨0,hK⟩
lemma weightChoices_nonempty {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (u : ℝ) (hu : u < ∑ i,w i) :
    (weightChoices w u).Nonempty := by
  let last : Fin K := ⟨K-1,by omega⟩
  refine ⟨last,?_⟩
  have hl : last.val+1=K := by dsimp [last]; omega
  simpa [weightChoices,hl] using hu
lemma pickWeight_eq_iff {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (hw : ∀ i,0 ≤ w i)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u < ∑ i,w i) (i : Fin K) :
    pickWeight hK w u=i ↔ weightPrefix w i.val ≤ u ∧ u < weightPrefix w (i.val+1) := by
  classical
  have hne := weightChoices_nonempty hK w u hu
  rw [pickWeight,dif_pos hne,Finset.min'_eq_iff]
  simp only [weightChoices,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hi,hmin⟩
    refine ⟨?_,hi⟩
    by_cases hiz : i.val=0
    · simpa only [hiz,weightPrefix_zero] using hu0
    · by_contra hn
      have hlt : u < weightPrefix w i.val := lt_of_not_ge hn
      let prev : Fin K := ⟨i.val-1,by omega⟩
      have hp : prev.val+1=i.val := by dsimp [prev]; omega
      have hprev := hmin prev (by rwa [hp])
      have hv := hprev
      change i.val ≤ prev.val at hv
      dsimp only [prev] at hv
      omega
  · rintro ⟨hlow,hhigh⟩
    refine ⟨hhigh,?_⟩
    intro j hj
    by_contra hn
    have hji : j.val+1 ≤ i.val := by change ¬i.val ≤ j.val at hn; omega
    have hp := weightPrefix_mono w hw hji
    linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RAMWeightsInvariant
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
structure WeightInvariant (D k M : ℕ) (w : Fin (k*M) → ℝ) (s₀ : Store) (r : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ∉ ({3,4,12,25,26,55,57,58,59} : Finset ℕ) → s.ptrs q=s₀.ptrs q
  fixedRegisters : ∀ j, j ∉ ({0,1,31,33,64,65,66,68} : Finset ℕ) → s.regs j=s₀.regs j
  counter : s.ptrs 25=(r : ℤ)+1
  thresholdCounter : s.ptrs 26=((r%M : ℕ) : ℤ)+1
  coefficientCursor : s.ptrs 55=s₀.ptrs 49+((r/M : ℕ) : ℤ)*D
  weightCursor : s.ptrs 57=s₀.ptrs 56+(r : ℤ)
  total : s.regs 66=weightPrefix w r
  memory : s.mem=writeArray s₀.mem (s₀.ptrs 56) ((List.ofFn w).take r)
lemma WeightInvariant.data {D k M : ℕ} {w : Fin (k*M) → ℝ} {s₀ s : Store} {r : ℕ}
    (hs : WeightInvariant D k M w s₀ r s) (hM : 0 < M) (hr : r < k*M) (m : ℕ)
    (coef a : ℕ → Vec D) (y : ℕ → Bool)
    (hcoefEnd : s₀.ptrs 49+(k : ℤ)*D ≤ s₀.ptrs 56)
    (hvalEnd : s₀.ptrs 51+(m : ℤ)*((D : ℤ)+2) ≤ s₀.ptrs 56)
    (hcoef : ∀ j, j < k → readArray s₀.mem (s₀.ptrs 49+(j : ℤ)*D) D=List.ofFn (fun i => coef j i))
    (ha : ∀ j, j < m → readArray s₀.mem (s₀.ptrs 51+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j < m → s₀.mem (s₀.ptrs 51+(j : ℤ)*((D : ℤ)+2)+D)=label (y j)) :
    readArray s.mem (s.ptrs 55) D=List.ofFn (fun i => coef (r/M) i) ∧
      (∀ j, j < m → readArray s.mem (s.ptrs 51+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i)) ∧
      (∀ j, j < m → s.mem (s.ptrs 51+(j : ℤ)*((D : ℤ)+2)+D)=label (y j)) := by
  have hquot : r/M < k := (Nat.div_lt_iff_lt_mul hM).mpr (by simpa [Nat.mul_comm] using hr)
  have hend : s₀.ptrs 49+((r/M : ℕ) : ℤ)*D+(D : ℤ) ≤ s₀.ptrs 56 := by
    have hh : ((r/M : ℕ) : ℤ)+1 ≤ k := by exact_mod_cast (show r/M+1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_right hh (show (0 : ℤ) ≤ D by positivity)
    nlinarith only [hm,hcoefEnd]
  refine ⟨?_,?_,?_⟩
  · rw [hs.memory,hs.coefficientCursor,readArray_write_after _ _ _ _ _ hend]
    exact hcoef _ hquot
  · intro j hj
    rw [hs.memory,hs.fixedPointers 51 (by decide),readArray_write_after _ _ _ _ _ ?_]
    · exact ha j hj
    · have hh := encoded_index_interval (s₀.ptrs 51) (D+2) j m (D+1) hj (by omega)
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hh
      omega
  · intro j hj
    rw [hs.memory,hs.fixedPointers 51 (by decide),writeArray_outside _ _ _ _ (Or.inl ?_)]
    · exact hy j hj
    · have hh := encoded_index_interval (s₀.ptrs 51) (D+2) j m D hj (by omega)
      simp only [Nat.cast_add,Nat.cast_ofNat] at hh
      omega
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMWeightsStep
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma weights_invariant_step (ω : PolySampIso.Streams) (D k M m : ℕ) (hMpos : 0 < M)
    (coef a : ℕ → Vec D) (y : ℕ → Bool) (ε : ℝ) (w : Fin (k*M) → ℝ) (s₀ : Store)
    (hD : s₀.ptrs 15=D) (hM : s₀.ptrs 2=M) (hm : s₀.ptrs 20=m) (hε : s₀.regs 53=ε)
    (hcoefEnd : s₀.ptrs 49+(k : ℤ)*D ≤ s₀.ptrs 56)
    (hvalEnd : s₀.ptrs 51+(m : ℤ)*((D : ℤ)+2) ≤ s₀.ptrs 56)
    (hcoef : ∀ j, j < k → readArray s₀.mem (s₀.ptrs 49+(j : ℤ)*D) D=List.ofFn (fun i => coef j i))
    (ha : ∀ j, j < m → readArray s₀.mem (s₀.ptrs 51+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j < m → s₀.mem (s₀.ptrs 51+(j : ℤ)*((D : ℤ)+2)+D)=label (y j))
    (hw : ∀ i : Fin (k*M), w i=Real.exp (-ε*validationPartial (coef (i.val/M)) a y
      (-1+(2*((i.val%M : ℕ) : ℝ)+1)/M) m/2))
    (r : ℕ) (hr : r < k*M) (s : Store) (hs : WeightInvariant D k M w s₀ r s) :
    ∃ t cost, Eval ω candidateBodyCommand s t cost ∧ cost ≤ 31+4*D+m*(25+9*D) ∧
      WeightInvariant D k M w s₀ (r+1) t := by
  obtain ⟨hcv,hav,hyv⟩ := hs.data hMpos hr m coef a y hcoefEnd hvalEnd hcoef ha hy
  obtain ⟨t,cost,he,hcost,htm,ht66,ht57,ht26,ht55,ht25,htgc,htec,htr,htp⟩ := candidate_body_correct ω D m M r hMpos
    (s₀.ptrs 49) (coef (r/M)) a y ε s
    ((hs.fixedPointers 15 (by decide)).trans hD) ((hs.fixedPointers 20 (by decide)).trans hm)
    ((hs.fixedPointers 2 (by decide)).trans hM) hs.thresholdCounter hs.coefficientCursor
    ((hs.fixedRegisters 53 (by decide)).trans hε) hcv hav hyv
  have hweight := hw ⟨r,hr⟩
  change w ⟨r,hr⟩=Real.exp (-ε*validationPartial (coef (r/M)) a y (-1+(2*((r%M : ℕ) : ℝ)+1)/M) m/2) at hweight
  rw [← hweight] at htm ht66
  refine ⟨t,cost,he,hcost,?_⟩
  constructor
  · intro q hq
    exact (htp q hq).trans (hs.fixedPointers q hq)
  · intro j hj
    exact (htr j hj).trans (hs.fixedRegisters j hj)
  · rw [ht25,hs.counter]
    push_cast
    ring
  · exact ht26
  · exact ht55
  · rw [ht57,hs.weightCursor]
    push_cast
    ring
  · rw [ht66,hs.total]
    exact (weightPrefix_succ w ⟨r,hr⟩).symm
  · rw [htm,hs.memory,hs.weightCursor]
    have hlen : ((List.ofFn w).take r).length=r := by simp [List.length_take,min_eq_left (Nat.le_of_lt hr)]
    have happ := writeArray_snoc s₀.mem (s₀.ptrs 56) ((List.ofFn w).take r) (w ⟨r,hr⟩)
    rw [hlen] at happ
    rw [happ]
    congr 1
    have htake := List.take_succ_eq_append_getElem (l := List.ofFn w) (i := r) (by simpa using hr)
    simpa only [List.getElem_ofFn] using htake.symm
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMWeightsLoop
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma WeightInvariant.initial (D k M : ℕ) (w : Fin (k*M) → ℝ) (s : Store)
    (h25 : s.ptrs 25=1) (h26 : s.ptrs 26=1) (h55 : s.ptrs 55=s.ptrs 49)
    (h57 : s.ptrs 57=s.ptrs 56) (h66 : s.regs 66=0) : WeightInvariant D k M w s 0 s := by
  constructor <;> simp_all

def weightsLoop : Cmd := .loop (.pointer 25 24) candidateBodyCommand
lemma weights_loop_correct (ω : PolySampIso.Streams) (D k M m : ℕ) (hMpos : 0 < M)
    (coef a : ℕ → Vec D) (y : ℕ → Bool) (ε : ℝ) (w : Fin (k*M) → ℝ) (s₀ : Store)
    (hD : s₀.ptrs 15=D) (hM : s₀.ptrs 2=M) (hm : s₀.ptrs 20=m) (hε : s₀.regs 53=ε)
    (hcoefEnd : s₀.ptrs 49+(k : ℤ)*D ≤ s₀.ptrs 56)
    (hvalEnd : s₀.ptrs 51+(m : ℤ)*((D : ℤ)+2) ≤ s₀.ptrs 56)
    (hcoef : ∀ j, j < k → readArray s₀.mem (s₀.ptrs 49+(j : ℤ)*D) D=List.ofFn (fun i => coef j i))
    (ha : ∀ j, j < m → readArray s₀.mem (s₀.ptrs 51+(j : ℤ)*((D : ℤ)+2)) D=List.ofFn (fun i => a j i))
    (hy : ∀ j, j < m → s₀.mem (s₀.ptrs 51+(j : ℤ)*((D : ℤ)+2)+D)=label (y j))
    (hw : ∀ i : Fin (k*M), w i=Real.exp (-ε*validationPartial (coef (i.val/M)) a y
      (-1+(2*((i.val%M : ℕ) : ℝ)+1)/M) m/2))
    (hK : s₀.ptrs 24=k*M) (hinit : WeightInvariant D k M w s₀ 0 s₀) :
    ∃ t cost, Eval ω weightsLoop s₀ t cost ∧ cost ≤ 2+(k*M)*(33+4*D+m*(25+9*D)) ∧
      WeightInvariant D k M w s₀ (k*M) t := by
  have htrue : ∀ r, r < k*M → ∀ u, WeightInvariant D k M w s₀ r u → Test.holds u (.pointer 25 24) := by
    intro r hr u hu
    change u.ptrs 25 ≤ u.ptrs 24
    rw [hu.counter,hu.fixedPointers 24 (by decide),hK]
    omega
  have hfalse : ∀ u, WeightInvariant D k M w s₀ (k*M) u → ¬Test.holds u (.pointer 25 24) := by
    intro u hu
    change ¬u.ptrs 25 ≤ u.ptrs 24
    rw [hu.counter,hu.fixedPointers 24 (by decide),hK]
    omega
  have hbody : ∀ r, r < k*M → ∀ u, WeightInvariant D k M w s₀ r u →
      ∃ t cost, cost ≤ 31+4*D+m*(25+9*D) ∧ Eval ω candidateBodyCommand u t cost ∧
        WeightInvariant D k M w s₀ (r+1) t := by
    intro r hr u hu
    obtain ⟨t,cost,he,hcost,ht⟩ := weights_invariant_step ω D k M m hMpos coef a y ε w s₀
      hD hM hm hε hcoefEnd hvalEnd hcoef ha hy hw r hr u hu
    exact ⟨t,cost,hcost,he,ht⟩
  obtain ⟨t,cost,hcost,he,ht⟩ := eval_loop_invariant ω (.pointer 25 24) candidateBodyCommand (k*M)
    (31+4*D+m*(25+9*D)) (WeightInvariant D k M w s₀) htrue hfalse hbody s₀ hinit
  refine ⟨t,cost,he,?_,ht⟩
  convert! hcost using 1 <;> ring
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.FiniteWeightMeasurable
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma pickWeight_measurable_joint {K : ℕ} (hK : 0 < K) :
    Measurable (fun q : (Fin K → ℝ) × ℝ => pickWeight hK q.1 q.2) := by
  classical
  let choose : Finset (Fin K) → Fin K := fun s => if h : s.Nonempty then s.min' h else ⟨0,hK⟩
  have hc : Measurable choose := measurable_of_countable _
  have hs : Measurable (fun q : (Fin K → ℝ) × ℝ => weightChoices q.1 q.2) := by
    apply measurable_finset_iff.mpr
    intro i
    simp only [weightChoices,Finset.mem_filter,Finset.mem_univ,true_and]
    apply measurableSet_setOfPred.1
    apply measurableSet_lt measurable_snd
    unfold weightPrefix
    apply Finset.measurable_sum
    intro j hj
    split_ifs <;> fun_prop
  exact hc.comp hs
lemma pickWeight_measurable {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) : Measurable (pickWeight hK w) :=
  (pickWeight_measurable_joint hK).comp (measurable_const.prodMk measurable_id)
lemma exponentialUniform_interval (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (expMeasure 1).real {z | a ≤ exponentialUniform z ∧ exponentialUniform z < b}=b-a := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hset : {z | a ≤ exponentialUniform z ∧ exponentialUniform z < b}=
      {z | exponentialUniform z < b} \ {z | exponentialUniform z < a} := by ext z; simp only [mem_setOf_eq,mem_diff,not_lt]; tauto
  have hmeas : MeasurableSet {z | exponentialUniform z < a} := measurableSet_lt exponentialUniform_measurable measurable_const
  have hsub : {z | exponentialUniform z < a} ⊆ {z | exponentialUniform z < b} := fun z hz => lt_of_lt_of_le hz hab
  rw [hset,measureReal_sdiff hsub hmeas,exponentialUniform_cdf a ha (hab.trans hb),
    exponentialUniform_cdf b (ha.trans hab) hb]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteWeightSampling
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
local instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
lemma exponentialUniform_lt_one_ae : ∀ᵐ z ∂expMeasure 1, exponentialUniform z < 1 := by
  apply ae_iff.mpr
  apply (measureReal_eq_zero_iff).mp
  have hm := measureReal_compl (μ := expMeasure 1)
    (measurableSet_lt exponentialUniform_measurable (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))))
  rw [probReal_univ,exponentialUniform_cdf 1 (by norm_num) le_rfl] at hm
  convert! hm using 1 <;> simp only [sub_self] <;> ext z <;> simp
noncomputable def weightedPick {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (z : ℝ) : Fin K :=
  pickWeight hK w (exponentialUniform z*(∑ i,w i))
lemma weightedPick_measurable {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) : Measurable (weightedPick hK w) :=
  (pickWeight_measurable hK w).comp (exponentialUniform_measurable.mul_const _)
lemma weightedPick_mass {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (hw : ∀ i,0 < w i) (i : Fin K) :
    (expMeasure 1).real {z | weightedPick hK w z=i}=w i/(∑ j,w j) := by
  let Z := ∑ j,w j
  have hZ : 0 < Z := Finset.sum_pos (fun j hj => hw j) (by exact ⟨⟨0,hK⟩,mem_univ _⟩)
  have hnonneg := fun j => (hw j).le
  have hp0 : 0 ≤ weightPrefix w i.val := by
    have h := weightPrefix_mono w hnonneg (Nat.zero_le i.val)
    simpa using h
  have hpnext : weightPrefix w i.val ≤ weightPrefix w (i.val+1) := weightPrefix_mono w hnonneg (Nat.le_succ _)
  have hpZ : weightPrefix w (i.val+1) ≤ Z := by
    have h := weightPrefix_mono w hnonneg (show i.val+1 ≤ K by omega)
    simpa only [weightPrefix_total] using h
  have hae : {z | weightedPick hK w z=i}=ᵐ[expMeasure 1]
      {z | weightPrefix w i.val/Z ≤ exponentialUniform z ∧ exponentialUniform z < weightPrefix w (i.val+1)/Z} := by
    filter_upwards [exponentialUniform_lt_one_ae] with z hz
    change (weightedPick hK w z=i) = (weightPrefix w i.val/Z ≤ exponentialUniform z ∧ exponentialUniform z < weightPrefix w (i.val+1)/Z)
    apply propext
    change pickWeight hK w (exponentialUniform z*Z)=i ↔ _
    rw [pickWeight_eq_iff hK w hnonneg _ (mul_nonneg (exponentialUniform_pos z).le hZ.le)
      (by simpa only [one_mul] using mul_lt_mul_of_pos_right hz hZ)]
    rw [div_le_iff₀ hZ,lt_div_iff₀ hZ]
  rw [measureReal_congr hae,exponentialUniform_interval _ _ (div_nonneg hp0 hZ.le)
    (div_le_div_of_nonneg_right hpnext hZ.le) ((div_le_one hZ).mpr hpZ),weightPrefix_succ]
  dsimp only [Z]
  ring
lemma weightedPick_law {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (hw : ∀ i,0 < w i) :
    (expMeasure 1).map (weightedPick hK w)=
      ∑ i, ENNReal.ofReal (w i/(∑ j,w j)) • Measure.dirac i := by
  classical
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply (weightedPick_measurable hK w) (measurableSet_singleton i)]
  have hm : (expMeasure 1) ((weightedPick hK w) ⁻¹' {i})=ENNReal.ofReal (w i/(∑ j,w j)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    change ENNReal.ofReal ((expMeasure 1).real {z | weightedPick hK w z=i})=_
    rw [weightedPick_mass hK w hw i]
  rw [hm]
  simp [Measure.finset_sum_apply,Measure.smul_apply,Pi.single_apply]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteWeightJoint
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma weightedPick_measurable_joint {K : ℕ} (hK : 0 < K) :
    Measurable (fun q : (Fin K → ℝ) × ℝ => weightedPick hK q.1 q.2) := by
  have hsum : Measurable (fun q : (Fin K → ℝ) × ℝ => ∑ i,q.1 i) := by fun_prop
  exact (pickWeight_measurable_joint hK).comp
    (measurable_fst.prodMk (((exponentialUniform_measurable.comp measurable_snd).mul hsum)))
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RAMGaussianExponential
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open RegressionGeometry
local instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
noncomputable def normalBlockPlain (k n D offset : ℕ) (g : ℕ → ℝ) :
    Fin k → Fin (n+1) → RegressionNoise n D := normalBlockDraw k n D offset (g,fun _ => 0)
lemma normalBlockPlain_measurable (k n D offset : ℕ) : Measurable (normalBlockPlain k n D offset) := by
  unfold normalBlockPlain normalBlockDraw normalNoiseDraw normalRecord
  apply measurable_pi_lambda
  intro b
  apply measurable_pi_lambda
  intro j
  apply Measurable.prodMk
  · fun_prop
  · exact (PiLp.continuous_toLp 2 (fun _ : Fin D => ℝ)).measurable.comp (by fun_prop)
lemma normalBlockPlain_preserving (k n D offset : ℕ) : MeasurePreserving (normalBlockPlain k n D offset)
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
    (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D))) := by
  have hm := normalBlockPlain_measurable k n D offset
  have h := (normalBlockDraw_preserving k n D offset).map_eq
  change PolySampIso.tape.map (normalBlockPlain k n D offset ∘ Prod.fst)=_ at h
  rw [← Measure.map_map hm measurable_fst] at h
  unfold PolySampIso.tape at h
  rw [measurePreserving_fst.map_eq] at h
  exact ⟨hm,h⟩
lemma normal_blocks_exponential_preserving (k n D offset eoffset : ℕ) :
    MeasurePreserving (fun ω : PolySampIso.Streams => (normalBlockDraw k n D offset ω,ω.2 eoffset))
      PolySampIso.tape
      ((Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D))).prod (expMeasure 1)) := by
  have h1 := normalBlockPlain_preserving k n D offset
  have h2 := measurePreserving_eval_infinitePi (fun _ : ℕ => expMeasure 1) eoffset
  exact h1.prod h2
end PrivateAgnosticHalfspace.Gaussian.RAM
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
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AlgorithmFiniteCoins
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PrivateAgnosticHalfspace.Gaussian
open AlgorithmInfrastructure RegressionGeometry RAM
lemma measurable_index_output {Y : Type*} [MeasurableSpace Y] (k M K : ℕ) (e : Fin K → Fin k × Fin M) :
    Measurable (fun q : (Fin k → Y) × Fin K => (q.1 (e q.2).1,(e q.2).2)) := by
  apply measurable_from_prod_countable_left (α := Fin k → Y) (β := Fin K)
  intro i
  change Measurable (fun v : Fin k → Y => (v (e i).1,(e i).2))
  exact (measurable_pi_apply (e i).1).prodMk measurable_const
lemma measurable_weighted_pick {X : Type*} [MeasurableSpace X] {K : ℕ} (hK : 0 < K)
    (g : X → Fin K → ℝ) (hg : Measurable g) :
    Measurable (fun q : X × ℝ => weightedPick hK (g q.1) q.2) := by
  convert! (weightedPick_measurable_joint hK).comp ((hg.comp measurable_fst).prodMk measurable_snd) using 1
noncomputable def indexedValidationWeights (d p k M m : ℕ) (ε : ℝ) (V : Fin m → Example d)
    (v : Fin k → UnitBall d p) (i : Fin (k*M)) : ℝ :=
  let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  Real.exp (-ε*m*empiricalError V (candidate d p M (v (e i).1).val (e i).2)/2)
lemma indexedValidationWeights_measurable (d p k M m : ℕ) (ε : ℝ) (V : Fin m → Example d) :
    Measurable (indexedValidationWeights d p k M m ε V) := by
  classical
  apply measurable_pi_lambda
  intro i
  let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  have hpred (j : Fin m) : Measurable (fun v : Fin k → UnitBall d p => candidate d p M (v (e i).1).val (e i).2 (V j).1) := by
    have hc : Measurable (fun v : Fin k → UnitBall d p => (v (e i).1).val) :=
      (measurable_pi_apply (e i).1).subtype_val
    have hs : Measurable (fun c : Coeff d p => score d p c (V j).1-(-1+(2*((e i).2.val : ℝ)+1)/M)) := by
      unfold score
      fun_prop
    convert! measurable_sign.comp (hs.comp hc) using 1
  have herr : Measurable (fun v : Fin k → UnitBall d p => empiricalError V (candidate d p M (v (e i).1).val (e i).2)) := by
    unfold empiricalError
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro j hj
    exact measurable_const.ite (measurableSet_eq_fun (hpred j) measurable_const) measurable_const
  convert! ((herr.const_mul (-ε*m)).div_const 2).exp using 1
noncomputable def validationCoin (d p k M m : ℕ) (hK : 0 < k*M) (ε : ℝ) (V : Fin m → Example d)
    (v : Fin k → UnitBall d p) (z : ℝ) : Output d p M :=
  let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  let i := weightedPick hK (indexedValidationWeights d p k M m ε V v) z
  (v (e i).1,(e i).2)
lemma validationCoin_measurable_joint (d p k M m : ℕ) (hK : 0 < k*M) (ε : ℝ) (V : Fin m → Example d) :
    Measurable (fun q : (Fin k → UnitBall d p) × ℝ => validationCoin d p k M m hK ε V q.1 q.2) := by
  let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  have hw := indexedValidationWeights_measurable d p k M m ε V
  have hi : Measurable (fun q : (Fin k → UnitBall d p) × ℝ =>
      weightedPick hK (indexedValidationWeights d p k M m ε V q.1) q.2) :=
    measurable_weighted_pick hK (indexedValidationWeights d p k M m ε V) hw
  have ho := measurable_index_output (Y := UnitBall d p) k M (k*M) e
  convert! ho.comp (measurable_fst.prodMk hi) using 1
lemma validationCoin_law (d p k M m : ℕ) (hK : 0 < k*M) (ε : ℝ) (V : Fin m → Example d)
    (v : Fin k → UnitBall d p) :
    (expMeasure 1).map (validationCoin d p k M m hK ε V v)=selectionLaw d p k M m ε v V := by
  let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  let w := indexedValidationWeights d p k M m ε V v
  let out := fun i : Fin (k*M) => (v (e i).1,(e i).2)
  have ho : Measurable out := measurable_of_countable _
  have hp := weightedPick_law hK w (fun i => Real.exp_pos _)
  change (expMeasure 1).map (out ∘ weightedPick hK w)=_
  rw [← Measure.map_map ho (weightedPick_measurable hK w),hp]
  exact selectionLaw_reindex d p k M m ε v V
lemma map_prod_as_bind {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (f : X × Y → Z) (hf : Measurable f) :
    (μ.prod ν).map f=μ.bind (fun x => ν.map (fun y => f (x,y))) := by
  rw [Measure.prod,map_bind_eq μ _ Measurable.map_prodMk_left f hf]
  congr 1
  funext x
  rw [Measure.map_map hf measurable_prodMk_left]
  rfl
noncomputable def algorithmCoins (d p k M n m : ℕ) (hK : 0 < k*M) (ε δ : ℝ)
    (S : Fin (k*n+m) → Example d) (ω : PolySampIso.Streams) : Output d p M :=
  validationCoin d p k M m hK ε (validationBlock d k n m S)
    (fun b => optimizerDraw d p n ε δ (trainingBlocks d k n m S b)
      (normalBlockDraw k n (featureDimension d p) 0 ω b)) (ω.2 0)
lemma algorithmCoins_law (d p k M n m : ℕ) (hK : 0 < k*M) (ε δ : ℝ)
    (S : Fin (k*n+m) → Example d) :
    Measurable (algorithmCoins d p k M n m hK ε δ S) ∧
      PolySampIso.tape.map (algorithmCoins d p k M n m hK ε δ S)=algorithmLaw concreteOptimizer d p k M n m ε δ S := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  let draw := fun q : Fin k → Fin (n+1) → RegressionNoise n (featureDimension d p) =>
    fun b => optimizerDraw d p n ε δ (trainingBlocks d k n m S b) (q b)
  have hd : MeasurePreserving draw
      (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n (featureDimension d p))))
      (Measure.pi (fun b : Fin k => (concreteOptimizer d p n ε δ (trainingBlocks d k n m S b) : Measure (UnitBall d p)))) := by
    apply measurePreserving_pi
    intro b
    exact ⟨optimizerDraw_measurable d p n ε δ _,rfl⟩
  have hj := (hd.prod (MeasurePreserving.id (expMeasure 1))).comp
    (normal_blocks_exponential_preserving k n (featureDimension d p) 0 0)
  let F := fun q : (Fin k → UnitBall d p) × ℝ =>
    validationCoin d p k M m hK ε (validationBlock d k n m S) q.1 q.2
  have hF : Measurable F := validationCoin_measurable_joint d p k M m hK ε _
  let J := fun ω : PolySampIso.Streams => (draw (normalBlockDraw k n (featureDimension d p) 0 ω),ω.2 0)
  have hJ : MeasurePreserving J PolySampIso.tape
      ((Measure.pi (fun b : Fin k => (concreteOptimizer d p n ε δ (trainingBlocks d k n m S b) : Measure (UnitBall d p)))).prod (expMeasure 1)) := hj
  have heq : algorithmCoins d p k M n m hK ε δ S=F ∘ J := rfl
  refine ⟨by rw [heq]; exact hF.comp hJ.measurable,?_⟩
  rw [heq,← Measure.map_map hF hJ.measurable,hJ.map_eq,map_prod_as_bind _ _ F hF]
  congr 1
  funext v
  exact validationCoin_law d p k M m hK ε _ v
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ValidationErrorBridge
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RAM
lemma validationPartial_finite {D m : ℕ} (v : Vec D) (a : Fin m → Vec D) (y : Fin m → Bool) (θ : ℝ) :
    validationPartial v (extendFin a 0) (extendFin y false) θ m=
      ∑ i : Fin m, if sign (inner ℝ v (a i)-θ)=y i then (0 : ℝ) else 1 := by
  unfold validationPartial
  rw [Finset.sum_range]
  simp
lemma validationPartial_candidate (d p M m : ℕ) (v : Coeff d p) (l : Fin M) (V : Fin m → Example d) :
    validationPartial (coefficientIsometry d p v) (extendFin (coefficientFeatures d p V) 0)
      (extendFin (fun i => (V i).2) false) (-1+(2*(l.val : ℝ)+1)/M) m=
      (m : ℝ)*empiricalError V (candidate d p M v l) := by
  rw [validationPartial_finite]
  have hscore (i : Fin m) : inner ℝ (coefficientIsometry d p v) (coefficientFeatures d p V i)=score d p v (V i).1 :=
    (coefficientIsometry d p).inner_map_map v (clipped d p (V i).1)
  simp_rw [hscore]
  unfold empiricalError candidate
  by_cases hm : m=0
  · subst m
    simp
  · have hmr : (m : ℝ)≠0 := by exact_mod_cast hm
    field_simp
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.IndexedWeightRegression
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
open RAM
lemma indexedValidationWeights_regression (d p k M m : ℕ) (ε : ℝ) (V : Fin m → Example d)
    (v : Fin k → UnitBall d p) (i : Fin (k*M)) :
    indexedValidationWeights d p k M m ε V v i=
      Real.exp (-ε*validationPartial
        (extendFin (fun j => coefficientIsometry d p (v j).val) 0 (i.val/M))
        (extendFin (coefficientFeatures d p V) 0) (extendFin (fun j => (V j).2) false)
        (-1+(2*((i.val%M : ℕ) : ℝ)+1)/M) m/2) := by
  let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  have hfirst : (e i).1.val=i.val/M := rfl
  have hsecond : (e i).2.val=i.val%M := rfl
  have hc : extendFin (fun j => coefficientIsometry d p (v j).val) 0 (i.val/M)=
      coefficientIsometry d p (v (e i).1).val := by rw [← hfirst,extendFin_val]
  rw [hc,← hsecond]
  change Real.exp (-ε*(m : ℝ)*empiricalError V (candidate d p M (v (e i).1).val (e i).2)/2)=_
  rw [show -ε*(m : ℝ)*empiricalError V (candidate d p M (v (e i).1).val (e i).2)/2=
      -ε*((m : ℝ)*empiricalError V (candidate d p M (v (e i).1).val (e i).2))/2 by ring,
    ← validationPartial_candidate d p M m (v (e i).1).val (e i).2 V]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RAMWeightsFromBank
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open scoped BigOperators
lemma weights_from_bank_correct (ω : PolySampIso.Streams) (d p k M m : ℕ) (hMpos : 0 < M) (ε : ℝ)
    (V : Fin m → Example d) (v : Fin k → UnitBall d p) (s : Store)
    (hD : s.ptrs 15=featureDimension d p) (hM : s.ptrs 2=M) (hm : s.ptrs 20=m) (hK : s.ptrs 24=k*M)
    (hε : s.regs 53=ε) (h25 : s.ptrs 25=1) (h26 : s.ptrs 26=1) (h55 : s.ptrs 55=s.ptrs 49)
    (h57 : s.ptrs 57=s.ptrs 56) (h66 : s.regs 66=0)
    (hbankEnd : s.ptrs 49+(k : ℤ)*featureDimension d p ≤ s.ptrs 56)
    (hvalEnd : s.ptrs 51+(m : ℤ)*((featureDimension d p : ℤ)+2) ≤ s.ptrs 56)
    (hbank : ∀ j : Fin k, readArray s.mem (s.ptrs 49+(j.val : ℤ)*featureDimension d p) (featureDimension d p)=
      List.ofFn (fun i => coefficientIsometry d p (v j).val i))
    (hval : ∀ j : Fin m, readArray s.mem (s.ptrs 51+(j.val : ℤ)*((featureDimension d p : ℤ)+2))
      (featureDimension d p+2)=encodedRow d p (V j).1 (V j).2) :
    ∃ t cost, Eval ω weightsLoop s t cost ∧ cost ≤ 2+(k*M)*(33+4*featureDimension d p+m*(25+9*featureDimension d p)) ∧
      t.mem=writeArray s.mem (s.ptrs 56) (List.ofFn (indexedValidationWeights d p k M m ε V v)) ∧
      t.regs 66=∑ i,indexedValidationWeights d p k M m ε V v i ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ q, q ∉ ({3,4,12,25,26,55,57,58,59} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let w := indexedValidationWeights d p k M m ε V v
  let coef := extendFin (fun j => coefficientIsometry d p (v j).val) 0
  let a := extendFin (coefficientFeatures d p V) 0
  let y := extendFin (fun j => (V j).2) false
  have hcoefs (j : ℕ) (hj : j < k) : readArray s.mem (s.ptrs 49+(j : ℤ)*featureDimension d p) (featureDimension d p)=
      List.ofFn (fun i => coef j i) := by simpa [coef,extendFin,hj] using hbank ⟨j,hj⟩
  have hcells (j : Fin m) := encoded_row_coordinates d p (V j).1 (V j).2 s.mem _ (hval j)
  have hfeatures (j : ℕ) (hj : j < m) : readArray s.mem (s.ptrs 51+(j : ℤ)*((featureDimension d p : ℤ)+2))
      (featureDimension d p)=List.ofFn (fun i => a j i) := by
    simpa [a,extendFin,hj,coefficientFeatures] using (hcells ⟨j,hj⟩).1
  have hlabels (j : ℕ) (hj : j < m) : s.mem (s.ptrs 51+(j : ℤ)*((featureDimension d p : ℤ)+2)+featureDimension d p)=label (y j) := by
    simpa [y,extendFin,hj] using (hcells ⟨j,hj⟩).2.1
  obtain ⟨t,cost,he,hcost,ht⟩ := weights_loop_correct ω (featureDimension d p) k M m hMpos coef a y ε w s
    hD hM hm hε hbankEnd hvalEnd hcoefs hfeatures hlabels
    (indexedValidationWeights_regression d p k M m ε V v) hK
    (WeightInvariant.initial _ _ _ w s h25 h26 h55 h57 h66)
  have hc := he.cursors_preserved (by decide)
  refine ⟨t,cost,he,hcost,?_,?_,hc.1,hc.2,ht.fixedPointers⟩
  · have htake : (List.ofFn w).take (k*M)=List.ofFn w := by simpa using List.take_length (List.ofFn w)
    simpa only [htake] using ht.memory
  · simpa only [weightPrefix_total] using ht.total
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMSelectionInit
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def exponentialClampCommand : Cmd := .cond (.real 0) (.atom (.literal 0 0)) .skip
lemma exponential_clamp_correct (ω : PolySampIso.Streams) (s : Store) :
    ∃ t, Eval ω exponentialClampCommand s t 2 ∧
      t={s with regs := Function.update s.regs 0 (max 0 (s.regs 0))} := by
  by_cases h : s.regs 0 ≤ 0
  · refine ⟨_,Eval.cond_yes (test := .real 0) (no := .skip) h (Eval.atom s _),?_⟩
    simp [Op.act,max_eq_left h]
  · refine ⟨s,Eval.cond_no (test := .real 0) (yes := .atom (.literal 0 0)) h (Eval.skip s),?_⟩
    have he : max 0 (s.regs 0)=s.regs 0 := max_eq_right (by linarith)
    simp [he]
def selectionInitTail : List Op := [.literal 1 0,.sub 0 1 0,.exp 72 0,.mul 72 72 66,
  .literal 74 0,.literal 73 0,.pset 25 1,.pset 26 1,.pcopy 55 49,.pcopy 57 56,.pcopy 60 49,.pset 27 0]
def selectionInitCommand : Cmd := .seq (.atom (.expo 0)) (.seq exponentialClampCommand (.block selectionInitTail))
lemma selection_init_correct (ω : PolySampIso.Streams) (s : Store) :
    ∃ t, Eval ω selectionInitCommand s t 15 ∧
      t.regs 72=exponentialUniform (ω.2 s.ec)*s.regs 66 ∧ t.regs 73=0 ∧ t.regs 74=0 ∧
      t.ptrs 25=1 ∧ t.ptrs 26=1 ∧ t.ptrs 27=0 ∧ t.ptrs 55=s.ptrs 49 ∧
      t.ptrs 57=s.ptrs 56 ∧ t.ptrs 60=s.ptrs 49 ∧ t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec+1 ∧
      (∀ r, r ∉ ({0,1,72,73,74} : Finset ℕ) → t.regs r=s.regs r) ∧
      (∀ q, q ∉ ({25,26,27,55,57,60} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := Op.act ω s (.expo 0)
  have hu : Eval ω (.atom (.expo 0)) s u 1 := Eval.atom s _
  obtain ⟨v,hv,hveq⟩ := exponential_clamp_correct ω u
  let t := blockAct ω selectionInitTail v
  have ht : Eval ω (.block selectionInitTail) v t 12 := eval_block ω _ v
  have hall : Eval ω selectionInitCommand s t 15 := by convert! Eval.seq hu (Eval.seq hv ht) using 1 <;> omega
  refine ⟨t,hall,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [t,blockAct,selectionInitTail,Op.act,hveq,u,exponentialUniform]
  · simp [t,blockAct,selectionInitTail,Op.act]
  · simp [t,blockAct,selectionInitTail,Op.act]
  · simp [t,blockAct,selectionInitTail,Op.act]
  · simp [t,blockAct,selectionInitTail,Op.act]
  · simp [t,blockAct,selectionInitTail,Op.act]
  · simp [t,blockAct,selectionInitTail,Op.act,hveq,u]
  · simp [t,blockAct,selectionInitTail,Op.act,hveq,u]
  · simp [t,blockAct,selectionInitTail,Op.act,hveq,u]
  · simp [t,blockAct,selectionInitTail,Op.act,hveq,u]
  · simp [t,blockAct,selectionInitTail,Op.act,hveq,u]
  · simp [t,blockAct,selectionInitTail,Op.act,hveq,u]
  · intro r hr
    apply hall.register_preserved
    simp [selectionInitCommand,exponentialClampCommand,selectionInitTail,Cmd.block,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [selectionInitCommand,exponentialClampCommand,selectionInitTail,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMSelectionMaybe
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
attribute [local instance] Classical.propDecidable
def chooseSelection : List Op := [.pcopy 60 55,.pcopy 27 26,.pdec 27,.literal 73 1]
def selectionMaybeCommand : Cmd := .cond (.real 73) (.cond (.real 0) .skip (.block chooseSelection)) .skip
lemma selection_maybe_correct (ω : PolySampIso.Streams) (found : Prop) (target cumulative : ℝ) (s : Store)
    (hflag : s.regs 73=if found then (1 : ℝ) else 0) (h0 : s.regs 0=cumulative-target) :
    ∃ t cost, Eval ω selectionMaybeCommand s t cost ∧ cost ≤ 7 ∧
      t.regs 73=(if found ∨ target < cumulative then (1 : ℝ) else 0) ∧
      t.ptrs 60=(if ¬found ∧ target < cumulative then s.ptrs 55 else s.ptrs 60) ∧
      t.ptrs 27=(if ¬found ∧ target < cumulative then s.ptrs 26-1 else s.ptrs 27) ∧
      t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ r, r ≠ 73 → t.regs r=s.regs r) ∧
      (∀ q, q ≠ 27 → q ≠ 60 → t.ptrs q=s.ptrs q) := by
  classical
  have hh : ∃ t cost, Eval ω selectionMaybeCommand s t cost ∧ cost ≤ 7 ∧
      t.regs 73=(if found ∨ target < cumulative then (1 : ℝ) else 0) ∧
      t.ptrs 60=(if ¬found ∧ target < cumulative then s.ptrs 55 else s.ptrs 60) ∧
      t.ptrs 27=(if ¬found ∧ target < cumulative then s.ptrs 26-1 else s.ptrs 27) := by
    by_cases hf : found
    · refine ⟨s,2,Eval.cond_no (test := .real 73) (yes := .cond (.real 0) .skip (.block chooseSelection)) ?_ (Eval.skip s),by omega,?_,?_,?_⟩
      · change ¬s.regs 73 ≤ 0
        simp [hflag,hf]
      · simp [hflag,hf]
      · simp [hf]
      · simp [hf]
    · by_cases hq : target < cumulative
      · let t := blockAct ω chooseSelection s
        have ht : Eval ω (.block chooseSelection) s t 4 := eval_block ω _ s
        refine ⟨t,7,Eval.cond_yes (test := .real 73) (no := .skip) ?_
          (Eval.cond_no (test := .real 0) (yes := .skip) ?_ ht),by omega,?_,?_,?_⟩
        · change s.regs 73 ≤ 0
          simp [hflag,hf]
        · change ¬s.regs 0 ≤ 0
          rw [h0]
          linarith
        · simp [t,blockAct,chooseSelection,Op.act,hf,hq]
        · simp [t,blockAct,chooseSelection,Op.act,hf,hq]
        · simp [t,blockAct,chooseSelection,Op.act,hf,hq]
      · refine ⟨s,2,Eval.cond_yes (test := .real 73) (no := .skip) ?_
          (Eval.cond_yes (test := .real 0) (no := .block chooseSelection) ?_ (Eval.skip s)),by omega,?_,?_,?_⟩
        · change s.regs 73 ≤ 0
          simp [hflag,hf]
        · change s.regs 0 ≤ 0
          rw [h0]
          linarith
        · simp [hflag,hf,hq]
        · simp [hf,hq]
        · simp [hf,hq]
  obtain ⟨t,cost,he,hcost,h73,h60,h27⟩ := hh
  have hc := he.cursors_preserved (by decide)
  refine ⟨t,cost,he,hcost,h73,h60,h27,he.memory_preserved (by decide),hc.1,hc.2,?_,?_⟩
  · intro r hr
    exact he.register_preserved (by simp [selectionMaybeCommand,chooseSelection,Cmd.block,Cmd.registers,Op.registers,hr])
  · intro q hq27 hq60
    exact he.pointer_preserved (by simp [selectionMaybeCommand,chooseSelection,Cmd.block,Cmd.pointers,Op.pointers,hq27,hq60])
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMSelectionBody
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
attribute [local instance] Classical.propDecidable
def selectionScanPrefix : List Op := [.load 0 57,.add 74 74 0,.sub 0 74 72]
def selectionScanTail : List Op := [.pinc 57,.pinc 26]
def selectionBodyCommand : Cmd := .seq (.block selectionScanPrefix) (.seq selectionMaybeCommand
  (.seq (.block selectionScanTail) candidateCarryCommand))
lemma selection_body_correct (ω : PolySampIso.Streams) (D M r : ℕ) (hMpos : 0 < M) (B : ℤ)
    (found : Prop) (target cumulative weight : ℝ) (s : Store)
    (hD : s.ptrs 15=D) (hM : s.ptrs 2=M) (hl : s.ptrs 26=((r%M : ℕ) : ℤ)+1)
    (hB : s.ptrs 55=B+((r/M : ℕ) : ℤ)*D) (hflag : s.regs 73=if found then (1 : ℝ) else 0)
    (htarget : s.regs 72=target) (hcum : s.regs 74=cumulative) (hweight : s.mem (s.ptrs 57)=weight) :
    ∃ t cost, Eval ω selectionBodyCommand s t cost ∧ cost ≤ 19+4*D ∧
      t.regs 74=cumulative+weight ∧ t.regs 73=(if found ∨ target < cumulative+weight then (1 : ℝ) else 0) ∧
      t.ptrs 60=(if ¬found ∧ target < cumulative+weight then s.ptrs 55 else s.ptrs 60) ∧
      t.ptrs 27=(if ¬found ∧ target < cumulative+weight then s.ptrs 26-1 else s.ptrs 27) ∧
      t.ptrs 57=s.ptrs 57+1 ∧ t.ptrs 26=(((r+1)%M : ℕ) : ℤ)+1 ∧
      t.ptrs 55=B+(((r+1)/M : ℕ) : ℤ)*D ∧ t.ptrs 25=s.ptrs 25+1 ∧
      t.mem=s.mem ∧ t.gc=s.gc ∧ t.ec=s.ec ∧
      (∀ j, j ∉ ({0,73,74} : Finset ℕ) → t.regs j=s.regs j) ∧
      (∀ q, q ∉ ({12,25,26,27,55,57,60} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := blockAct ω selectionScanPrefix s
  have hu : Eval ω (.block selectionScanPrefix) s u 3 := eval_block ω _ s
  have u0 : u.regs 0=cumulative+weight-target := by simp [u,blockAct,selectionScanPrefix,Op.act,htarget,hcum,hweight]
  have u73 : u.regs 73=if found then (1 : ℝ) else 0 := hflag
  have u74 : u.regs 74=cumulative+weight := by simp [u,blockAct,selectionScanPrefix,Op.act,hcum,hweight]
  obtain ⟨v,cv,hv,hcv,hv73,hv60,hv27,hvm,hvgc,hvec,hvr,hvp⟩ := selection_maybe_correct ω found target (cumulative+weight) u u73 u0
  let a := blockAct ω selectionScanTail v
  have ha : Eval ω (.block selectionScanTail) v a 2 := eval_block ω _ v
  have ap (q : ℕ) (hq26 : q ≠ 26) (hq57 : q ≠ 57) : a.ptrs q=v.ptrs q := by simp [a,blockAct,selectionScanTail,Op.act,hq26,hq57]
  have a26 : a.ptrs 26=((r%M : ℕ) : ℤ)+2 := by
    simp [a,blockAct,selectionScanTail,Op.act,hvp 26 (by omega) (by omega),u,blockAct,selectionScanPrefix,hl]
    ring
  have a15 : a.ptrs 15=D := by rw [ap 15 (by omega) (by omega),hvp 15 (by omega) (by omega)]; exact hD
  have a2 : a.ptrs 2=M := by rw [ap 2 (by omega) (by omega),hvp 2 (by omega) (by omega)]; exact hM
  obtain ⟨t,ct,ht,hct,ht26,ht55,ht25,htm,htr,htgc,htec,htp⟩ := candidate_carry_correct ω D M (r%M) a a15 a2 a26
  have hall : Eval ω selectionBodyCommand s t (3+cv+2+ct) := by
    convert! Eval.seq hu (Eval.seq hv (Eval.seq ha ht)) using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  obtain ⟨hmod,hdiv⟩ := grid_counter_succ M r hMpos
  refine ⟨t,_,hall,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,hc.1,hc.2,?_,?_⟩
  · rw [htr]
    exact (hvr 74 (by omega)).trans u74
  · rw [htr]
    exact hv73
  · rw [htp 60 (by decide),ap 60 (by omega) (by omega)]
    exact hv60
  · rw [htp 27 (by decide),ap 27 (by omega) (by omega)]
    exact hv27
  · rw [htp 57 (by decide)]
    change v.ptrs 57+1=s.ptrs 57+1
    rw [hvp 57 (by omega) (by omega)]
    rfl
  · rw [ht26,hmod]
    split_ifs <;> push_cast <;> omega
  · rw [ht55,ap 55 (by omega) (by omega),hvp 55 (by omega) (by omega)]
    change s.ptrs 55+_= _
    rw [hB,hdiv]
    split_ifs <;> push_cast <;> ring
  · rw [ht25,ap 25 (by omega) (by omega),hvp 25 (by omega) (by omega)]
    rfl
  · exact htm.trans hvm
  · intro j hj
    rw [htr]
    change v.regs j=s.regs j
    rw [hvr j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj; tauto)]
    apply hu.register_preserved
    simp [Cmd.block,selectionScanPrefix,Cmd.registers,Op.registers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    tauto
  · intro q hq
    apply hall.pointer_preserved
    simp [selectionBodyCommand,selectionScanPrefix,selectionScanTail,selectionMaybeCommand,chooseSelection,
      candidateCarryCommand,advanceCommand,advanceLoop,advanceStep,Cmd.block,Cmd.pointers,Op.pointers]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
    tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.PrefixWeightChoice
open Finset
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def prefixWeightChoices {K : ℕ} (w : Fin K → ℝ) (u : ℝ) (r : ℕ) : Finset (Fin K) :=
  (weightChoices w u).filter (fun i => i.val < r)
noncomputable def prefixWeightPick {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (u : ℝ) (r : ℕ) : Fin K :=
  if h : (prefixWeightChoices w u r).Nonempty then (prefixWeightChoices w u r).min' h else ⟨0,hK⟩
@[simp] lemma prefixWeightChoices_zero {K : ℕ} (w : Fin K → ℝ) (u : ℝ) : prefixWeightChoices w u 0=∅ := by
  simp [prefixWeightChoices]
@[simp] lemma prefixWeightPick_zero {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (u : ℝ) :
    prefixWeightPick hK w u 0=⟨0,hK⟩ := by simp [prefixWeightPick]
lemma prefixWeightChoices_next {K : ℕ} (w : Fin K → ℝ) (u : ℝ) (r : ℕ) (hr : r < K) :
    prefixWeightChoices w u (r+1)=
      if u < weightPrefix w (r+1) then insert ⟨r,hr⟩ (prefixWeightChoices w u r) else prefixWeightChoices w u r := by
  classical
  ext i
  by_cases h : u < weightPrefix w (r+1)
  · simp only [h,if_true,prefixWeightChoices,mem_filter,weightChoices,mem_univ,true_and,mem_insert]
    have he : i=⟨r,hr⟩ ↔ i.val=r := Fin.ext_iff
    rw [he]
    by_cases hi : i.val=r
    · simp [hi,h]
    · have hh : i.val < r+1 ↔ i.val < r := by omega
      rw [hh]
      tauto
  · simp only [h,if_false,prefixWeightChoices,mem_filter,weightChoices,mem_univ,true_and]
    by_cases hi : i.val=r
    · simp [hi,h]
    · have hh : i.val < r+1 ↔ i.val < r := by omega
      rw [hh]
lemma prefixWeightChoices_nonempty_next {K : ℕ} (w : Fin K → ℝ) (u : ℝ) (r : ℕ) (hr : r < K) :
    (prefixWeightChoices w u (r+1)).Nonempty ↔
      (prefixWeightChoices w u r).Nonempty ∨ u < weightPrefix w (r+1) := by
  rw [prefixWeightChoices_next w u r hr]
  split_ifs <;> simp_all
lemma prefixWeightPick_next {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (u : ℝ) (r : ℕ) (hr : r < K) :
    prefixWeightPick hK w u (r+1)=
      if (prefixWeightChoices w u r).Nonempty then prefixWeightPick hK w u r
      else if u < weightPrefix w (r+1) then ⟨r,hr⟩ else ⟨0,hK⟩ := by
  classical
  by_cases hold : (prefixWeightChoices w u r).Nonempty
  · rw [if_pos hold]
    by_cases h : u < weightPrefix w (r+1)
    · have hmin : (prefixWeightChoices w u r).min' hold ≤ (⟨r,hr⟩ : Fin K) := by
        have hh := Finset.min'_mem (prefixWeightChoices w u r) hold
        have hi : ((prefixWeightChoices w u r).min' hold).val < r := (Finset.mem_filter.mp hh).2
        change ((prefixWeightChoices w u r).min' hold).val ≤ r
        omega
      simp only [prefixWeightPick,prefixWeightChoices_next w u r hr,if_pos h,if_pos hold]
      rw [dif_pos (Finset.insert_nonempty _ _),Finset.min'_insert _ _ hold,min_eq_right hmin,dif_pos hold]
    · simp only [prefixWeightPick,prefixWeightChoices_next w u r hr,if_neg h,dif_pos hold]
  · rw [if_neg hold]
    have he : prefixWeightChoices w u r=∅ := Finset.not_nonempty_iff_eq_empty.mp hold
    by_cases h : u < weightPrefix w (r+1)
    · simp [prefixWeightPick,prefixWeightChoices_next w u r hr,h,he]
    · simp [prefixWeightPick,prefixWeightChoices_next w u r hr,h,he]
lemma prefixWeightPick_total {K : ℕ} (hK : 0 < K) (w : Fin K → ℝ) (u : ℝ) :
    prefixWeightPick hK w u K=pickWeight hK w u := by
  have he : prefixWeightChoices w u K=weightChoices w u := by simp [prefixWeightChoices]
  simp only [prefixWeightPick,pickWeight,he]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RAMSelectionInvariant
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
attribute [local instance] Classical.propDecidable
structure SelectionInvariant (D k M : ℕ) (hK : 0 < k*M) (w : Fin (k*M) → ℝ) (target : ℝ)
    (s₀ : Store) (r : ℕ) (s : Store) : Prop where
  fixedPointers : ∀ q, q ∉ ({12,25,26,27,55,57,60} : Finset ℕ) → s.ptrs q=s₀.ptrs q
  targetValue : s.regs 72=target
  cumulative : s.regs 74=weightPrefix w r
  foundFlag : s.regs 73=if (prefixWeightChoices w target r).Nonempty then (1 : ℝ) else 0
  counter : s.ptrs 25=(r : ℤ)+1
  thresholdCounter : s.ptrs 26=((r%M : ℕ) : ℤ)+1
  coefficientCursor : s.ptrs 55=s₀.ptrs 49+((r/M : ℕ) : ℤ)*D
  weightCursor : s.ptrs 57=s₀.ptrs 56+(r : ℤ)
  selectedPointer : s.ptrs 60=s₀.ptrs 49+(((prefixWeightPick hK w target r).val/M : ℕ) : ℤ)*D
  selectedThreshold : s.ptrs 27=(((prefixWeightPick hK w target r).val%M : ℕ) : ℤ)
  memory : s.mem=s₀.mem
lemma selection_invariant_step (ω : PolySampIso.Streams) (D k M : ℕ) (hK : 0 < k*M) (hMpos : 0 < M)
    (w : Fin (k*M) → ℝ) (target : ℝ) (s₀ : Store) (hD : s₀.ptrs 15=D) (hM : s₀.ptrs 2=M)
    (hw : ∀ i : Fin (k*M), s₀.mem (s₀.ptrs 56+(i.val : ℤ))=w i)
    (r : ℕ) (hr : r < k*M) (s : Store) (hs : SelectionInvariant D k M hK w target s₀ r s) :
    ∃ t cost, Eval ω selectionBodyCommand s t cost ∧ cost ≤ 19+4*D ∧
      SelectionInvariant D k M hK w target s₀ (r+1) t := by
  have hcell : s.mem (s.ptrs 57)=w ⟨r,hr⟩ := by rw [hs.memory,hs.weightCursor]; exact hw ⟨r,hr⟩
  obtain ⟨t,cost,he,hcost,h74,h73,h60,h27,h57,h26,h55,h25,htm,htgc,htec,htr,htp⟩ := selection_body_correct ω D M r hMpos
    (s₀.ptrs 49) ((prefixWeightChoices w target r).Nonempty) target (weightPrefix w r) (w ⟨r,hr⟩) s
    ((hs.fixedPointers 15 (by decide)).trans hD) ((hs.fixedPointers 2 (by decide)).trans hM)
    hs.thresholdCounter hs.coefficientCursor
    (by by_cases hh : (prefixWeightChoices w target r).Nonempty <;> simpa [hh] using hs.foundFlag)
    hs.targetValue hs.cumulative hcell
  have hsucc : weightPrefix w r+w ⟨r,hr⟩=weightPrefix w (r+1) := (weightPrefix_succ w ⟨r,hr⟩).symm
  rw [hsucc] at h74 h73 h60 h27
  refine ⟨t,cost,he,hcost,?_⟩
  constructor
  · intro q hq
    exact (htp q hq).trans (hs.fixedPointers q hq)
  · exact (htr 72 (by decide)).trans hs.targetValue
  · exact h74
  · by_cases ho : (prefixWeightChoices w target r).Nonempty <;>
      by_cases hn : target < weightPrefix w (r+1) <;>
      simpa [prefixWeightChoices_nonempty_next w target r hr,ho,hn] using h73
  · rw [h25,hs.counter]
    push_cast
    ring
  · exact h26
  · exact h55
  · rw [h57,hs.weightCursor]
    push_cast
    ring
  · rw [h60,hs.selectedPointer,hs.coefficientCursor,prefixWeightPick_next hK w target r hr]
    by_cases ho : (prefixWeightChoices w target r).Nonempty <;>
      by_cases hn : target < weightPrefix w (r+1) <;> simp [ho,hn,prefixWeightPick]
  · rw [h27,hs.selectedThreshold,hs.thresholdCounter,prefixWeightPick_next hK w target r hr]
    by_cases ho : (prefixWeightChoices w target r).Nonempty <;>
      by_cases hn : target < weightPrefix w (r+1) <;> simp [ho,hn,prefixWeightPick]
  · exact htm.trans hs.memory
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMSelectionLoop
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma SelectionInvariant.initial (D k M : ℕ) (hK : 0 < k*M) (w : Fin (k*M) → ℝ) (target : ℝ) (s : Store)
    (h25 : s.ptrs 25=1) (h26 : s.ptrs 26=1) (h55 : s.ptrs 55=s.ptrs 49)
    (h57 : s.ptrs 57=s.ptrs 56) (h60 : s.ptrs 60=s.ptrs 49) (h27 : s.ptrs 27=0)
    (h72 : s.regs 72=target) (h73 : s.regs 73=0) (h74 : s.regs 74=0) :
    SelectionInvariant D k M hK w target s 0 s := by
  constructor <;> simp_all

def selectionLoop : Cmd := .loop (.pointer 25 24) selectionBodyCommand
lemma selection_loop_correct (ω : PolySampIso.Streams) (D k M : ℕ) (hKpos : 0 < k*M) (hMpos : 0 < M)
    (w : Fin (k*M) → ℝ) (target : ℝ) (s : Store) (hD : s.ptrs 15=D) (hM : s.ptrs 2=M) (hK : s.ptrs 24=k*M)
    (hw : ∀ i : Fin (k*M), s.mem (s.ptrs 56+(i.val : ℤ))=w i)
    (hinit : SelectionInvariant D k M hKpos w target s 0 s) :
    ∃ t cost, Eval ω selectionLoop s t cost ∧ cost ≤ 2+(k*M)*(21+4*D) ∧
      SelectionInvariant D k M hKpos w target s (k*M) t ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  have htrue : ∀ r, r < k*M → ∀ u, SelectionInvariant D k M hKpos w target s r u → Test.holds u (.pointer 25 24) := by
    intro r hr u hu
    change u.ptrs 25 ≤ u.ptrs 24
    rw [hu.counter,hu.fixedPointers 24 (by decide),hK]
    omega
  have hfalse : ∀ u, SelectionInvariant D k M hKpos w target s (k*M) u → ¬Test.holds u (.pointer 25 24) := by
    intro u hu
    change ¬u.ptrs 25 ≤ u.ptrs 24
    rw [hu.counter,hu.fixedPointers 24 (by decide),hK]
    omega
  have hbody : ∀ r, r < k*M → ∀ u, SelectionInvariant D k M hKpos w target s r u →
      ∃ t cost, cost ≤ 19+4*D ∧ Eval ω selectionBodyCommand u t cost ∧
        SelectionInvariant D k M hKpos w target s (r+1) t := by
    intro r hr u hu
    obtain ⟨t,cost,he,hcost,ht⟩ := selection_invariant_step ω D k M hKpos hMpos w target s hD hM hw r hr u hu
    exact ⟨t,cost,hcost,he,ht⟩
  obtain ⟨t,cost,hcost,he,ht⟩ := eval_loop_invariant ω (.pointer 25 24) selectionBodyCommand (k*M)
    (19+4*D) (SelectionInvariant D k M hKpos w target s) htrue hfalse hbody s hinit
  have hc := he.cursors_preserved (by decide)
  refine ⟨t,cost,he,?_,ht,hc.1,hc.2⟩
  convert! hcost using 1 <;> ring
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMReverseCopy
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
noncomputable def writeReverse (mem : ℤ → ℝ) (base : ℤ) : List ℝ → ℤ → ℝ
  | [] => mem
  | x::xs => Function.update (writeReverse mem (base-1) xs) base x
lemma writeReverse_at (mem : ℤ → ℝ) (base : ℤ) (xs : List ℝ) (i : ℕ) (hi : i<xs.length) :
    writeReverse mem base xs (base-i)=xs[i] := by
  induction xs generalizing base i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [writeReverse]
    | succ i =>
      rw [writeReverse,Function.update_of_ne (by omega : base-((i+1 : ℕ) : ℤ) ≠ base)]
      rw [show base-((i+1 : ℕ) : ℤ)=(base-1)-(i : ℤ) by omega,ih (base-1) i (by simpa using hi)]
      rfl
lemma writeReverse_update_before (mem : ℤ → ℝ) (base z : ℤ) (xs : List ℝ) (a : ℝ) (hz : base<z) :
    writeReverse (Function.update mem z a) base xs=Function.update (writeReverse mem base xs) z a := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih =>
    rw [writeReverse,ih (base-1) (by omega),writeReverse]
    exact Function.update_comm (by omega : z≠base) a x (writeReverse mem (base-1) xs)
lemma writeReverse_cons_sequential (mem : ℤ → ℝ) (base : ℤ) (a : ℝ) (xs : List ℝ) :
    writeReverse (Function.update mem base a) (base-1) xs=writeReverse mem base (a::xs) := by
  rw [writeReverse_update_before mem (base-1) base xs a (by omega)]
  rfl
def reverseCopyStep : List Op := [.load 0 3,.store 5 0,.pinc 3,.pdec 5,.pinc 12]
def reverseCopyLoop : Cmd := .loop (.pointer 12 15) (.block reverseCopyStep)
def reverseCopyCommand : Cmd := .seq (.atom (.pset 12 1)) reverseCopyLoop
lemma reverse_copy_loop_correct (ω : PolySampIso.Streams) (xs : List ℝ) (s : Store)
    (hbound : s.ptrs 12+(xs.length : ℤ)=s.ptrs 15+1)
    (hx : readArray s.mem (s.ptrs 3) xs.length=xs) (hsrc : 0 ≤ s.ptrs 3) (hdst : s.ptrs 5<0) :
    ∃ t, Eval ω reverseCopyLoop s t (2+7*xs.length) ∧
      t.mem=writeReverse s.mem (s.ptrs 5) xs ∧ t.ptrs 3=s.ptrs 3+xs.length ∧ t.ptrs 5=s.ptrs 5-xs.length := by
  induction xs generalizing s with
  | nil =>
    refine ⟨s,Eval.loop_done ?_,rfl,by simp,by simp⟩
    change ¬s.ptrs 12 ≤ s.ptrs 15
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hbound
    omega
  | cons x xs ih =>
    have hread : s.mem (s.ptrs 3)=x ∧ readArray s.mem (s.ptrs 3+1) xs.length=xs := by
      simpa only [List.length_cons,readArray_cons,List.cons.injEq] using hx
    have htest : Test.holds s (.pointer 12 15) := by
      change s.ptrs 12 ≤ s.ptrs 15
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound
      omega
    let u := blockAct ω reverseCopyStep s
    have hu : Eval ω (.block reverseCopyStep) s u 5 := eval_block ω _ s
    have um : u.mem=Function.update s.mem (s.ptrs 5) x := by simp [u,blockAct,reverseCopyStep,Op.act,hread.1]
    have up : u.ptrs=Function.update (Function.update (Function.update s.ptrs 3 (s.ptrs 3+1)) 5 (s.ptrs 5-1)) 12 (s.ptrs 12+1) := by
      simp [u,blockAct,reverseCopyStep,Op.act]
    obtain ⟨t,ht,hm,h3,h5⟩ := ih u
      (by simp only [up,Function.update_apply]; norm_num; simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbound; omega)
      (by simp only [um,up,Function.update_apply]; norm_num; rw [readArray_update_before _ _ _ _ _ (by omega)]; exact hread.2)
      (by simp only [up,Function.update_apply]; norm_num; omega) (by simp only [up,Function.update_apply]; norm_num; omega)
    refine ⟨t,?_,?_,?_,?_⟩
    · convert! Eval.loop_step htest hu ht using 1 <;> simp only [List.length_cons] <;> omega
    · rw [hm,um,up]
      norm_num
      exact writeReverse_cons_sequential _ _ _ _
    · rw [h3,up]
      norm_num
      omega
    · rw [h5,up]
      norm_num
      omega
lemma reverse_copy_command_correct (ω : PolySampIso.Streams) (xs : List ℝ) (s : Store)
    (hn : s.ptrs 15=xs.length) (hx : readArray s.mem (s.ptrs 3) xs.length=xs)
    (hsrc : 0 ≤ s.ptrs 3) (hdst : s.ptrs 5<0) :
    ∃ t, Eval ω reverseCopyCommand s t (3+7*xs.length) ∧
      t.mem=writeReverse s.mem (s.ptrs 5) xs ∧ t.ptrs 3=s.ptrs 3+xs.length ∧ t.ptrs 5=s.ptrs 5-xs.length ∧
      t.gc=s.gc ∧ t.ec=s.ec ∧ (∀ q, q ∉ ({3,5,12} : Finset ℕ) → t.ptrs q=s.ptrs q) := by
  let u := Op.act ω s (.pset 12 1)
  have hu : Eval ω (.atom (.pset 12 1)) s u 1 := Eval.atom s _
  obtain ⟨t,ht,hm,h3,h5⟩ := reverse_copy_loop_correct ω xs u
    (by simp [u,Op.act,hn,add_comm]) (by simpa [u,Op.act] using hx) (by simpa [u,Op.act] using hsrc) (by simpa [u,Op.act] using hdst)
  have hall : Eval ω reverseCopyCommand s t (3+7*xs.length) := by convert! Eval.seq hu ht using 1 <;> omega
  have hc := hall.cursors_preserved (by decide)
  refine ⟨t,hall,by simpa [u,Op.act] using hm,by simpa [u,Op.act] using h3,by simpa [u,Op.act] using h5,hc.1,hc.2,?_⟩
  intro q hq
  apply hall.pointer_preserved
  simp [reverseCopyCommand,reverseCopyLoop,reverseCopyStep,Cmd.block,Cmd.pointers,Op.pointers]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hq
  tauto
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMOutput
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma rawOutput_of_vector_cells (d p : ℕ) (v : Vec (featureDimension d p)) (l : ℕ) (r : ℕ → ℝ)
    (hv : ∀ i : Fin (featureDimension d p), r i.val=v i) (hl : r (featureDimension d p)=l) :
    rawOutput d p r=((coefficientIsometry d p).symm v,l) := by
  have hcard := ((lemma_B_8 d).2.2.2 p).2.1
  apply Prod.ext
  · apply PiLp.ext
    intro κ
    change r (indexRank κ)=_
    rw [coefficientIsometry_symm_coordinate]
    exact hv (coefficientIndexEquiv d p κ)
  · simp [rawOutput,hcard,hl,address]
def outputPrefix : List Op := [.pcopy 3 55,.pset 5 (-1)]
def outputTail : List Op := [.pointerReal 0 27,.store 5 0]
def outputCommand : Cmd := .seq (.block outputPrefix) (.seq reverseCopyCommand (.block outputTail))
lemma output_command_correct (ω : PolySampIso.Streams) (d p l : ℕ) (v : Vec (featureDimension d p)) (s : Store)
    (hD : s.ptrs 15=featureDimension d p) (hl : s.ptrs 27=l) (hsrc : 0 ≤ s.ptrs 55)
    (hv : readArray s.mem (s.ptrs 55) (featureDimension d p)=List.ofFn (fun i => v i)) :
    ∃ t, Eval ω outputCommand s t (7+7*featureDimension d p) ∧
      rawOutput d p (fun i => t.mem (-1-(i : ℤ)))=((coefficientIsometry d p).symm v,l) ∧
      t.mem (-1-(featureDimension d p : ℤ))=(l : ℝ) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  let u := blockAct ω outputPrefix s
  have hu : Eval ω (.block outputPrefix) s u 2 := eval_block ω _ s
  have um : u.mem=s.mem := rfl
  have u3 : u.ptrs 3=s.ptrs 55 := by simp [u,blockAct,outputPrefix,Op.act]
  have u5 : u.ptrs 5= -1 := by simp [u,blockAct,outputPrefix,Op.act]
  obtain ⟨w,hw,hwm,hw3,hw5,hwgc,hwec,hwp⟩ := reverse_copy_command_correct ω (List.ofFn (fun i => v i)) u
    (by simpa [u,blockAct,outputPrefix,Op.act] using hD)
    (by simpa only [um,u3,List.length_ofFn] using hv) (by rwa [u3]) (by rw [u5]; norm_num)
  have w5 : w.ptrs 5= -1-(featureDimension d p : ℤ) := by simpa only [u5,List.length_ofFn] using hw5
  have w27 : w.ptrs 27=l := by rw [hwp 27 (by decide)]; simpa [u,blockAct,outputPrefix,Op.act] using hl
  let t := blockAct ω outputTail w
  have ht : Eval ω (.block outputTail) w t 2 := eval_block ω _ w
  have tm : t.mem=Function.update (writeReverse s.mem (-1) (List.ofFn (fun i => v i)))
      (-1-(featureDimension d p : ℤ)) (l : ℝ) := by
    simp [t,blockAct,outputTail,Op.act,hwm,um,u5,w5,w27]
  have hall : Eval ω outputCommand s t (7+7*featureDimension d p) := by
    convert! Eval.seq hu (Eval.seq hw ht) using 1 <;> simp only [List.length_ofFn] <;> omega
  have hc := hall.cursors_preserved (by decide)
  have tl : t.mem (-1-(featureDimension d p : ℤ))=(l : ℝ) := by simp [tm]
  refine ⟨t,hall,?_,tl,hc.1,hc.2⟩
  apply rawOutput_of_vector_cells d p v l _ ?_ tl
  intro i
  rw [tm,Function.update_of_ne (by have hi := i.isLt; omega)]
  rw [writeReverse_at _ (-1) (List.ofFn (fun i => v i)) i.val (by simpa using i.isLt)]
  simp
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMSelectOutput
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open scoped BigOperators
def selectOutputCommand : Cmd := .seq selectionInitCommand (.seq selectionLoop
  (.seq (.atom (.pcopy 55 60)) outputCommand))
lemma select_output_correct (ω : PolySampIso.Streams) (d p k M : ℕ) (hKpos : 0 < k*M) (hMpos : 0 < M)
    (w : Fin (k*M) → ℝ) (v : Fin k → UnitBall d p) (s : Store)
    (hD : s.ptrs 15=featureDimension d p) (hM : s.ptrs 2=M) (hK : s.ptrs 24=k*M)
    (hZ : s.regs 66=∑ i,w i) (hec : s.ec=0) (hbase : 0 ≤ s.ptrs 49)
    (hw : ∀ i : Fin (k*M), s.mem (s.ptrs 56+(i.val : ℤ))=w i)
    (hbank : ∀ j : Fin k, readArray s.mem (s.ptrs 49+(j.val : ℤ)*featureDimension d p) (featureDimension d p)=
      List.ofFn (fun i => coefficientIsometry d p (v j).val i)) :
    let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
    let idx := weightedPick hKpos w (ω.2 0)
    ∃ t cost, Eval ω selectOutputCommand s t cost ∧ cost ≤ 25+7*featureDimension d p+(k*M)*(21+4*featureDimension d p) ∧
      rawOutput d p (fun i => t.mem (-1-(i : ℤ)))=((v (e idx).1).val,(e idx).2.val) ∧
      t.mem (-1-(featureDimension d p : ℤ))=((e idx).2.val : ℝ) := by
  dsimp only
  let e : Fin (k*M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  let idx := weightedPick hKpos w (ω.2 0)
  let target := exponentialUniform (ω.2 0)*(∑ i,w i)
  obtain ⟨u,hu,hu72,hu73,hu74,hu25,hu26,hu27,hu55,hu57,hu60,hum,hugc,huec,hur,hup⟩ := selection_init_correct ω s
  have u72 : u.regs 72=target := by simpa only [hec,hZ] using hu72
  have up (q : ℕ) (hq : q ∉ ({25,26,27,55,57,60} : Finset ℕ)) : u.ptrs q=s.ptrs q := hup q hq
  have hinit : SelectionInvariant (featureDimension d p) k M hKpos w target u 0 u :=
    SelectionInvariant.initial _ _ _ hKpos w target u hu25 hu26
      (by rw [hu55,up 49 (by decide)]) (by rw [hu57,up 56 (by decide)])
      (by rw [hu60,up 49 (by decide)]) hu27 u72 hu73 hu74
  obtain ⟨z,cz,hz,hcz,hzInv,hzgc,hzec⟩ := selection_loop_correct ω (featureDimension d p) k M hKpos hMpos w target u
    ((up 15 (by decide)).trans hD) ((up 2 (by decide)).trans hM) ((up 24 (by decide)).trans hK)
    (fun i => by rw [hum,up 56 (by decide)]; exact hw i) hinit
  have hidx : prefixWeightPick hKpos w target (k*M)=idx := prefixWeightPick_total hKpos w target
  have z60 : z.ptrs 60=s.ptrs 49+((idx.val/M : ℕ) : ℤ)*featureDimension d p := by
    simpa only [hidx,up 49 (by decide)] using hzInv.selectedPointer
  have z27 : z.ptrs 27=((e idx).2.val : ℤ) := by
    have hs : (e idx).2.val=idx.val%M := rfl
    rw [hs]
    simpa only [hidx] using hzInv.selectedThreshold
  have zm : z.mem=s.mem := hzInv.memory.trans hum
  let a := Op.act ω z (.pcopy 55 60)
  have ha : Eval ω (.atom (.pcopy 55 60)) z a 1 := Eval.atom z _
  have a15 : a.ptrs 15=featureDimension d p := by
    change z.ptrs 15=_
    exact (hzInv.fixedPointers 15 (by decide)).trans ((up 15 (by decide)).trans hD)
  have a27 : a.ptrs 27=((e idx).2.val : ℤ) := z27
  have a55 : a.ptrs 55=s.ptrs 49+((e idx).1.val : ℤ)*featureDimension d p := z60
  have aread : readArray a.mem (a.ptrs 55) (featureDimension d p)=
      List.ofFn (fun i => coefficientIsometry d p (v (e idx).1).val i) := by
    change readArray z.mem (z.ptrs 60) _=_
    rw [zm,z60]
    exact hbank (e idx).1
  have abase : 0 ≤ a.ptrs 55 := by rw [a55]; positivity
  obtain ⟨t,ht,hraw,htthreshold,htgc,htec⟩ := output_command_correct ω d p (e idx).2.val
    (coefficientIsometry d p (v (e idx).1).val) a a15 a27 abase aread
  have hall : Eval ω selectOutputCommand s t (15+cz+1+(7+7*featureDimension d p)) := by
    convert! Eval.seq hu (Eval.seq hz (Eval.seq ha ht)) using 1 <;> omega
  refine ⟨t,_,hall,by omega,?_,htthreshold⟩
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hraw
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMValidationPipeline
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def validationCommand : Cmd := .seq validationInitCommand (.seq weightsLoop selectOutputCommand)
lemma validation_command_correct (ω : PolySampIso.Streams) (d p k M m : ℕ) (hKpos : 0 < k*M) (hMpos : 0 < M) (ε : ℝ)
    (V : Fin m → Example d) (v : Fin k → UnitBall d p) (s : Store)
    (hD : s.ptrs 15=featureDimension d p) (hM : s.ptrs 2=M) (hk : s.ptrs 19=k) (hm : s.ptrs 20=m)
    (hε : s.regs 53=ε) (hec : s.ec=0) (hbase : 0 ≤ s.ptrs 49)
    (hbankEnd : s.ptrs 49+(k : ℤ)*featureDimension d p ≤ s.ptrs 13)
    (hvalEnd : s.ptrs 53+(m : ℤ)*((featureDimension d p : ℤ)+2) ≤ s.ptrs 13)
    (hbank : ∀ j : Fin k, readArray s.mem (s.ptrs 49+(j.val : ℤ)*featureDimension d p) (featureDimension d p)=
      List.ofFn (fun i => coefficientIsometry d p (v j).val i))
    (hval : ∀ j : Fin m, readArray s.mem (s.ptrs 53+(j.val : ℤ)*((featureDimension d p : ℤ)+2))
      (featureDimension d p+2)=encodedRow d p (V j).1 (V j).2) :
    ∃ t cost, Eval ω validationCommand s t cost ∧
      cost ≤ 44+7*featureDimension d p+(k*M)*(60+8*featureDimension d p+m*(25+9*featureDimension d p)) ∧
      rawOutput d p (fun i => t.mem (-1-(i : ℤ)))=
        ((validationCoin d p k M m hKpos ε V v (ω.2 0)).1.val,(validationCoin d p k M m hKpos ε V v (ω.2 0)).2.val) ∧
      t.mem (-1-(featureDimension d p : ℤ))=((validationCoin d p k M m hKpos ε V v (ω.2 0)).2.val : ℝ) := by
  let w := indexedValidationWeights d p k M m ε V v
  obtain ⟨u,hu,hu24,hu25,hu26,hu55,hu51,hu56,hu57,hu66,hum,hugc,huec,hur,hup⟩ := validation_init_correct ω k M s hk hM
  have up (q : ℕ) (hq : q ∉ ({24,25,26,51,55,56,57} : Finset ℕ)) : u.ptrs q=s.ptrs q := hup q hq
  have ubankEnd : u.ptrs 49+(k : ℤ)*featureDimension d p ≤ u.ptrs 56 := by rw [up 49 (by decide),hu56]; exact hbankEnd
  have uvalEnd : u.ptrs 51+(m : ℤ)*((featureDimension d p : ℤ)+2) ≤ u.ptrs 56 := by rw [hu51,hu56]; exact hvalEnd
  have ubank (j : Fin k) : readArray u.mem (u.ptrs 49+(j.val : ℤ)*featureDimension d p) (featureDimension d p)=
      List.ofFn (fun i => coefficientIsometry d p (v j).val i) := by rw [hum,up 49 (by decide)]; exact hbank j
  obtain ⟨z,cz,hz,hcz,hzm,hz66,hzgc,hzec,hzp⟩ := weights_from_bank_correct ω d p k M m hMpos ε V v u
    ((up 15 (by decide)).trans hD) ((up 2 (by decide)).trans hM) ((up 20 (by decide)).trans hm) hu24
    ((hur 53 (by decide)).trans hε) hu25 hu26 (by rw [hu55,up 49 (by decide)]) (by rw [hu57,hu56]) hu66
    ubankEnd uvalEnd ubank (fun j => by rw [hum,hu51]; exact hval j)
  have zp (q : ℕ) (hq : q ∉ ({3,4,12,25,26,55,57,58,59} : Finset ℕ)) : z.ptrs q=u.ptrs q := hzp q hq
  have zbank (j : Fin k) : readArray z.mem (z.ptrs 49+(j.val : ℤ)*featureDimension d p) (featureDimension d p)=
      List.ofFn (fun i => coefficientIsometry d p (v j).val i) := by
    rw [hzm,zp 49 (by decide),readArray_write_after _ _ _ _ _ ?_]
    · exact ubank j
    · have hj : (j.val : ℤ)+1 ≤ k := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
      have hmul := mul_le_mul_of_nonneg_right hj (show (0 : ℤ) ≤ featureDimension d p by positivity)
      nlinarith only [hmul,ubankEnd]
  have zw (i : Fin (k*M)) : z.mem (z.ptrs 56+(i.val : ℤ))=w i := by
    rw [hzm,zp 56 (by decide),writeArray_at _ _ _ i.val (by simpa using i.isLt)]
    simp only [List.getElem_ofFn] <;> rfl
  obtain ⟨t,ct,ht,hct,hraw,hthreshold⟩ := select_output_correct ω d p k M hKpos hMpos w v z
    ((zp 15 (by decide)).trans ((up 15 (by decide)).trans hD))
    ((zp 2 (by decide)).trans ((up 2 (by decide)).trans hM)) ((zp 24 (by decide)).trans hu24)
    hz66 (hzec.trans (huec.trans hec)) (by rw [zp 49 (by decide),up 49 (by decide)]; exact hbase) zw zbank
  have hall : Eval ω validationCommand s t (17+6*(k*M)+cz+ct) := by
    convert! Eval.seq hu (Eval.seq hz ht) using 1 <;> omega
  refine ⟨t,_,hall,?_,hraw,hthreshold⟩
  nlinarith only [hcz,hct]
lemma validation_command_cost (K m D : ℕ) (hK : 1 ≤ K) (hm : 1 ≤ m) (hD : 1 ≤ D) :
    44+7*D+K*(60+8*D+m*(25+9*D)) ≤ 1000*K*m*D := by
  have hmD : m ≤ m*D := Nat.le_mul_of_pos_right _ hD
  have hDm : D ≤ m*D := by have := Nat.mul_le_mul_right D hm; simpa using this
  have h1mD : 1 ≤ m*D := hm.trans hmD
  have hb : 60+8*D+m*(25+9*D) ≤ 200*m*D := by nlinarith only [hmD,hDm,h1mD]
  have hmult := Nat.mul_le_mul_left K hb
  have hQ : 1 ≤ K*(m*D) := by have := Nat.mul_le_mul_right (m*D) hK; nlinarith only [this,h1mD]
  have hDQ : D ≤ K*(m*D) := by have := Nat.mul_le_mul_right (m*D) hK; nlinarith only [this,hDm]
  nlinarith only [hmult,hQ,hDQ]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMLearnerActive
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
open AlgorithmInfrastructure
abbrev validationWork (d p k M m : ℕ) : ℕ :=
  44+7*featureDimension d p+(k*M)*(60+8*featureDimension d p+m*(25+9*featureDimension d p))
abbrev activeLearnerWork (d p k M n m : ℕ) : ℕ := activeTrainingWork d p k n m+validationWork d p k M m
def learnerActiveCommand : Cmd := .seq activeTrainingCommand validationCommand
lemma learner_active_correct (ω : PolySampIso.Streams) (d p k M n m : ℕ) (hn : 0 < n)
    (hKpos : 0 < k*M) (hMpos : 0 < M) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) (input : ℕ → ℝ)
    (S : Fin (k*n+m) → Example d) (hS : InputRows d (k*n+m) S input)
    (h4 : input 4=n) (h2 : input 2=k) (h5 : input 5=m) (h6 : input 6=ε) (h7 : input 7=δ)
    (s : Store) (hs : PreparedShape d p M (k*n+m) n input s)
    (hDn : featureDimension d p ≤ n) (hgc : s.gc=0) (hec : s.ec=0) :
    ∃ t cost, Eval ω learnerActiveCommand s t cost ∧ cost ≤ activeLearnerWork d p k M n m ∧
      rawOutput d p (fun i => t.mem (-1-(i : ℤ)))=
        ((algorithmCoins d p k M n m hKpos ε δ S ω).1.val,(algorithmCoins d p k M n m hKpos ε δ S ω).2.val) ∧
      t.mem (-1-(featureDimension d p : ℤ))=((algorithmCoins d p k M n m hKpos ε δ S ω).2.val : ℝ) := by
  obtain ⟨seed,u,cu,hu,hcu,hReady,hInv,huec⟩ := active_training_correct ω d p k M n m hn ε δ hε hδ input S hS h4 h2 h5 h6 h7 s hs hDn hgc hec
  obtain ⟨huD,huM,huk,hum,huε⟩ := post_training_parameters hReady hInv
  obtain ⟨huBase,huBankEnd,huValEnd⟩ := post_training_geometry hReady hInv
  obtain ⟨t,ct,ht,hct,hraw,hthreshold⟩ := validation_command_correct ω d p k M m hKpos hMpos ε
    (validationBlock d k n m S) (fun j => optimizerDraw d p n ε δ (trainingBlocks d k n m S j)
      (normalBlockDraw k n (featureDimension d p) 0 ω j)) u huD huM huk hum huε huec huBase huBankEnd huValEnd
    (post_training_bank hReady hInv) (hInv.validation_rows hReady)
  refine ⟨t,cu+ct,Eval.seq hu ht,?_,hraw,hthreshold⟩
  exact Nat.add_le_add hcu hct
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.Schedule
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian

end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma degree_dimension_le (d p : ℕ) (hd : 1 ≤ d) : p + 1 ≤ featureDimension d p := by
  have hh := Nat.choose_le_choose p (show p + 1 ≤ d + p by omega)
  simpa [featureDimension, Nat.choose_succ_self_right] using hh

lemma arithmetic_cost_bound (k n₀ m M p D : ℕ)
    (hk : 0 < k) (hn : 0 < n₀) (hp : p ≤ D) (hD : D ≤ n₀) (hM : M ≤ p) :
    let n := k * n₀ + m
    (n : ℝ) * p * D + (k : ℝ) * n₀ ^ 2 * D + (k : ℝ) * M * m * D ≤
      3 * (n : ℝ) ^ 3 := by
  dsimp only
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp' : (p : ℝ) ≤ D := by exact_mod_cast hp
  have hD' : (D : ℝ) ≤ n₀ := by exact_mod_cast hD
  have hM' : (M : ℝ) ≤ p := by exact_mod_cast hM
  have hnle : (n₀ : ℝ) ≤ (k * n₀ + m : ℕ) := by push_cast; nlinarith
  have hmle : (m : ℝ) ≤ (k * n₀ + m : ℕ) := by push_cast; nlinarith
  have hkN : (k : ℝ) * n₀ ≤ (k * n₀ + m : ℕ) := by push_cast; linarith
  have hnlen : n₀ ≤ k * n₀ + m := by exact_mod_cast hnle
  have hnall : (0 : ℝ) ≤ (k * n₀ + m : ℕ) := Nat.cast_nonneg _
  have hfirst : ((k * n₀ + m : ℕ) : ℝ) * p * D ≤ ((k * n₀ + m : ℕ) : ℝ)^3 := by
    calc
      _ ≤ ((k * n₀ + m : ℕ) : ℝ) * (k * n₀ + m : ℕ) * (k * n₀ + m : ℕ) := by gcongr <;> omega
      _ = _ := by ring
  have hsecond : (k : ℝ) * n₀^2 * D ≤ ((k * n₀ + m : ℕ) : ℝ)^3 := by
    calc
      _ = ((k : ℝ) * n₀) * n₀ * D := by ring
      _ ≤ ((k * n₀ + m : ℕ) : ℝ) * (k * n₀ + m : ℕ) * (k * n₀ + m : ℕ) := by gcongr <;> omega
      _ = _ := by ring
  have hthird : (k : ℝ) * M * m * D ≤ ((k * n₀ + m : ℕ) : ℝ)^3 := by
    calc
      _ ≤ ((k : ℝ) * n₀) * m * n₀ := by gcongr <;> omega
      _ ≤ ((k * n₀ + m : ℕ) : ℝ) * (k * n₀ + m : ℕ) * (k * n₀ + m : ℕ) := by gcongr
      _ = _ := by ring
  linarith
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
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.OperationalScheduleBounds
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
lemma coordinate_dimension_le (d p : ℕ) (hp : 1 ≤ p) : d+1 ≤ featureDimension d p := by
  have h := degree_dimension_le p d hp
  have he : featureDimension p d=featureDimension d p := by
    unfold featureDimension
    rw [Nat.add_comm p d]
    exact Nat.choose_symm_add
  rw [he] at h
  exact h
lemma dense_learner_feature_cost (d p k n₀ m : ℕ) (hp : 1 ≤ p)
    (hD : featureDimension d p ≤ n₀) (hm : m ≤ k*n₀) :
    ((k*n₀+m : ℕ) : ℝ)*(d+p+1)*featureDimension d p ≤
      ((k*n₀+m : ℕ) : ℝ)*p*featureDimension d p+2*(k : ℝ)*n₀^2*featureDimension d p := by
  have hd : d+1 ≤ n₀ := (coordinate_dimension_le d p hp).trans hD
  have hbound : ((d : ℝ)+1) ≤ n₀ := by exact_mod_cast hd
  have hn : ((k*n₀+m : ℕ) : ℝ) ≤ 2*(k : ℝ)*n₀ := by exact_mod_cast (show k*n₀+m ≤ 2*k*n₀ by nlinarith only [hm])
  have hs : ((k*n₀+m : ℕ) : ℝ)*((d : ℝ)+1)*featureDimension d p ≤
      (2*(k : ℝ)*n₀)*(n₀ : ℝ)*featureDimension d p := by gcongr
  nlinarith only [hs]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RAMInactiveOptimizer
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def dimensionComparison : List Op := [.pointerReal 44 15,.sub 41 44 40]
def optimizerBranchCommand (active : Cmd) : Cmd := .seq prepareShapeCommand
  (.seq (.block dimensionComparison) (.cond (.real 41) active .skip))
def inactiveOptimizerFuel (d n : ℕ) : ℕ := 35+5*d+n*(42+15*d)
local instance : IsProbabilityMeasure PolySampIso.tape := by
  unfold PolySampIso.tape
  haveI := isProbabilityMeasure_expMeasure (one_pos (α := ℝ))
  infer_instance
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMBranchShape
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RAM
lemma dimension_comparison_correct (ω : PolySampIso.Streams) (d p M N n : ℕ) (input : ℕ → ℝ)
    (s : Store) (hs : PreparedShape d p M N n input s) (hDn : featureDimension d p ≤ n) :
    let t := blockAct ω dimensionComparison s
    Eval ω (.block dimensionComparison) s t 2 ∧ PreparedShape d p M N n input t ∧
      Test.holds t (.real 41) ∧ t.gc=s.gc ∧ t.ec=s.ec := by
  dsimp only
  have he := eval_block ω dimensionComparison s
  refine ⟨he,?_,?_,rfl,rfl⟩
  · constructor
    · exact hs.dim
    · exact hs.degreePointer
    · exact hs.thresholdPointer
    · exact hs.inputStart
    · exact hs.exponentBase
    · exact hs.featureBase
    · exact hs.dimension
    · exact hs.totalSize
    · simpa [blockAct,dimensionComparison,Op.act] using hs.budget
    · simpa [blockAct,dimensionComparison,Op.act] using hs.trainSize
    · intro h
      simpa [blockAct,dimensionComparison,Op.act] using hs.active h
    · exact hs.frame
  · have hd : s.ptrs 15=featureDimension d p := by simpa only [if_pos hDn] using hs.dimension
    have hreal : (featureDimension d p : ℝ) ≤ n := by exact_mod_cast hDn
    change (blockAct ω dimensionComparison s).regs 41 ≤ 0
    simp [blockAct,dimensionComparison,Op.act,hd,hs.trainSize]
    exact hDn
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMLearnerEval
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
abbrev shapeWork (d k n m : ℕ) : ℕ := 30+5*d+(k*n+m)*(13+4*d)+n*(29+11*d)
abbrev learnerFuel (d p k M n m : ℕ) : ℕ := shapeWork d k n m+4+activeLearnerWork d p k M n m
lemma learner_eval (ω : PolySampIso.Streams) (d p k M n m : ℕ) (hn : 0 < n)
    (hKpos : 0 < k*M) (hMpos : 0 < M) (ε δ α β : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2) (S : Fin (k*n+m) → Example d)
    (hDn : featureDimension d p ≤ n) :
    ∃ t cost, Eval ω (optimizerBranchCommand learnerActiveCommand)
      (initialStore d p M (learnerInput d p k M n m ε δ α β S)) t cost ∧ cost+1 ≤ learnerFuel d p k M n m ∧
      rawOutput d p (fun i => t.mem (-1-(i : ℤ)))=
        ((algorithmCoins d p k M n m hKpos ε δ S ω).1.val,(algorithmCoins d p k M n m hKpos ε δ S ω).2.val) ∧
      t.mem (-1-(featureDimension d p : ℤ))=((algorithmCoins d p k M n m hKpos ε δ S ω).2.val : ℝ) := by
  let input := learnerInput d p k M n m ε δ α β S
  obtain ⟨u,cu,hcu,hu,huShape,hugc,huec⟩ := prepare_shape_correct ω d p M (k*n+m) n hn input
    (by norm_num [input,learnerInput]) (by norm_num [input,learnerInput])
  let a := blockAct ω dimensionComparison u
  obtain ⟨ha,haShape,haTest,hagc,haec⟩ := dimension_comparison_correct ω d p M (k*n+m) n input u huShape hDn
  obtain ⟨t,ct,ht,hct,hraw,hthreshold⟩ := learner_active_correct ω d p k M n m hn hKpos hMpos ε δ hε hδ input S
    (learnerInput_rows d p k M n m ε δ α β S)
    (by norm_num [input,learnerInput]) (by norm_num [input,learnerInput]) (by norm_num [input,learnerInput])
    (by norm_num [input,learnerInput]) (by norm_num [input,learnerInput]) a haShape hDn (hagc.trans hugc) (haec.trans huec)
  have hall : Eval ω (optimizerBranchCommand learnerActiveCommand) (initialStore d p M input) t (cu+2+1+ct) := by
    convert! Eval.seq hu (Eval.seq ha (Eval.cond_yes (no := .skip) haTest ht)) using 1 <;> omega
  refine ⟨t,_,hall,?_,hraw,hthreshold⟩
  dsimp only [learnerFuel,shapeWork]
  omega
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMLearnerImplementation
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
def gaussianLearnerCode : LearnerProgram := (optimizerBranchCommand learnerActiveCommand).program
lemma learner_implementation (d p k M n m : ℕ) (hn : 0 < n) (hKpos : 0 < k*M) (hMpos : 0 < M)
    (ε δ α β : ℝ) (hε : 0 < ε ∧ ε ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (S : Fin (k*n+m) → Example d) (hDn : featureDimension d p ≤ n) :
    Implements gaussianLearnerCode (learnerFuel d p k M n m) (learnerFuel d p k M n m) d p M
      (learnerInput d p k M n m ε δ α β S) (algorithmLaw concreteOptimizer d p k M n m ε δ S) := by
  classical
  choose result steps he hbound hraw hthreshold using
    fun ω => learner_eval ω d p k M n m hn hKpos hMpos ε δ α β hε hδ S hDn
  let π := fun o : Output d p M => (o.1.val,o.2.val)
  have hπ : Measurable π := measurable_fst.subtype_val.prodMk
    ((measurable_of_countable (fun i : Fin M => i.val)).comp measurable_snd)
  obtain ⟨hCoinMeas,hCoinLaw⟩ := algorithmCoins_law d p k M n m hKpos ε δ S
  have hfun : (fun ω => rawOutput d p (fun i => (result ω).mem (-1-(i : ℤ))))=
      π ∘ algorithmCoins d p k M n m hKpos ε δ S := funext hraw
  apply implements_of_eval (optimizerBranchCommand learnerActiveCommand) d p M (learnerFuel d p k M n m)
    (learnerInput d p k M n m ε δ α β S) _ result steps he hbound
  · intro ω
    dsimp only
    rw [hraw ω]
    refine ⟨(algorithmCoins d p k M n m hKpos ε δ S ω).1.property,
      (algorithmCoins d p k M n m hKpos ε δ S ω).2.isLt,?_⟩
    have hcard := ((lemma_B_8 d).2.2.2 p).2.1
    rw [hcard]
    exact hthreshold ω
  · rw [hfun]
    exact hπ.comp hCoinMeas
  · rw [hfun,← Measure.map_map hπ hCoinMeas,hCoinLaw]
end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.RAMLearnerBudgetOnly
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PrivateAgnosticHalfspace.Gaussian.RAM
abbrev trainBudget (k n D : ℕ) : ℕ := k*n^2*D
abbrev featureBudget (p k n m D : ℕ) : ℕ := (k*n+m)*p*D
structure BasicBudget (d p k n m D : ℕ) : Prop where
  one_le : 1 ≤ trainBudget k n D
  n_le : n ≤ trainBudget k n D
  k_le : k ≤ trainBudget k n D
  m_le : m ≤ trainBudget k n D
  dim_le : D ≤ trainBudget k n D
  coord_le : d ≤ trainBudget k n D
  nd_le : n*d ≤ trainBudget k n D
  kd_le : k*D ≤ trainBudget k n D
  stride_le : n*(D+2) ≤ 3*trainBudget k n D
  data_le : k*n+m ≤ featureBudget p k n m D
  data_coord_le : (k*n+m)*d ≤ featureBudget p k n m D
  noise_le : noiseCount k n D ≤ 4*trainBudget k n D
lemma basic_budget (d p k n m D : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (hd : d+1 ≤ D)
    (hDn : D ≤ n) (hm : m ≤ k*n) : BasicBudget d p k n m D := by
  have hD : 1 ≤ D := by omega
  have hn : 1 ≤ n := by omega
  have hn2 : n ≤ n^2 := by nlinarith only [hn]
  have hpow : 1 ≤ n^2 := by nlinarith only [hn]
  have hnBase : n ≤ n^2*D := hn2.trans (Nat.le_mul_of_pos_right _ hD)
  have hdimBase : D ≤ n^2*D := by have h := Nat.mul_le_mul_right D hpow; simpa using h
  have hbase : n^2*D ≤ trainBudget k n D := by
    have h := Nat.mul_le_mul_right (n^2*D) hk
    simpa only [one_mul,Nat.mul_assoc] using h
  have hnB := hnBase.trans hbase
  have hdB := hdimBase.trans hbase
  have hkB : k ≤ trainBudget k n D := by
    have h := Nat.le_mul_of_pos_right k (show 0 < n^2*D by positivity)
    simpa only [Nat.mul_assoc] using h
  have hkn : k*n ≤ trainBudget k n D := by
    have h := Nat.mul_le_mul_left k hnBase
    simpa only [Nat.mul_assoc] using h
  have hnd : n*d ≤ trainBudget k n D :=
    (Nat.mul_le_mul_left n (show d ≤ D by omega)).trans ((Nat.mul_le_mul_right D hn2).trans hbase)
  have hnDim : n*D ≤ trainBudget k n D := (Nat.mul_le_mul_right D hn2).trans hbase
  have hkd : k*D ≤ trainBudget k n D := by
    have h := Nat.mul_le_mul_left k hdimBase
    simpa only [Nat.mul_assoc] using h
  have hDpd : D ≤ p*D := by have h := Nat.mul_le_mul_right D hp; simpa using h
  have hdata : k*n+m ≤ featureBudget p k n m D := by
    have h := Nat.le_mul_of_pos_right (k*n+m) (show 0 < p*D by positivity)
    simpa only [Nat.mul_assoc] using h
  have hdataD : (k*n+m)*d ≤ featureBudget p k n m D := by
    have h := Nat.mul_le_mul_left (k*n+m) ((show d ≤ D by omega).trans hDpd)
    simpa only [Nat.mul_assoc] using h
  have hnoise : noiseCount k n D ≤ 4*trainBudget k n D := by
    have hnplus : n+1 ≤ 2*n := by omega
    have hndplus : n+D ≤ 2*n := by omega
    have hprod := Nat.mul_le_mul_left k (Nat.mul_le_mul hnplus hndplus)
    have hbound : k*n^2 ≤ trainBudget k n D := Nat.le_mul_of_pos_right _ hD
    dsimp only [noiseCount] at *
    nlinarith only [hprod,hbound]
  refine ⟨hn.trans hnB,hnB,hkB,hm.trans hkn,hdB,(show d ≤ D by omega).trans hdB,hnd,hkd,?_,hdata,hdataD,hnoise⟩
  nlinarith only [hnB,hnDim]
lemma matrix_work_bound (d p k n m : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (hDn : featureDimension d p ≤ n) (hm : m ≤ k*n) :
    matrixWork d p k n m ≤ 500*(featureBudget p k n m (featureDimension d p)+trainBudget k n (featureDimension d p)) := by
  have hb := basic_budget d p k n m (featureDimension d p) hp hk (coordinate_dimension_le d p hp) hDn hm
  have hDense : (k*n+m)*(d+p+1)*featureDimension d p ≤
      (k*n+m)*p*featureDimension d p+2*k*n^2*featureDimension d p := by
    exact_mod_cast dense_learner_feature_cost d p k n m hp hDn hm
  unfold matrixWork featureBudget trainBudget
  nlinarith only [hb.one_le,hb.n_le,hb.k_le,hb.m_le,hb.data_le,hDense]
lemma heap_work_bound (d p k n m : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (hDn : featureDimension d p ≤ n) (hm : m ≤ k*n) :
    heapWork d p k n m ≤ 200*trainBudget k n (featureDimension d p) := by
  have hb := basic_budget d p k n m (featureDimension d p) hp hk (coordinate_dimension_le d p hp) hDn hm
  unfold heapWork
  nlinarith only [hb.one_le,hb.noise_le,hb.dim_le,hb.stride_le,hb.kd_le]
lemma shape_work_bound (d p k n m : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (hDn : featureDimension d p ≤ n) (hm : m ≤ k*n) :
    shapeWork d k n m ≤ 100*(featureBudget p k n m (featureDimension d p)+trainBudget k n (featureDimension d p)) := by
  have hb := basic_budget d p k n m (featureDimension d p) hp hk (coordinate_dimension_le d p hp) hDn hm
  unfold shapeWork
  nlinarith only [hb.one_le,hb.coord_le,hb.data_le,hb.data_coord_le,hb.n_le,hb.nd_le]
lemma learner_fuel_bound (d p k M n m : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (hM : 1 ≤ M) (hm1 : 1 ≤ m)
    (hDn : featureDimension d p ≤ n) (hm : m ≤ k*n) :
    learnerFuel d p k M n m ≤ 100000*((k*n+m)*p*featureDimension d p+k*n^2*featureDimension d p+k*M*m*featureDimension d p) := by
  have hDim : 1 ≤ featureDimension d p := by have := coordinate_dimension_le d p hp; omega
  have hn : 1 ≤ n := hDim.trans hDn
  have hB := basic_budget d p k n m (featureDimension d p) hp hk (coordinate_dimension_le d p hp) hDn hm
  have hs := shape_work_bound d p k n m hp hk hDn hm
  have hmatrix := matrix_work_bound d p k n m hp hk hDn hm
  have hheap := heap_work_bound d p k n m hp hk hDn hm
  have hblocks := trainingBlocks_cost_bound k (featureDimension d p) n hk hDim hn
  have hval := validation_command_cost (k*M) m (featureDimension d p) (Nat.mul_pos hk hM) hm1 hDim
  let F := featureBudget p k n m (featureDimension d p)
  let B := trainBudget k n (featureDimension d p)
  let Z := k*M*m*featureDimension d p
  have hOne : 1 ≤ B := hB.one_le
  change shapeWork d k n m ≤ 100*(F+B) at hs
  change matrixWork d p k n m ≤ 500*(F+B) at hmatrix
  change heapWork d p k n m ≤ 200*B at hheap
  have hblocks' : blocksWork d p k n ≤ 500*B := by
    simpa only [blocksWork,B,trainBudget,Nat.mul_assoc] using hblocks
  have hval' : validationWork d p k M m ≤ 1000*Z := by
    simpa only [validationWork,Z,Nat.mul_assoc] using hval
  change learnerFuel d p k M n m ≤ 100000*(F+B+Z)
  dsimp only [learnerFuel,activeLearnerWork,activeTrainingWork]
  omega

end PrivateAgnosticHalfspace.Gaussian.RAM
end

section
-- Solutions.Sol_ordered_learner_program
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian
open PrivateAgnosticHalfspace.Gaussian.RAM

theorem solution :
    ∃ learnerCode : LearnerProgram,
    ∀ O : Optimizer, RealizesOrderedRegression O →
      (∀ d p k M n₀ m : ℕ, 1 ≤ p → 0 < k → 0 < M → 0 < m →
        featureDimension d p ≤ n₀ → m ≤ k*n₀ → p ≤ featureDimension d p → M ≤ p →
        ∀ ε δ α β : ℝ, 0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
        ∀ S : Fin (k*n₀+m) → Example d, ∃ fuel cost : ℕ,
          (cost : ℝ) ≤ (100000 : ℝ)*(((k*n₀+m : ℕ) : ℝ)*p*featureDimension d p+
            (k : ℝ)*n₀^2*featureDimension d p+(k : ℝ)*M*m*featureDimension d p) ∧
          (cost : ℝ) ≤ 3*(100000 : ℝ)*((k*n₀+m : ℕ) : ℝ)^3 ∧
          Implements learnerCode fuel cost d p M (learnerInput d p k M n₀ m ε δ α β S)
            (algorithmLaw O d p k M n₀ m ε δ S)) := by
  refine ⟨gaussianLearnerCode,?_⟩
  intro O hO
  have heq := realizesOrderedRegression_unique O hO
  subst O
  intro d p k M n₀ m hp hk hM hm hDn hmBlock hpD hMp ε δ α β hε hδ S
  have hn : 0 < n₀ := by have hh := coordinate_dimension_le d p hp; omega
  have hImpl := learner_implementation d p k M n₀ m hn (Nat.mul_pos hk hM) hM ε δ α β hε hδ S hDn
  have hLaw : algorithmLaw operationalOptimizer d p k M n₀ m ε δ S=
      algorithmLaw concreteOptimizer d p k M n₀ m ε δ S := by
    unfold algorithmLaw
    rw [operationalOptimizer_eq d p n₀ hDn]
  rw [← hLaw] at hImpl
  have hCost : (learnerFuel d p k M n₀ m : ℝ) ≤ (100000 : ℝ)*(((k*n₀+m : ℕ) : ℝ)*p*featureDimension d p+
      (k : ℝ)*n₀^2*featureDimension d p+(k : ℝ)*M*m*featureDimension d p) := by
    exact_mod_cast learner_fuel_bound d p k M n₀ m hp hk hM hm hDn hmBlock
  have hArithmetic := arithmetic_cost_bound k n₀ m M p (featureDimension d p) hk hn hpD hDn hMp
  refine ⟨learnerFuel d p k M n₀ m,learnerFuel d p k M n₀ m,hCost,?_,hImpl⟩
  exact hCost.trans (by nlinarith only [hArithmetic])
end
