-- Prove2me | solution 1 for RobustGeneralization.GaussLower.corollary23_robust_error_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T22:13:05.232927+00:00
-- url     : https://prove2.me/submissions/52f5cfcc-db38-4744-92fd-ed6a917845cf

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

set_option autoImplicit false

/- Complete checked body: GaussianCoordinates -/
section

set_option autoImplicit false
open scoped BigOperators
open RobustGeneralization.GaussLower

namespace RobustGeneralization.GaussLowerProof

abbrev Joint (d n : ℕ) := EuclideanSpace ℝ (Option (Fin n) × Fin d)

noncomputable def prior {d n : ℕ} (v : Joint d n) : E d :=
  WithLp.toLp 2 (fun j => v (none, j))

noncomputable def noise {d n : ℕ} (v : Joint d n) (i : Fin n) : E d :=
  WithLp.toLp 2 (fun j => v (some i, j))

noncomputable def mean {d n : ℕ} (σ : ℝ) (v : Joint d n) : E d :=
  (σ^2+(n : ℝ))⁻¹ • ((n : ℝ) • prior v + σ • ∑ i, noise v i)

noncomputable def shift {d n : ℕ} (σ : ℝ) (v : Joint d n) : E d :=
  (σ^2+(n : ℝ))⁻¹ • (σ • prior v - ∑ i, noise v i)

noncomputable def zSample {d n : ℕ} (σ : ℝ) (v : Joint d n) (i : Fin n) : E d :=
  prior v + σ • noise v i

def labelSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def trainingData {d n : ℕ} (σ : ℝ) (v : Joint d n)
    (labels : Fin n → Bool) (i : Fin n) : E d × Bool :=
  (labelSign (labels i) • zSample σ v i, labels i)

noncomputable def testData {d : ℕ} (θ : E d) (σ : ℝ) (ζ : E d) (b : Bool) : E d × Bool :=
  (labelSign b • (θ + σ • ζ), b)

@[simp] theorem prior_apply {d n : ℕ} (v : Joint d n) (j : Fin d) :
    prior v j = v (none, j) := rfl

@[simp] theorem noise_apply {d n : ℕ} (v : Joint d n) (i : Fin n) (j : Fin d) :
    noise v i j = v (some i, j) := rfl

@[simp] theorem labelSign_not (b : Bool) : labelSign (!b) = -labelSign b := by
  cases b <;> norm_num [labelSign]

@[simp] theorem abs_labelSign (b : Bool) : |labelSign b| = 1 := by
  cases b <;> norm_num [labelSign]

theorem prior_continuous {d n : ℕ} : Continuous (@prior d n) := by
  unfold prior
  fun_prop

theorem noise_continuous {d n : ℕ} (i : Fin n) : Continuous (fun v : Joint d n => noise v i) := by
  unfold noise
  fun_prop

theorem mean_continuous {d n : ℕ} (σ : ℝ) : Continuous (@mean d n σ) := by
  unfold mean
  have hs : Continuous (fun v : Joint d n => ∑ i, noise v i) :=
    continuous_finsetSum Finset.univ (fun i _ => noise_continuous i)
  exact ((prior_continuous.const_smul (n : ℝ)).add (hs.const_smul σ)).const_smul ((σ^2+(n : ℝ))⁻¹)

theorem shift_continuous {d n : ℕ} (σ : ℝ) : Continuous (@shift d n σ) := by
  unfold shift
  have hs : Continuous (fun v : Joint d n => ∑ i, noise v i) :=
    continuous_finsetSum Finset.univ (fun i _ => noise_continuous i)
  exact ((prior_continuous.const_smul σ).sub hs).const_smul ((σ^2+(n : ℝ))⁻¹)

theorem mean_eq_sum_zSample {d n : ℕ} (σ : ℝ) (v : Joint d n) :
    mean σ v = (σ^2+(n : ℝ))⁻¹ • ∑ i, zSample σ v i := by
  simp only [mean, zSample, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum]
  norm_cast

theorem prior_sub_mean {d n : ℕ} (σ : ℝ) (hσ : 0 < σ) (v : Joint d n) :
    prior v - mean σ v = σ • shift σ v := by
  have hq : σ^2+(n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  ext j
  simp only [mean, shift, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: ResidualReflection -/
section

set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open RobustGeneralization.GaussLower

namespace RobustGeneralization.GaussLowerProof

noncomputable def axisNormal (n : ℕ) (σ : ℝ) : EuclideanSpace ℝ (Option (Fin n)) :=
  WithLp.toLp 2 (fun o => match o with | none => σ | some _ => -1)

noncomputable def axisReflection (n : ℕ) (σ : ℝ) :
    EuclideanSpace ℝ (Option (Fin n)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Option (Fin n)) :=
  (ℝ ∙ axisNormal n σ)ᗮ.reflection

theorem axisNormal_norm_sq (n : ℕ) (σ : ℝ) : ‖axisNormal n σ‖^2 = σ^2+(n : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option]
  simp [axisNormal]

theorem axisNormal_inner (n : ℕ) (σ : ℝ) (v : EuclideanSpace ℝ (Option (Fin n))) :
    ⟪axisNormal n σ, v⟫_ℝ = σ*v none - ∑ i, v (some i) := by
  simp [PiLp.inner_apply, axisNormal, Fintype.sum_option, sub_eq_add_neg, mul_comm]

theorem axisReflection_apply (n : ℕ) (σ : ℝ) (v : EuclideanSpace ℝ (Option (Fin n))) :
    axisReflection n σ v =
      v - (2*((σ*v none-∑ i, v (some i))/(σ^2+(n : ℝ)))) • axisNormal n σ := by
  unfold axisReflection
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, axisNormal_norm_sq, axisNormal_inner]
  module

noncomputable def columnCurry (d n : ℕ) :
    Joint d n ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin d => EuclideanSpace ℝ (Option (Fin n))) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((Equiv.prodComm (Option (Fin n)) (Fin d)).trans
      (Equiv.sigmaEquivProd (Fin d) (Option (Fin n))).symm)).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun _ : Fin d => fun _ : Option (Fin n) => ℝ))

@[simp] theorem columnCurry_apply {d n : ℕ} (v : Joint d n) (j : Fin d) (i : Option (Fin n)) :
    columnCurry d n v j i = v (i,j) := rfl

@[simp] theorem columnCurry_symm_apply {d n : ℕ}
    (v : PiLp 2 (fun _ : Fin d => EuclideanSpace ℝ (Option (Fin n))))
    (i : Option (Fin n)) (j : Fin d) :
    (columnCurry d n).symm v (i,j) = v j i := rfl

/-- Reflect each feature column in the hyperplane perpendicular to (σ,-1,...,-1). -/
noncomputable def residualReflection (d n : ℕ) (σ : ℝ) : Joint d n ≃ₗᵢ[ℝ] Joint d n :=
  (columnCurry d n).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin d => axisReflection n σ)).trans
      (columnCurry d n).symm)

theorem residualReflection_prior {d n : ℕ} (σ : ℝ) (v : Joint d n) :
    prior (residualReflection d n σ v) = prior v - (2*σ) • shift σ v := by
  ext j
  simp only [prior_apply, residualReflection, LinearIsometryEquiv.trans_apply,
    columnCurry_symm_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    axisReflection_apply, columnCurry_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    axisNormal, shift, WithLp.ofLp_sum, Finset.sum_apply, noise_apply]
  ring

theorem residualReflection_noise {d n : ℕ} (σ : ℝ) (v : Joint d n) (i : Fin n) :
    noise (residualReflection d n σ v) i = noise v i + (2 : ℝ) • shift σ v := by
  ext j
  simp only [noise_apply, residualReflection, LinearIsometryEquiv.trans_apply,
    columnCurry_symm_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    axisReflection_apply, columnCurry_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    axisNormal, shift, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, prior_apply]
  ring

theorem residualReflection_zSample {d n : ℕ} (σ : ℝ) (v : Joint d n) (i : Fin n) :
    zSample σ (residualReflection d n σ v) i = zSample σ v i := by
  rw [zSample, residualReflection_prior, residualReflection_noise, zSample]
  module

theorem residualReflection_mean {d n : ℕ} (σ : ℝ) (v : Joint d n) :
    mean σ (residualReflection d n σ v) = mean σ v := by
  simp only [mean_eq_sum_zSample, residualReflection_zSample]

theorem residualReflection_prior_eq {d n : ℕ} (σ : ℝ) (hσ : 0 < σ) (v : Joint d n) :
    prior (residualReflection d n σ v) = (2 : ℝ) • mean σ v - prior v := by
  rw [residualReflection_prior]
  have he := prior_sub_mean σ hσ v
  calc
    prior v - (2*σ) • shift σ v = prior v - (2 : ℝ) • (σ • shift σ v) := by module
    _ = _ := by rw [← he]; module

theorem residualReflection_trainingData {d n : ℕ} (σ : ℝ) (v : Joint d n)
    (labels : Fin n → Bool) : trainingData σ (residualReflection d n σ v) labels =
      trainingData σ v labels := by
  funext i
  simp only [trainingData, residualReflection_zSample]

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: ObservedAttack -/
section

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open RobustGeneralization.GaussLower

namespace RobustGeneralization.GaussLowerProof

noncomputable def observedMean {d n : ℕ} (σ : ℝ) (S : Fin n → E d × Bool) : E d :=
  (σ^2+(n : ℝ))⁻¹ • ∑ i, labelSign (S i).2 • (S i).1

def goodTraining {d n : ℕ} (σ ε : ℝ) (S : Fin n → E d × Bool) : Prop :=
  ∀ j, |observedMean σ S j| ≤ ε

noncomputable def attackInput {d n : ℕ} (σ : ℝ) (S : Fin n → E d × Bool)
    (p : E d × Bool) : E d := p.1 - labelSign p.2 • observedMean σ S

def selectedEvent {d n : ℕ} (g : (Fin n → E d × Bool) → E d → Bool)
    (σ ε : ℝ) : Set ((Fin n → E d × Bool) × (E d × Bool)) :=
  {p | goodTraining σ ε p.1 ∧ g p.1 (attackInput σ p.1 p.2) ≠ p.2.2}

@[simp] theorem labelSign_mul_self (b : Bool) : labelSign b * labelSign b = 1 := by
  cases b <;> norm_num [labelSign]

@[fun_prop] theorem labelSign_measurable : Measurable labelSign := measurable_of_countable _

@[fun_prop] theorem observedMean_measurable {d n : ℕ} (σ : ℝ) :
    Measurable (@observedMean d n σ) := by
  unfold observedMean
  fun_prop

theorem goodTraining_measurableSet {d n : ℕ} (σ ε : ℝ) :
    MeasurableSet {S : Fin n → E d × Bool | goodTraining σ ε S} := by
  simp only [goodTraining, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).measurable.comp
    (observedMean_measurable σ)).abs measurable_const

@[fun_prop] theorem attackInput_measurable {d n : ℕ} (σ : ℝ) :
    Measurable (fun p : (Fin n → E d × Bool) × (E d × Bool) => attackInput σ p.1 p.2) := by
  unfold attackInput
  fun_prop

theorem selectedEvent_measurable {d n : ℕ} (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) : MeasurableSet (selectedEvent g σ ε) := by
  apply (goodTraining_measurableSet σ ε).preimage measurable_fst |>.inter
  exact (measurableSet_eq_fun (hg.comp (measurable_fst.prodMk (attackInput_measurable σ)))
    (measurable_snd.snd)).compl

theorem observedMean_trainingData {d n : ℕ} (σ : ℝ) (v : Joint d n) (b : Fin n → Bool) :
    observedMean σ (trainingData σ v b) = mean σ v := by
  simp only [observedMean, trainingData, smul_smul, labelSign_mul_self, one_smul]
  exact (mean_eq_sum_zSample σ v).symm

theorem attackInput_mem {d n : ℕ} (σ ε : ℝ) (S : Fin n → E d × Bool)
    (p : E d × Bool) (hS : goodTraining σ ε S) : attackInput σ S p ∈ linfBall p.1 ε := by
  intro j
  have he : (attackInput σ S p) j - p.1 j = -labelSign p.2 * observedMean σ S j := by
    simp only [attackInput, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [he, abs_mul, abs_neg, abs_labelSign, one_mul]
  exact hS j

theorem selectedEvent_subset_robust {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool) (σ ε : ℝ) (S : Fin n → E d × Bool) :
    {p | (S,p) ∈ selectedEvent g σ ε} ⊆
      {p | ∃ x' ∈ linfBall p.1 ε, g S x' ≠ p.2} := by
  rintro p ⟨hgood, herr⟩
  exact ⟨attackInput σ S p, attackInput_mem σ ε S p hgood, herr⟩

theorem attackInput_testData {d n : ℕ} (σ : ℝ) (v : Joint d n)
    (labels : Fin n → Bool) (ζ : E d) (b : Bool) :
    attackInput σ (trainingData σ v labels) (testData (prior v) σ ζ b) =
      labelSign b • (prior v - mean σ v + σ • ζ) := by
  simp only [attackInput, testData, observedMean_trainingData]
  module

theorem reflected_attackInput {d n : ℕ} (σ : ℝ) (hσ : 0 < σ) (v : Joint d n)
    (labels : Fin n → Bool) (ζ : E d) (b : Bool) :
    attackInput σ (trainingData σ (residualReflection d n σ v) labels)
      (testData (prior (residualReflection d n σ v)) σ (-ζ) (!b)) =
    attackInput σ (trainingData σ v labels) (testData (prior v) σ ζ b) := by
  rw [attackInput_testData, attackInput_testData, residualReflection_prior_eq σ hσ,
    residualReflection_mean, labelSign_not]
  module

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GaussianModelBasics -/
section

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

noncomputable section

def fairBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance fairBool_probability : IsProbabilityMeasure fairBool := by
  constructor
  norm_num [fairBool, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

theorem lintegral_fairBool (f : Bool → ℝ≥0∞) :
    (∫⁻ b, f b ∂fairBool) = (1 / 2 : ℝ≥0∞) * f true + (1 / 2 : ℝ≥0∞) * f false := by
  rw [fairBool, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp

theorem fairBool_not : MeasurePreserving Bool.not fairBool fairBool := by
  refine ⟨(measurable_of_finite _), ?_⟩
  rw [fairBool, Measure.map_add _ _ (measurable_of_finite _)]
  simp only [Measure.map_smul, Measure.map_dirac' (measurable_of_finite _),
    Bool.not_true, Bool.not_false]
  exact add_comm _ _

variable {d : ℕ}

theorem gaussian_neg : (stdGaussian (E d)).map (fun x => -x) = stdGaussian (E d) :=
  stdGaussian_map (LinearIsometryEquiv.neg ℝ)

instance gaussVec_probability (θ : E d) (σ : ℝ) : IsProbabilityMeasure (gaussVec θ σ) := by
  unfold gaussVec
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance gaussModel_probability (θ : E d) (σ : ℝ) : IsProbabilityMeasure (gaussModel θ σ) := by
  constructor
  norm_num [gaussModel, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply (by fun_prop : Measurable (fun x : E d => (x, true))),
    Measure.map_apply (by fun_prop : Measurable (fun x : E d => (x, false))),
    ENNReal.inv_two_add_inv_two]

theorem gaussVec_neg (θ : E d) (σ : ℝ) :
    (gaussVec θ σ).map (fun x => -x) = gaussVec (-θ) σ := by
  unfold gaussVec
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h := congrArg (fun μ : Measure (E d) => μ.map (fun x => -θ + σ • x))
    (gaussian_neg (d := d))
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1
  congr 1
  funext x
  simp [add_comm]

@[fun_prop] theorem model_labelSign_measurable : Measurable labelSign := (measurable_of_finite _)

@[fun_prop] theorem testData_measurable (θ : E d) (σ : ℝ) :
    Measurable (fun p : E d × Bool => testData θ σ p.1 p.2) := by
  have h1 := model_labelSign_measurable.comp (measurable_snd : Measurable (Prod.snd : E d × Bool → Bool))
  have h2 : Measurable (fun p : E d × Bool => θ + σ • p.1) := by fun_prop
  have h3 := (h1.smul h2).prodMk (measurable_snd : Measurable (Prod.snd : E d × Bool → Bool))
  exact h3

theorem testData_law (θ : E d) (σ : ℝ) :
    ((stdGaussian (E d)).prod fairBool).map (fun p => testData θ σ p.1 p.2) =
      gaussModel θ σ := by
  rw [fairBool, Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.map_add _ _ (testData_measurable θ σ), Measure.map_smul, Measure.map_smul,
    Measure.prod_dirac, Measure.prod_dirac,
    Measure.map_map (testData_measurable θ σ) measurable_prodMk_right,
    Measure.map_map (testData_measurable θ σ) measurable_prodMk_right]
  have hpos : (stdGaussian (E d)).map (fun x => testData θ σ x true) =
      (gaussVec θ σ).map (fun x => (x, true)) := by
    rw [gaussVec, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp [testData, labelSign]
  have hneg : (stdGaussian (E d)).map (fun x => testData θ σ x false) =
      (gaussVec (-θ) σ).map (fun x => (x, false)) := by
    rw [← gaussVec_neg θ σ, gaussVec, Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp [testData, labelSign, add_comm]
  change (1 / 2 : ℝ≥0∞) • ((stdGaussian (E d)).map (fun x => testData θ σ x true)) +
    (1 / 2 : ℝ≥0∞) • ((stdGaussian (E d)).map (fun x => testData θ σ x false)) = _
  rw [hpos, hneg]
  rfl

end
end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: SelectedRisk -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

noncomputable abbrev testNoiseLaw (d : ℕ) : Measure (E d × Bool) := (stdGaussian (E d)).prod fairBool

noncomputable def selectedKernel {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool) (σ ε : ℝ)
    (q : (E d × (Fin n → E d × Bool)) × (E d × Bool)) : ℝ≥0∞ :=
  (selectedEvent g σ ε).indicator (fun _ => 1)
    (q.1.2, testData q.1.1 σ q.2.1 q.2.2)

noncomputable def selectedRisk {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool) (σ ε : ℝ)
    (q : E d × (Fin n → E d × Bool)) : ℝ≥0∞ :=
  ∫⁻ t, selectedKernel g σ ε (q,t) ∂testNoiseLaw d

theorem selectedKernel_measurable {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) : Measurable (selectedKernel g σ ε) := by
  have ht : Measurable (fun q : (E d × (Fin n → E d × Bool)) × (E d × Bool) =>
      testData q.1.1 σ q.2.1 q.2.2) := by
    unfold testData
    fun_prop
  exact (measurable_const.indicator (selectedEvent_measurable g hg σ ε)).comp
    ((measurable_snd.comp measurable_fst).prodMk ht)

theorem selectedRisk_measurable {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) : Measurable (selectedRisk g σ ε) :=
  (selectedKernel_measurable g hg σ ε).lintegral_prod_right'

/-- The selected attack is compared with outer robust error before any change of joint law. -/
theorem selectedRisk_le_robustErr {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) (θ : E d) (S : Fin n → E d × Bool) :
    selectedRisk g σ ε (θ,S) ≤ robustErr (gaussModel θ σ) (g S) ε := by
  let A : Set (E d × Bool) := {p | (S,p) ∈ selectedEvent g σ ε}
  have hA : MeasurableSet A :=
    (selectedEvent_measurable g hg σ ε).preimage (measurable_const.prodMk measurable_id)
  have he : selectedRisk g σ ε (θ,S) = gaussModel θ σ A := by
    rw [← testData_law θ σ, Measure.map_apply (testData_measurable θ σ) hA]
    change (∫⁻ t, selectedKernel g σ ε ((θ,S),t) ∂testNoiseLaw d) = _
    have hf : (fun t => selectedKernel g σ ε ((θ,S),t)) =
        ((fun t => testData θ σ t.1 t.2) ⁻¹' A).indicator (fun _ => 1) := by
      rfl
    rw [hf, lintegral_indicator (hA.preimage (testData_measurable θ σ))]
    simp
  rw [he]
  exact measure_mono (selectedEvent_subset_robust g σ ε S)

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: MeasurePairing -/
section

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

/-- A measure-preserving pairing exchanges an event with its complement inside a fixed good set. -/
theorem measure_eq_half_of_pairing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (A B : Set Ω) (hB : MeasurableSet B) (hBA : B ⊆ A)
    (hA : ∀ x, T x ∈ A ↔ x ∈ A)
    (hpair : ∀ x ∈ A, T x ∈ B ↔ x ∉ B) :
    (1 / 2 : ℝ≥0∞) * μ A = μ B := by
  have hdisj : Disjoint B (T ⁻¹' B) := by
    apply Set.disjoint_left.mpr
    intro x hx hTx
    exact (hpair x (hBA hx)).mp hTx hx
  have hunion : B ∪ (T ⁻¹' B) = A := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hBA hx
      · exact (hA x).mp (hBA hx)
    · intro hx
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · exact Or.inr ((hpair x hx).mpr hxB)
  have hpre : μ (T ⁻¹' B) = μ B := hT.measure_preimage hB.nullMeasurableSet
  rw [← hunion, measure_union hdisj (hB.preimage hT.measurable), hpre, mul_add,
    ← add_mul]
  have hhalf : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
    simpa only [one_div] using ENNReal.inv_two_add_inv_two
  rw [hhalf, one_mul]

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GaussianProducts -/
section

open MeasureTheory ProbabilityTheory WithLp
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace RobustGeneralization.GaussLowerProof

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem gaussian_pi_toLp :
    (Measure.pi (fun _ : ι => stdGaussian V)).map (toLp 2) =
      stdGaussian (PiLp 2 (fun _ : ι => V)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_pi, charFun_stdGaussian]
  simp_rw [charFun_stdGaussian, ← Complex.exp_sum]
  congr 1
  rw [← Complex.ofReal_pow, PiLp.norm_sq_eq_of_L2]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem gaussian_pi_ofLp :
    (stdGaussian (PiLp 2 (fun _ : ι => V))).map ofLp =
      Measure.pi (fun _ : ι => stdGaussian V) := by
  rw [← gaussian_pi_toLp (ι := ι) (V := V), Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Measure.map_id']

theorem gaussian_weighted_sum (w : ι → ℝ) :
    (Measure.pi (fun _ : ι => stdGaussian V)).map (fun x : ι → V => ∑ i, w i • x i) =
      (stdGaussian V).map (fun v => Real.sqrt (∑ i, w i ^ 2) • v) := by
  have hM : Measurable (fun x : ι → V => ∑ i, w i • x i) :=
    (continuous_finsetSum _ fun i _ => continuous_const.smul (continuous_apply i)).measurable
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_smul, charFun_stdGaussian, charFun_apply,
    integral_map hM.aemeasurable (by fun_prop)]
  simp_rw [sum_inner, real_inner_smul_left, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : ι => stdGaussian V)
    (f := fun i (x : V) => Complex.exp ((w i * ⟪x, t⟫_ℝ : ℝ) * Complex.I))]
  have he (i : ι) :
      (∫ x : V, Complex.exp ((w i * ⟪x, t⟫_ℝ : ℝ) * Complex.I) ∂stdGaussian V) =
        Complex.exp (- ‖w i • t‖ ^ 2 / 2) := by
    rw [← charFun_stdGaussian]
    simp only [charFun_apply, real_inner_smul_right]
  have hnorm (a : ℝ) : (‖a • t‖ : ℂ) ^ 2 = (a : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 := by
    have hr : ‖a • t‖ ^ 2 = a ^ 2 * ‖t‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact_mod_cast hr
  simp_rw [he, ← Complex.exp_sum, hnorm]
  have hsqrt : ((Real.sqrt (∑ i, w i ^ 2) : ℝ) : ℂ) ^ 2 = ((∑ i, w i ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (w i))]
  rw [hsqrt]
  congr 1
  push_cast
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.sum_mul]

variable {κ : Type*} [Fintype κ]

def rowCurry : EuclideanSpace ℝ (ι × κ) ≃ₗᵢ[ℝ]
    PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sigmaEquivProd ι κ).symm).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : ι) (_ : κ) => ℝ))

theorem rowCurry_apply (x : EuclideanSpace ℝ (ι × κ)) :
    rowCurry x = toLp 2 (fun i : ι => (toLp 2 fun j : κ => x (i, j))) := rfl

theorem gaussian_rows :
    (stdGaussian (EuclideanSpace ℝ (ι × κ))).map
      (fun x => (fun i : ι => (toLp 2 fun j : κ => x (i, j)))) =
      Measure.pi (fun _ : ι => stdGaussian (EuclideanSpace ℝ κ)) := by
  have h := stdGaussian_map (rowCurry (ι := ι) (κ := κ))
  have hm := congrArg (fun μ => μ.map ofLp) h
  rw [Measure.map_map (by fun_prop) (by fun_prop), gaussian_pi_ofLp] at hm
  exact hm

end
end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GaussianJointLaw -/
section

open MeasureTheory ProbabilityTheory WithLp RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

noncomputable section

theorem joint_unpack_law (d n : ℕ) :
    (stdGaussian (Joint d n)).map (fun v => (prior v, noise v)) =
      (stdGaussian (E d)).prod (Measure.pi fun _ : Fin n => stdGaussian (E d)) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => E d)
  have he : MeasurePreserving e.symm
      ((Measure.pi fun _ : Fin n => stdGaussian (E d)).prod (stdGaussian (E d)))
      (Measure.pi fun _ : Option (Fin n) => stdGaussian (E d)) :=
    ⟨e.symm.measurable, Measure.pi_map_piOptionEquivProd (β := fun _ : Option (Fin n) => E d)
      (fun _ : Option (Fin n) => stdGaussian (E d))⟩
  have hr : MeasurePreserving
      (fun v : Joint d n => (fun i : Option (Fin n) => (toLp 2 fun j : Fin d => v (i, j))))
      (stdGaussian (Joint d n)) (Measure.pi fun _ : Option (Fin n) => stdGaussian (E d)) :=
    ⟨by fun_prop, gaussian_rows⟩
  have h := (Measure.measurePreserving_swap.comp he.symm).comp hr
  exact h.map_eq

end
end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: TrainingModelLaw -/
section

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

noncomputable section

abbrev noiseLaw (d n : ℕ) : Measure (Fin n → E d) :=
  Measure.pi fun _ => stdGaussian (E d)

abbrev labelsLaw (n : ℕ) : Measure (Fin n → Bool) := Measure.pi fun _ => fairBool

theorem generated_training_law (d n : ℕ) (θ : E d) (σ : ℝ) :
    ((noiseLaw d n).prod (labelsLaw n)).map
      (fun p i => testData θ σ (p.1 i) (p.2 i)) =
        Measure.pi (fun _ : Fin n => gaussModel θ σ) := by
  have hp : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow (E d) Bool (Fin n)).symm
      ((noiseLaw d n).prod (labelsLaw n))
      (Measure.pi fun _ : Fin n => (stdGaussian (E d)).prod fairBool) :=
    (measurePreserving_arrowProdEquivProdArrow (E d) Bool (Fin n)
      (fun _ => stdGaussian (E d)) (fun _ => fairBool)).symm
  have hi : ∀ i : Fin n, MeasurePreserving (fun p : E d × Bool => testData θ σ p.1 p.2)
      ((stdGaussian (E d)).prod fairBool) (gaussModel θ σ) :=
    fun _ => ⟨testData_measurable θ σ, testData_law θ σ⟩
  exact ((measurePreserving_pi _ _ hi).comp hp).map_eq

@[fun_prop] theorem generated_training_measurable (d n : ℕ) (σ : ℝ) :
    Measurable (fun p : (E d × (Fin n → E d)) × (Fin n → Bool) =>
      (p.1.1, fun i => testData p.1.1 σ (p.1.2 i) (p.2 i))) := by
  apply Measurable.prodMk (measurable_fst.comp measurable_fst)
  apply measurable_pi_lambda
  intro i
  have hev : Measurable (fun p : (E d × (Fin n → E d)) × (Fin n → Bool) => p.2 i) := by fun_prop
  have hs := model_labelSign_measurable.comp hev
  have hz : Measurable (fun p : (E d × (Fin n → E d)) × (Fin n → Bool) =>
      p.1.1 + σ • p.1.2 i) := by fun_prop
  have hh := (hs.smul hz).prodMk ((measurable_pi_apply i).comp measurable_snd)
  exact hh

/-- Change only a measurable selected-error integrand to the Gaussian product model. -/
theorem joint_training_lintegral (d n : ℕ) (σ : ℝ)
    (F : E d × (Fin n → E d × Bool) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v : Joint d n, ∫⁻ labels, F (prior v, trainingData σ v labels)
      ∂labelsLaw n ∂stdGaussian (Joint d n)) =
    ∫⁻ θ : E d, ∫⁻ S, F (θ, S) ∂(Measure.pi fun _ : Fin n => gaussModel θ σ)
      ∂stdGaussian (E d) := by
  let G : E d × (Fin n → E d) → ℝ≥0∞ := fun p =>
    ∫⁻ labels, F (p.1, fun i => testData p.1 σ (p.2 i) (labels i)) ∂labelsLaw n
  have hG : Measurable G := (hF.comp (generated_training_measurable d n σ)).lintegral_prod_right'
  have hnoise : Measurable (fun v : Joint d n => noise v) := by
    apply measurable_pi_lambda
    intro i
    exact (noise_continuous i).measurable
  have hu := (prior_continuous (d := d) (n := n)).measurable.prodMk hnoise
  have hmap := lintegral_map (μ := stdGaussian (Joint d n)) hG hu
  rw [joint_unpack_law d n] at hmap
  calc
    _ = ∫⁻ p, G p ∂(stdGaussian (E d)).prod (noiseLaw d n) := hmap.symm
    _ = ∫⁻ θ : E d, ∫⁻ η : Fin n → E d, G (θ, η) ∂noiseLaw d n ∂stdGaussian (E d) :=
      lintegral_prod _ hG.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro θ
      have hsec : Measurable (fun S : Fin n → E d × Bool => F (θ, S)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      have hgen : Measurable (fun p : (Fin n → E d) × (Fin n → Bool) =>
          (fun i => testData θ σ (p.1 i) (p.2 i))) := by
        apply measurable_pi_lambda
        intro i
        have hpair : Measurable (fun p : (Fin n → E d) × (Fin n → Bool) => (p.1 i, p.2 i)) := by fun_prop
        have hcomp := (testData_measurable θ σ).comp hpair
        exact hcomp
      rw [← generated_training_law d n θ σ, lintegral_map hsec hgen]
      exact (lintegral_prod (μ := noiseLaw d n) (ν := labelsLaw n)
        (fun p => F (θ, fun i => testData θ σ (p.1 i) (p.2 i)))
        (hsec.comp hgen).aemeasurable).symm

end
end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GeneratedPairing -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

abbrev Experiment (d n : ℕ) := (Joint d n × (Fin n → Bool)) × (E d × Bool)

noncomputable abbrev experimentLaw (d n : ℕ) : Measure (Experiment d n) :=
  ((stdGaussian (Joint d n)).prod (labelsLaw n)).prod (testNoiseLaw d)

noncomputable def dataMap {d n : ℕ} (σ : ℝ) (p : Experiment d n) :
    (Fin n → E d × Bool) × (E d × Bool) :=
  (trainingData σ p.1.1 p.1.2, testData (prior p.1.1) σ p.2.1 p.2.2)

noncomputable def flipExperiment {d n : ℕ} (σ : ℝ) (p : Experiment d n) : Experiment d n :=
  ((residualReflection d n σ p.1.1, p.1.2), (-p.2.1, !p.2.2))

def meanGood {d n : ℕ} (σ ε : ℝ) : Set (Joint d n) := {v | ∀ j, |mean σ v j| ≤ ε}

def experimentGood {d n : ℕ} (σ ε : ℝ) : Set (Experiment d n) :=
  (meanGood σ ε ×ˢ Set.univ) ×ˢ Set.univ

noncomputable def generatedEvent {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool) (σ ε : ℝ) : Set (Experiment d n) :=
  dataMap σ ⁻¹' selectedEvent g σ ε

theorem dataMap_measurable {d n : ℕ} (σ : ℝ) : Measurable (@dataMap d n σ) := by
  unfold dataMap trainingData zSample testData prior noise
  fun_prop

theorem flipExperiment_preserving (d n : ℕ) (σ : ℝ) :
    MeasurePreserving (flipExperiment σ) (experimentLaw d n) (experimentLaw d n) := by
  have hR : MeasurePreserving (residualReflection d n σ)
      (stdGaussian (Joint d n)) (stdGaussian (Joint d n)) :=
    ⟨(residualReflection d n σ).continuous.measurable, stdGaussian_map _⟩
  have hN : MeasurePreserving (fun ζ : E d => -ζ) (stdGaussian (E d)) (stdGaussian (E d)) :=
    ⟨by fun_prop, gaussian_neg⟩
  exact (hR.prod (MeasurePreserving.id (labelsLaw n))).prod (hN.prod fairBool_not)

theorem generatedEvent_measurable {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) : MeasurableSet (generatedEvent g σ ε) :=
  (selectedEvent_measurable g hg σ ε).preimage (dataMap_measurable σ)

theorem generatedEvent_subset_good {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool) (σ ε : ℝ) :
    generatedEvent g σ ε ⊆ experimentGood σ ε := by
  rintro p ⟨hgood, _⟩
  refine ⟨⟨?_, Set.mem_univ _⟩, Set.mem_univ _⟩
  simpa only [goodTraining, dataMap, observedMean_trainingData, meanGood, Set.mem_ofPred_eq] using hgood

theorem flipExperiment_good {d n : ℕ} (σ ε : ℝ) (p : Experiment d n) :
    flipExperiment σ p ∈ experimentGood σ ε ↔ p ∈ experimentGood σ ε := by
  simp only [experimentGood, meanGood, Set.mem_prod, Set.mem_univ, and_true,
    flipExperiment, Set.mem_ofPred_eq, residualReflection_mean]

theorem flipExperiment_error {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool)
    (σ ε : ℝ) (hσ : 0 < σ) (p : Experiment d n) (hp : p ∈ experimentGood σ ε) :
    flipExperiment σ p ∈ generatedEvent g σ ε ↔ p ∉ generatedEvent g σ ε := by
  have hgood : goodTraining σ ε (trainingData σ p.1.1 p.1.2) := by
    have hm : p.1.1 ∈ meanGood σ ε := hp.1.1
    simpa only [goodTraining, meanGood, Set.mem_ofPred_eq, observedMean_trainingData] using hm
  change (goodTraining σ ε (trainingData σ (residualReflection d n σ p.1.1) p.1.2) ∧
    g (trainingData σ (residualReflection d n σ p.1.1) p.1.2)
      (attackInput σ (trainingData σ (residualReflection d n σ p.1.1) p.1.2)
        (testData (prior (residualReflection d n σ p.1.1)) σ (-p.2.1) (!p.2.2))) ≠ !p.2.2) ↔
    ¬ (goodTraining σ ε (trainingData σ p.1.1 p.1.2) ∧
      g (trainingData σ p.1.1 p.1.2)
        (attackInput σ (trainingData σ p.1.1 p.1.2) (testData (prior p.1.1) σ p.2.1 p.2.2)) ≠ p.2.2)
  rw [reflected_attackInput σ hσ, residualReflection_trainingData]
  simp only [hgood, true_and]
  cases hg : g (trainingData σ p.1.1 p.1.2)
      (attackInput σ (trainingData σ p.1.1 p.1.2) (testData (prior p.1.1) σ p.2.1 p.2.2)) <;>
    cases hb : p.2.2 <;> simp

theorem generated_error_half {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) (hσ : 0 < σ) :
    (1 / 2 : ℝ≥0∞) * stdGaussian (Joint d n) (meanGood σ ε) =
      experimentLaw d n (generatedEvent g σ ε) := by
  have h := measure_eq_half_of_pairing (experimentLaw d n) (flipExperiment σ)
    (flipExperiment_preserving d n σ) (experimentGood σ ε) (generatedEvent g σ ε)
    (generatedEvent_measurable g hg σ ε) (generatedEvent_subset_good g σ ε)
    (flipExperiment_good σ ε) (flipExperiment_error g σ ε hσ)
  simpa only [experimentGood, experimentLaw, Measure.prod_prod, measure_univ, mul_one] using h

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GaussianMean -/
section

open MeasureTheory ProbabilityTheory WithLp RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

noncomputable section

def meanWeight (n : ℕ) (σ : ℝ) : Option (Fin n) → ℝ
  | none => (σ ^ 2 + n)⁻¹ * n
  | some _ => (σ ^ 2 + n)⁻¹ * σ

theorem meanWeight_square_sum (n : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    ∑ i, meanWeight n σ i ^ 2 = (n : ℝ) / (σ ^ 2 + n) := by
  have hq : σ ^ 2 + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  simp only [Fintype.sum_option, meanWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem mean_eq_weighted_rows {d n : ℕ} (σ : ℝ) (v : Joint d n) :
    mean σ v = ∑ i : Option (Fin n), meanWeight n σ i •
      (toLp 2 fun j : Fin d => v (i, j)) := by
  rw [Fintype.sum_option]
  simp only [meanWeight, ← smul_smul, ← Finset.smul_sum, mean, smul_add,
    prior, noise]

theorem mean_gaussian_law (d n : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    (stdGaussian (Joint d n)).map (mean σ) =
      (stdGaussian (E d)).map (fun z => Real.sqrt ((n : ℝ) / (σ ^ 2 + n)) • z) := by
  have hrows := gaussian_rows (ι := Option (Fin n)) (κ := Fin d)
  have h := congrArg (fun μ : Measure (Option (Fin n) → E d) =>
    μ.map (fun x => ∑ i, meanWeight n σ i • x i)) hrows
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    gaussian_weighted_sum, meanWeight_square_sum n σ hσ] at h
  convert h using 1
  congr 1
  funext v
  exact mean_eq_weighted_rows σ v

theorem mean_box_probability (d n : ℕ) (σ : ℝ) (hσ : 0 < σ) (ε : ℝ) :
    stdGaussian (Joint d n) {v | ∀ j, |mean σ v j| ≤ ε} =
      stdGaussian (E d) {z | ∀ j, Real.sqrt ((n : ℝ) / (σ ^ 2 + n)) * |z j| ≤ ε} := by
  have hb : MeasurableSet {z : E d | ∀ j, |z j| ≤ ε} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).measurable.abs measurable_const
  have hh := congrArg (fun μ : Measure (E d) => μ {z | ∀ j, |z j| ≤ ε})
    (mean_gaussian_law d n σ hσ)
  rw [Measure.map_apply (mean_continuous σ).measurable hb,
    Measure.map_apply (by fun_prop) hb] at hh
  simpa only [Set.preimage_ofPred_eq, PiLp.smul_apply, smul_eq_mul,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using hh

end
end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GaussianLowerBound -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

theorem selectedRisk_on_training_measurable {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) : Measurable (fun q : Joint d n × (Fin n → Bool) =>
      selectedRisk g σ ε (prior q.1, trainingData σ q.1 q.2)) := by
  apply (selectedRisk_measurable g hg σ ε).comp
  unfold trainingData zSample prior noise
  fun_prop

/-- Integrate only the measurable witness; the original outer-error integrand stays on the RHS. -/
theorem generated_error_le_expRobErr {d n : ℕ}
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) : experimentLaw d n (generatedEvent g σ ε) ≤ expRobErr g σ ε := by
  have hE := generatedEvent_measurable g hg σ ε
  have hi : Measurable ((generatedEvent g σ ε).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hE
  have hR := selectedRisk_on_training_measurable g hg σ ε
  have he : experimentLaw d n (generatedEvent g σ ε) =
      ∫⁻ v : Joint d n, ∫⁻ labels, selectedRisk g σ ε (prior v, trainingData σ v labels)
        ∂labelsLaw n ∂stdGaussian (Joint d n) := by
    rw [← lintegral_indicator_one hE]
    change (∫⁻ p : Experiment d n, (generatedEvent g σ ε).indicator (fun _ => 1) p
      ∂((stdGaussian (Joint d n)).prod (labelsLaw n)).prod (testNoiseLaw d)) = _
    rw [lintegral_prod (μ := (stdGaussian (Joint d n)).prod (labelsLaw n))
      (ν := testNoiseLaw d) _ hi.aemeasurable]
    have heq : (fun q : Joint d n × (Fin n → Bool) =>
        ∫⁻ t, (generatedEvent g σ ε).indicator (fun _ => 1) (q,t) ∂testNoiseLaw d) =
        (fun q => selectedRisk g σ ε (prior q.1, trainingData σ q.1 q.2)) := by
      rfl
    rw [heq, lintegral_prod _ hR.aemeasurable]
  rw [he, joint_training_lintegral d n σ _ (selectedRisk_measurable g hg σ ε)]
  apply lintegral_mono
  intro θ
  apply lintegral_mono
  intro S
  exact selectedRisk_le_robustErr g hg σ ε θ S

theorem gaussian_error_lower_bound (d n : ℕ)
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun p : (Fin n → E d × Bool) × E d => g p.1 p.2))
    (σ ε : ℝ) (hσ : 0 < σ) :
    (1 / 2 : ℝ≥0∞) *
      stdGaussian (E d) {v | ∀ i, Real.sqrt (n / (σ^2+n)) * |v i| ≤ ε} ≤
        expRobErr g σ ε := by
  rw [← mean_box_probability d n σ hσ ε]
  exact (generated_error_half g hg σ ε hσ).le.trans (generated_error_le_expRobErr g hg σ ε)

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GaussianRoot -/
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem theorem11_robust_error_lower_bound (d n : ℕ)
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun q : (Fin n → E d × Bool) × E d => g q.1 q.2))
    (σ ε : ℝ) (hσ : 0 < σ) (_hε : 0 ≤ ε) :
    (1 / 2 : ℝ≥0∞) *
        stdGaussian (E d) {v | ∀ i, Real.sqrt (n / (σ ^ 2 + n)) * |v i| ≤ ε} ≤
      expRobErr g σ ε := by
  exact RobustGeneralization.GaussLowerProof.gaussian_error_lower_bound d n g hg σ ε hσ

end RobustGeneralization.GaussLower


end

/- Complete checked body: CorollaryParameters -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

theorem scaled_box_radius_le (d n : ℕ) (hd : 2 ≤ d) (σ ε : ℝ)
    (hσ : 0 < σ) (hε : 0 ≤ ε)
    (hn : (n : ℝ) ≤ ε^2*σ^2/(8*Real.log d)) :
    Real.sqrt ((n : ℝ)/(σ^2+n)) * Real.sqrt (8*Real.log d) ≤ ε := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos hdR
  have hq : 0 < σ^2+(n : ℝ) := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← Real.sqrt_mul (div_nonneg hn0 hq.le)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hε, ?_⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hq).mpr
  have hp := (le_div_iff₀ (show 0 < 8*Real.log (d : ℝ) by positivity)).mp hn
  nlinarith [mul_nonneg (sq_nonneg ε) hn0]

theorem gaussian_box_subset_scaled (d n : ℕ) (hd : 2 ≤ d) (σ ε : ℝ)
    (hσ : 0 < σ) (hε : 0 ≤ ε)
    (hn : (n : ℝ) ≤ ε^2*σ^2/(8*Real.log d)) :
    {v : E d | ∀ i, |v i| ≤ Real.sqrt (8*Real.log d)} ⊆
      {v : E d | ∀ i, Real.sqrt (n/(σ^2+n))*|v i| ≤ ε} := by
  intro v hv i
  exact (mul_le_mul_of_nonneg_left (hv i) (Real.sqrt_nonneg _)).trans
    (scaled_box_radius_le d n hd σ ε hσ hε hn)

theorem corollary_zero_dimension (n : ℕ)
    (g : (Fin n → E 0 × Bool) → E 0 → Bool)
    (hg : Measurable (fun q : (Fin n → E 0 × Bool) × E 0 => g q.1 q.2))
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    ENNReal.ofReal ((1-1/(0 : ℝ))*(1/2)) ≤ expRobErr g σ ε := by
  have h := theorem11_robust_error_lower_bound 0 n g hg σ ε hσ hε
  have hbox : stdGaussian (E 0)
      {v | ∀ i, Real.sqrt (n/(σ^2+n))*|v i| ≤ ε} = 1 := by simp
  rw [hbox, mul_one] at h
  simpa using h

lemma ofReal_gap_half (d : ℕ) :
    ENNReal.ofReal ((1-1/(d : ℝ))*(1/2)) =
      (1/2 : ℝ≥0∞)*ENNReal.ofReal (1-1/(d : ℝ)) := by
  rw [mul_comm (1-1/(d : ℝ)), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GaussianCoordinateTails -/
section

open MeasureTheory ProbabilityTheory WithLp RobustGeneralization.GaussLower
open scoped NNReal ENNReal

namespace RobustGeneralization.GaussLowerProof

theorem gaussian_coordinate_law {d : ℕ} (i : Fin d) :
    (stdGaussian (E d)).map (fun v => v i) = gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).map_eq

theorem standard_normal_subgaussian : HasSubgaussianMGF (id : ℝ → ℝ) 1 (gaussianReal 0 1) := by
  constructor
  · intro t
    exact integrable_exp_mul_gaussianReal t
  · intro t
    simp [mgf_id_gaussianReal]

theorem gaussian_coordinate_subgaussian {d : ℕ} (i : Fin d) :
    HasSubgaussianMGF (fun v : E d => v i) 1 (stdGaussian (E d)) := by
  have hm : AEMeasurable (fun v : E d => v i) (stdGaussian (E d)) := by fun_prop
  have h : HasSubgaussianMGF (id : ℝ → ℝ) 1 ((stdGaussian (E d)).map (fun v => v i)) := by
    rw [gaussian_coordinate_law i]
    exact standard_normal_subgaussian
  exact h.of_map hm

theorem gaussian_coordinate_abs_tail {d : ℕ} (i : Fin d) (t : ℝ) (ht : 0 ≤ t) :
    (stdGaussian (E d)).real {v | t < |v i|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  have hp := (gaussian_coordinate_subgaussian i).measure_ge_le ht
  have hn := (gaussian_coordinate_subgaussian i).neg.measure_ge_le ht
  simp only [NNReal.coe_one, mul_one, Pi.neg_apply] at hp hn
  have hs : {v : E d | t < |v i|} ⊆ {v | t ≤ v i} ∪ {v | t ≤ -v i} := by
    intro v hv
    change t < |v i| at hv
    change t ≤ v i ∨ t ≤ -v i
    rcases le_total 0 (v i) with h | h
    · exact Or.inl (by simpa only [abs_of_nonneg h] using hv.le)
    · exact Or.inr (by simpa only [abs_of_nonpos h] using hv.le)
  calc
    _ ≤ (stdGaussian (E d)).real ({v | t ≤ v i} ∪ {v | t ≤ -v i}) := measureReal_mono hs
    _ ≤ (stdGaussian (E d)).real {v | t ≤ v i} +
        (stdGaussian (E d)).real {v | t ≤ -v i} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / 2) + Real.exp (-t ^ 2 / 2) := add_le_add hp hn
    _ = _ := by ring

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: GaussianBoxBound -/
section

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussLower
open scoped ENNReal

namespace RobustGeneralization.GaussLowerProof

theorem gaussian_box_probability_lower (d : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal (1 - 1 / (d : ℝ)) ≤
      stdGaussian (E d) {v | ∀ i, |v i| ≤ Real.sqrt (8 * Real.log d)} := by
  classical
  have hdR : (2 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hdp : (0 : ℝ) < d := by linarith
  have hl : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by linarith)
  let T := Real.sqrt (8 * Real.log d)
  let A : Set (E d) := {v | ∀ i, |v i| ≤ T}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable.abs
      measurable_const
  have hc : Aᶜ = ⋃ i : Fin d, {v : E d | T < |v i|} := by
    ext v
    simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, not_forall, not_le]
  have htail : (stdGaussian (E d)).real Aᶜ ≤ (d : ℝ) * (2 * Real.exp (-T ^ 2 / 2)) := by
    rw [hc]
    calc
      _ ≤ ∑ i : Fin d, (stdGaussian (E d)).real {v | T < |v i|} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _ : Fin d, 2 * Real.exp (-T ^ 2 / 2) :=
        Finset.sum_le_sum fun i _ => gaussian_coordinate_abs_tail i T (Real.sqrt_nonneg _)
      _ = _ := by simp
  have he : Real.exp (-T ^ 2 / 2) = 1 / (d : ℝ) ^ 4 := by
    have hT : T ^ 2 = 8 * Real.log d := Real.sq_sqrt (mul_nonneg (by norm_num) hl)
    rw [hT]
    have hx : -(8 * Real.log (d : ℝ)) / 2 = -Real.log ((d : ℝ) ^ 4) := by
      rw [Real.log_pow]
      ring
    rw [hx, Real.exp_neg, Real.exp_log (pow_pos hdp 4)]
    simp only [one_div]
  rw [he] at htail
  have hb : (d : ℝ) * (2 * (1 / (d : ℝ) ^ 4)) ≤ 1 / d := by
    rw [show (d : ℝ) * (2 * (1 / (d : ℝ) ^ 4)) = (2 * d) / (d : ℝ) ^ 4 by ring]
    apply (div_le_div_iff₀ (pow_pos hdp 4) hdp).mpr
    have hs : (2 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hh := mul_nonneg (sq_nonneg (d : ℝ)) (sub_nonneg.mpr hs)
    nlinarith
  have hsum := probReal_add_probReal_compl (μ := stdGaussian (E d)) hA
  have hreal : 1 - 1 / (d : ℝ) ≤ (stdGaussian (E d)).real A := by
    have := htail.trans hb
    linarith
  have hout := ENNReal.ofReal_le_ofReal hreal
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hout

end RobustGeneralization.GaussLowerProof

end

/- Complete checked body: CorollaryRoot -/
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem corollary23_robust_error_lower_bound (d n : ℕ)
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun q : (Fin n → E d × Bool) × E d => g q.1 q.2))
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε)
    (hn : (n : ℝ) ≤ ε ^ 2 * σ ^ 2 / (8 * Real.log d)) :
    ENNReal.ofReal ((1 - 1 / (d : ℝ)) * (1 / 2)) ≤ expRobErr g σ ε := by
  by_cases hd0 : d = 0
  · subst d
    simpa only [Nat.cast_zero] using
      RobustGeneralization.GaussLowerProof.corollary_zero_dimension n g hg σ ε hσ hε
  by_cases hd1 : d = 1
  · subst d
    simp
  have hd : 2 ≤ d := by omega
  rw [RobustGeneralization.GaussLowerProof.ofReal_gap_half]
  calc
    _ ≤ (1/2 : ℝ≥0∞) * stdGaussian (E d)
        {v | ∀ i, |v i| ≤ Real.sqrt (8*Real.log d)} :=
      mul_le_mul_right (RobustGeneralization.GaussLowerProof.gaussian_box_probability_lower d hd) _
    _ ≤ (1/2 : ℝ≥0∞) * stdGaussian (E d)
        {v | ∀ i, Real.sqrt (n/(σ^2+n))*|v i| ≤ ε} :=
      mul_le_mul_right (measure_mono
        (RobustGeneralization.GaussLowerProof.gaussian_box_subset_scaled d n hd σ ε hσ hε hn)) _
    _ ≤ expRobErr g σ ε := theorem11_robust_error_lower_bound d n g hg σ ε hσ hε

end RobustGeneralization.GaussLower


end

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussLower
open scoped ENNReal

theorem solution (d n : ℕ)
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun q : (Fin n → E d × Bool) × E d => g q.1 q.2))
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε)
    (hn : (n : ℝ) ≤ ε ^ 2 * σ ^ 2 / (8 * Real.log d)) :
    ENNReal.ofReal ((1 - 1 / (d : ℝ)) * (1 / 2)) ≤ expRobErr g σ ε := by
  exact RobustGeneralization.GaussLower.corollary23_robust_error_lower_bound d n g hg σ ε hσ hε hn

#print axioms RobustGeneralization.GaussLower.corollary23_robust_error_lower_bound
#print axioms solution
