-- Prove2me | solution 1 for UniversalSubmod.theorem_1_1_universal_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:58:00.184368+00:00
-- url     : https://prove2.me/submissions/192199b1-479e-4e38-b2f1-e69edcf9abef

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_UniversalSubmod_threshSet
import Theorems.Thm_UniversalSubmod_lemma_2_6
import Theorems.Thm_UniversalSubmod_theorem_2_4
import Theorems.Thm_UniversalSubmod_lemma_2_5
import Theorems.Thm_UniversalSubmod_lattice_count

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Thm11A

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

/-- randomized rounding of `a` to the grid `η ℤ`: integer coordinate -/
noncomputable def ri (η a u : ℝ) : ℤ := ⌊a / η⌋ + if u < Int.fract (a / η) then 1 else 0

/-- rounded vector (grid point) -/
noncomputable def Yv {k : ℕ} (η : ℝ) (z : EuclideanSpace ℝ (Fin k)) (u : Fin k → ℝ) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => η * ((ri η (z j) (u j) : ℤ) : ℝ))

/-- uniform measure on the unit interval -/
noncomputable def rho1 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance rho1_prob : IsProbabilityMeasure rho1 :=
  ⟨by simp [rho1, Measure.restrict_apply_univ]⟩

/-- the Gaussian `N(0, η)` -/
noncomputable def nuG (η : ℝ) : Measure ℝ := gaussianReal 0 (Real.toNNReal η)

/-- its density -/
noncomputable def gp (η : ℝ) (t : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.exp (-(t ^ 2) / (2 * η))

lemma ri_sub (η a u : ℝ) (hη : 0 < η) :
    η * (ri η a u : ℝ) - a
      = η * ((if u < Int.fract (a / η) then (1 : ℝ) else 0) - Int.fract (a / η)) := by
  unfold ri
  have h : a / η = ⌊a / η⌋ + Int.fract (a / η) := (Int.floor_add_fract _).symm
  have h2 : a = η * (a / η) := by field_simp
  push_cast
  split_ifs <;> nlinarith [h, h2]

lemma abs_ri_sub (η a u : ℝ) (hη : 0 < η) : |η * (ri η a u : ℝ) - a| ≤ η := by
  rw [ri_sub η a u hη, abs_mul, abs_of_pos hη]
  have h0 := Int.fract_nonneg (a / η)
  have h1 := Int.fract_lt_one (a / η)
  refine mul_le_of_le_one_right hη.le ?_
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

lemma meas_ri (η a : ℝ) : Measurable (fun u : ℝ => η * ((ri η a u : ℤ) : ℝ)) := by
  unfold ri
  have : Measurable (fun u : ℝ => (if u < Int.fract (a / η) then (1 : ℤ) else 0)) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      measurable_const
  have h2 : Measurable (fun u : ℝ => ⌊a / η⌋ + (if u < Int.fract (a / η) then (1 : ℤ) else 0)) :=
    measurable_const.add this
  exact measurable_const.mul (measurable_from_top.comp h2)

lemma ri_mean (η a : ℝ) (hη : 0 < η) : ∫ u, η * ((ri η a u : ℤ) : ℝ) ∂rho1 = a := by
  have h0 := Int.fract_nonneg (a / η)
  have h1 := Int.fract_lt_one (a / η)
  have hfun : ∀ u : ℝ, η * ((ri η a u : ℤ) : ℝ)
      = η * (⌊a / η⌋ : ℝ) + η * (Set.Iio (Int.fract (a / η))).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    unfold ri
    push_cast
    by_cases h : u < Int.fract (a / η) <;> simp [h, Set.indicator, mul_add]
  simp_rw [hfun]
  have hI : Integrable (fun u : ℝ => η * (Set.Iio (Int.fract (a / η))).indicator
      (fun _ => (1 : ℝ)) u) rho1 :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iio).const_mul η
  rw [integral_add (integrable_const _) hI, integral_const, integral_const_mul,
    integral_indicator_const _ measurableSet_Iio]
  have hm : rho1 (Set.Iio (Int.fract (a / η))) = ENNReal.ofReal (Int.fract (a / η)) := by
    unfold rho1
    rw [Measure.restrict_apply measurableSet_Iio]
    have : Set.Iio (Int.fract (a / η)) ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 (Int.fract (a / η)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨h, h', _⟩; exact ⟨h', h⟩
      · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
    rw [this, Real.volume_Ico]; simp
  have hm' : (rho1.real (Set.Iio (Int.fract (a / η)))) = Int.fract (a / η) := by
    simp [Measure.real, hm, h0]
  simp only [probReal_univ, one_smul, smul_eq_mul, mul_one, hm']
  have h : a / η = ⌊a / η⌋ + Int.fract (a / η) := (Int.floor_add_fract _).symm
  have h2 : a = η * (a / η) := by field_simp
  nlinarith [h, h2]

lemma ri_bound (η a u : ℝ) (hη : 0 < η) : |η * (ri η a u : ℝ)| ≤ |a| + η := by
  have := abs_ri_sub η a u hη
  have h2 := abs_sub_abs_le_abs_sub (η * (ri η a u : ℝ)) a
  linarith

lemma gp_contDiff (η : ℝ) : ContDiff ℝ 1 (gp η) := by
  unfold gp
  fun_prop

lemma gp_nonneg (η : ℝ) (t : ℝ) : 0 ≤ gp η t := by
  unfold gp; positivity

lemma deriv_gp (η : ℝ) (hη : 0 < η) (t : ℝ) :
    deriv (gp η) t = (Real.sqrt (2 * Real.pi * η))⁻¹ *
      (Real.exp (-(t ^ 2) / (2 * η)) * (-(2 * t) / (2 * η))) := by
  unfold gp
  have h : HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2) / (2 * η)))
      (Real.exp (-(t ^ 2) / (2 * η)) * (-(2 * t) / (2 * η))) t := by
    have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2) / (2 * η)) (-(2 * t) / (2 * η)) t := by
      have := ((hasDerivAt_pow 2 t).neg).div_const (2 * η)
      simpa using this
    exact h1.exp
  exact (h.const_mul _).deriv

lemma gp_deriv_bound (η : ℝ) (hη : 0 < η) (t : ℝ) : |deriv (gp η) t| ≤ 1 / η := by
  rw [deriv_gp η hη]
  set c := (Real.sqrt (2 * Real.pi * η))⁻¹ with hc
  have hsq : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hsq2 : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  have hcle : c ≤ (Real.sqrt η)⁻¹ := by
    rw [hc]
    apply inv_anti₀ hsq
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hE : Real.exp (-(t ^ 2) / (2 * η)) * Real.exp (t ^ 2 / (2 * η)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hE0 : 0 < Real.exp (-(t ^ 2) / (2 * η)) := Real.exp_pos _
  -- key: c * |t| ≤ exp (t^2/(2η)) * η ... we show c*|t|/η * exp(-t²/2η) ≤ 1/η
  have hkey : c * |t| ≤ Real.exp (t ^ 2 / (2 * η)) := by
    have h1 : c * |t| ≤ |t| / Real.sqrt η := by
      rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_right hcle (abs_nonneg _)
    have h2 : |t| / Real.sqrt η ≤ 1 + t ^ 2 / (2 * η) := by
      have : (|t| / Real.sqrt η) ^ 2 = t ^ 2 / η := by
        rw [div_pow, hsq2, sq_abs]
      have h3 : (|t| / Real.sqrt η - 1) ^ 2 ≥ 0 := sq_nonneg _
      have h5 : t ^ 2 / (2 * η) = (|t| / Real.sqrt η) ^ 2 / 2 := by
        rw [this]; field_simp
      rw [h5]
      nlinarith [h3]
    have h4 := Real.add_one_le_exp (t ^ 2 / (2 * η))
    linarith
  have habs : |c * (Real.exp (-(t ^ 2) / (2 * η)) * (-(2 * t) / (2 * η)))|
      = c * |t| * Real.exp (-(t ^ 2) / (2 * η)) / η := by
    have : -(2 * t) / (2 * η) = -(t / η) := by field_simp
    rw [this, abs_mul, abs_mul, abs_neg, abs_div, abs_of_nonneg hc0, abs_of_pos hE0,
      abs_of_pos hη]
    ring
  rw [habs, div_le_div_iff_of_pos_right hη]
  calc c * |t| * Real.exp (-(t ^ 2) / (2 * η))
      ≤ Real.exp (t ^ 2 / (2 * η)) * Real.exp (-(t ^ 2) / (2 * η)) :=
        mul_le_mul_of_nonneg_right hkey hE0.le
    _ = 1 := by rw [mul_comm]; exact hE

lemma nuG_eq (η : ℝ) (hη : 0 < η) :
    nuG η = volume.withDensity (fun t => ENNReal.ofReal (gp η t)) := by
  have hne : Real.toNNReal η ≠ 0 := by
    intro h
    have := Real.toNNReal_eq_zero.1 h
    linarith
  unfold nuG
  rw [gaussianReal_of_var_ne_zero _ hne]
  congr 1
  funext t
  simp only [gaussianPDF, gaussianPDFReal, gp, Real.coe_toNNReal _ hη.le, sub_zero]

instance nuG_prob (η : ℝ) : IsProbabilityMeasure (nuG η) := by
  unfold nuG; infer_instance

lemma meas_comp {α : Type*} [MeasurableSpace α] {n : ℕ} (φ : α → Finset (Fin n))
    (hφ : ∀ i, MeasurableSet {a | i ∈ φ a}) (f : Finset (Fin n) → ℝ) :
    Measurable (fun a => f (φ a)) := by
  classical
  have h : (fun a => f (φ a)) = fun a => ∑ S : Finset (Fin n), if φ a = S then f S else 0 := by
    funext a
    rw [Finset.sum_eq_single (φ a)]
    · simp
    · intro S _ hS; simp [Ne.symm hS]
    · simp
  rw [h]
  refine Finset.measurable_sum _ (fun S _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {a | φ a = S} = ⋂ i, {a | i ∈ φ a ↔ i ∈ S} := by
    ext a; simp [Finset.ext_iff]
  rw [this]
  refine MeasurableSet.iInter (fun i => ?_)
  by_cases hi : i ∈ S
  · simpa [hi] using hφ i
  · have e : {a | i ∈ φ a ↔ i ∈ S} = {a | i ∈ φ a}ᶜ := by ext a; simp [hi]
    rw [e]; exact (hφ i).compl

/-- transfer independence along the first projection of a product -/
lemma iIndep_fst {ι : Type*} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ι → Ω → ℝ) (hX : iIndepFun X μ) :
    iIndepFun (fun i (ω : Ω × Ω') => X i ω.1) (μ.prod ν) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hX ⊢
  intro S sets hsets
  have h1 : ⋂ i ∈ S, (fun ω : Ω × Ω' => X i ω.1) ⁻¹' sets i
      = (⋂ i ∈ S, X i ⁻¹' sets i) ×ˢ (Set.univ : Set Ω') := by
    ext ω; simp
  have h2 : ∀ i, (fun ω : Ω × Ω' => X i ω.1) ⁻¹' sets i = (X i ⁻¹' sets i) ×ˢ (Set.univ : Set Ω') := by
    intro i; ext ω; simp
  rw [h1, Measure.prod_prod]
  simp only [h2, Measure.prod_prod, measure_univ, mul_one]
  exact hX S hsets

lemma meas_thresh_t {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (z : EuclideanSpace ℝ (Fin k))
    (f : Finset (Fin n) → ℝ) : Measurable (fun t : ℝ => f (threshSet v z t)) := by
  refine meas_comp (fun t : ℝ => threshSet v z t) (fun i => ?_) f
  simp only [threshSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact measurableSet_le measurable_id measurable_const

lemma meas_Yv {k : ℕ} (η : ℝ) (z : EuclideanSpace ℝ (Fin k)) :
    Measurable (fun u : Fin k → ℝ => Yv η z u) := by
  unfold Yv
  exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp
    (measurable_pi_lambda _ (fun j => (meas_ri η (z j)).comp (measurable_pi_apply j)))

theorem step1 {n k : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (z : EuclideanSpace ℝ (Fin k)) (η : ℝ) (hη : 0 < η) :
    ∫ t, f (threshSet v z t) ∂(nuG η) - OPT f * (1 / η) * η ^ 2 ≤
      ∫ ω : (Fin k → ℝ) × ℝ, f (threshSet v (Yv η z ω.1) ω.2)
        ∂((Measure.pi (fun _ : Fin k => rho1)).prod (nuG η)) := by
  set P : Measure ((Fin k → ℝ) × ℝ) := (Measure.pi (fun _ : Fin k => rho1)).prod (nuG η) with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hfst : ∀ j : Fin k, MeasurePreserving (fun ω : (Fin k → ℝ) × ℝ => ω.1 j) P rho1 := fun j =>
    (measurePreserving_eval (fun _ : Fin k => rho1) j).comp measurePreserving_fst
  have hYm : Measurable (fun ω : (Fin k → ℝ) × ℝ => Yv η z ω.1) := (meas_Yv η z).comp measurable_fst
  have hlaw : P.map (fun ω : (Fin k → ℝ) × ℝ => ω.2)
      = volume.withDensity (fun t => ENNReal.ofReal (gp η t)) := by
    rw [hP, Measure.map_snd_prod]; simp [nuG_eq η hη]
  have h := UniversalSubmod.lemma_2_6 f hf0 hf v hv z (η ^ 2) (by positivity) P
    (fun ω => Yv η z ω.1) hYm
    (by
      have h1 := iIndepFun_pi (μ := fun _ : Fin k => rho1)
        (X := fun j => fun x : ℝ => η * ((ri η (z j) x : ℤ) : ℝ))
        (fun j => (meas_ri η (z j)).aemeasurable)
      have h2 := iIndep_fst (Measure.pi (fun _ : Fin k => rho1)) (nuG η) _ h1
      exact h2)
    (by
      intro j
      refine MemLp.of_bound ?_ (|z j| + η) (ae_of_all _ fun ω => ?_)
      · exact ((meas_ri η (z j)).comp ((measurable_pi_apply j).comp measurable_fst)).aestronglyMeasurable
      · simpa [Yv, Real.norm_eq_abs] using ri_bound η (z j) (ω.1 j) hη)
    (by
      intro j
      have h3 : ∫ ω : (Fin k → ℝ) × ℝ, (Yv η z ω.1) j ∂P
          = ∫ u, η * ((ri η (z j) u : ℤ) : ℝ) ∂rho1 := by
        have := integral_map (μ := P) (φ := fun ω : (Fin k → ℝ) × ℝ => ω.1 j)
          (hfst j).measurable.aemeasurable (meas_ri η (z j)).aestronglyMeasurable
        rw [(hfst j).map_eq] at this
        exact this.symm
      rw [h3]; exact ri_mean η (z j) hη)
    (by
      intro j
      have hb : ∀ ω : (Fin k → ℝ) × ℝ, ((Yv η z ω.1) j - z j) ^ 2 ≤ η ^ 2 := by
        intro ω
        have := abs_ri_sub η (z j) (ω.1 j) hη
        have h5 : |(Yv η z ω.1) j - z j| ≤ η := this
        nlinarith [abs_le.1 h5]
      calc ∫ ω : (Fin k → ℝ) × ℝ, ((Yv η z ω.1) j - z j) ^ 2 ∂P
          ≤ ∫ ω : (Fin k → ℝ) × ℝ, η ^ 2 ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) (integrable_const _)
              (ae_of_all _ hb)
        _ = η ^ 2 := by simp)
    (fun ω => ω.2) measurable_snd
    (indepFun_prod (μ := Measure.pi (fun _ : Fin k => rho1)) (ν := nuG η)
      (X := fun u => Yv η z u) (Y := fun t : ℝ => t) (meas_Yv η z) measurable_id)
    (gp η) (gp_contDiff η) (gp_nonneg η) hlaw (1 / η) (gp_deriv_bound η hη)
  have hsnd : ∫ ω : (Fin k → ℝ) × ℝ, f (threshSet v z ω.2) ∂P
      = ∫ t, f (threshSet v z t) ∂(nuG η) := by
    have := integral_map (μ := P) (φ := fun ω : (Fin k → ℝ) × ℝ => ω.2) measurable_snd.aemeasurable
      (meas_thresh_t v z f).aestronglyMeasurable
    rw [hP, Measure.map_snd_prod] at this
    simp at this
    rw [hP]; exact this.symm
  rw [← hsnd]
  exact h

end UniversalSubmod.Dev.Thm11A
end

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Thm11B

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared UniversalSubmod.Dev.Thm11A
open scoped RealInnerProductSpace

lemma gauss_second : ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (memLp_id_gaussianReal (μ := 0) (v := 1) 2).aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

lemma gauss_int_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  simpa using this

lemma second_moment (k : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin k))) ∧
    ∫ z : EuclideanSpace ℝ (Fin k), ‖z‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) = k := by
  rw [← map_pi_eq_stdGaussian]
  have hm : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable
  have hev : ∀ j : Fin k, ∫ x : Fin k → ℝ, (x j) ^ 2 ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = 1 := by
    intro j
    have := integral_map (μ := Measure.pi fun _ : Fin k => gaussianReal 0 1)
      (φ := fun x : Fin k → ℝ => x j) (measurable_pi_apply j).aemeasurable
      (f := fun y : ℝ => y ^ 2) (by fun_prop)
    rw [(measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) j).map_eq] at this
    rw [← this]; exact gauss_second
  have hint : ∀ j : Fin k, Integrable (fun x : Fin k → ℝ => (x j) ^ 2)
      (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
    intro j
    have := (integrable_map_measure (μ := Measure.pi fun _ : Fin k => gaussianReal 0 1)
      (f := fun x : Fin k → ℝ => x j) (g := fun y : ℝ => y ^ 2) (by fun_prop)
      (measurable_pi_apply j).aemeasurable).1
    rw [(measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) j).map_eq] at this
    exact this gauss_int_sq
  have hnorm : (fun x : Fin k → ℝ => ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))‖ ^ 2)
      = fun x => ∑ j, (x j) ^ 2 := by
    funext x; rw [EuclideanSpace.real_norm_sq_eq]
  constructor
  · rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
    show Integrable (fun x : Fin k → ℝ => ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))‖ ^ 2) _
    rw [hnorm]
    exact integrable_finsetSum _ (fun j _ => hint j)
  · rw [integral_map hm.aemeasurable (by fun_prop)]
    show ∫ x : Fin k → ℝ, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))‖ ^ 2 ∂_ = _
    rw [hnorm, integral_finsetSum _ (fun j _ => hint j)]
    simp [hev]

/-- Markov for the Gaussian norm -/
lemma markov_norm (k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | Real.sqrt (k / η) < ‖z‖} ≤ η := by
  obtain ⟨hi, hv⟩ := second_moment k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hs2 : Real.sqrt (k / η) ^ 2 = k / η := Real.sq_sqrt (by positivity)
  have hM := mul_meas_ge_le_integral_of_nonneg
    (μ := stdGaussian (EuclideanSpace ℝ (Fin k)))
    (f := fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2)
    (ae_of_all _ fun z => sq_nonneg _) hi (k / η)
  rw [hv] at hM
  have hsub : {z : EuclideanSpace ℝ (Fin k) | Real.sqrt (k / η) < ‖z‖}
      ⊆ {z | k / η ≤ ‖z‖ ^ 2} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [← hs2]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hz.le 2
  have h1 := measureReal_mono (μ := stdGaussian (EuclideanSpace ℝ (Fin k))) hsub
  have hpos : 0 < k / η := by positivity
  have h2 : k / η * (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | Real.sqrt (k / η) < ‖z‖} ≤ k :=
    le_trans (mul_le_mul_of_nonneg_left h1 hpos.le) hM
  rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
  nlinarith

/-- the rounded vector is within `η √k` of `z` -/
lemma norm_Yv_sub {k : ℕ} (η : ℝ) (hη : 0 < η) (z : EuclideanSpace ℝ (Fin k)) (u : Fin k → ℝ) :
    ‖Yv η z u - z‖ ≤ η * Real.sqrt k := by
  have h1 : ‖Yv η z u - z‖ ^ 2 ≤ (η * Real.sqrt k) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    have : ∀ j : Fin k, ((Yv η z u - z) j) ^ 2 ≤ η ^ 2 := by
      intro j
      have h := abs_ri_sub η (z j) (u j) hη
      have h' : |(Yv η z u - z) j| ≤ η := h
      nlinarith [abs_le.1 h']
    calc ∑ j, ((Yv η z u - z) j) ^ 2 ≤ ∑ _j : Fin k, η ^ 2 := Finset.sum_le_sum (fun j _ => this j)
      _ = η ^ 2 * k := by simp [mul_comm]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h1

lemma sum_ri_le {k : ℕ} (η : ℝ) (hη : 0 < η) (z : EuclideanSpace ℝ (Fin k)) (u : Fin k → ℝ)
    (s : ℝ) (hz : ‖z‖ ≤ s) :
    ∑ j, (((ri η (z j) (u j) : ℤ) : ℝ)) ^ 2 ≤ ((s + η * Real.sqrt k) / η) ^ 2 := by
  have hn : ‖Yv η z u‖ ≤ s + η * Real.sqrt k := by
    calc ‖Yv η z u‖ = ‖(Yv η z u - z) + z‖ := by simp
      _ ≤ ‖Yv η z u - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_Yv_sub η hη z u]
  have h2 : ‖Yv η z u‖ ^ 2 = η ^ 2 * ∑ j, (((ri η (z j) (u j) : ℤ) : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Yv, mul_pow]
  have h3 : ‖Yv η z u‖ ^ 2 ≤ (s + η * Real.sqrt k) ^ 2 := by
    have : 0 ≤ ‖Yv η z u‖ := norm_nonneg _
    exact pow_le_pow_left₀ this hn 2
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith

lemma f_bdd {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : |f S| ≤ ∑ T, |f T| :=
  Finset.single_le_sum (f := fun T => |f T|) (fun T _ => abs_nonneg _) (Finset.mem_univ S)

lemma avg_bound {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (hvv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ η)
    (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) :
    (1 / 4 - η) * OPT f ≤ ∫ z, (∫ t, f (threshSet v z t) ∂(nuG η))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hμ
  haveI := nuG_prob η
  have hmapsnd : (μ.prod (nuG η)).map Prod.snd = nuG η := by
    rw [Measure.map_snd_prod]; simp
  have hmapfst : (μ.prod (nuG η)).map Prod.fst = μ := by
    rw [Measure.map_fst_prod]; simp
  have hidm : MemLp (id : ℝ → ℝ) 2 (nuG η) := by
    unfold nuG; exact memLp_id_gaussianReal 2
  have hT2 : MemLp (fun ω : EuclideanSpace ℝ (Fin k) × ℝ => ω.2) 2 (μ.prod (nuG η)) := by
    have h0 : MemLp (id : ℝ → ℝ) 2 ((μ.prod (nuG η)).map Prod.snd) := by rw [hmapsnd]; exact hidm
    exact (memLp_map_measure_iff aestronglyMeasurable_id measurable_snd.aemeasurable).1 h0
  have hT0 : ∫ ω : EuclideanSpace ℝ (Fin k) × ℝ, ω.2 ∂(μ.prod (nuG η)) = 0 := by
    have := integral_map (μ := μ.prod (nuG η)) (φ := Prod.snd) measurable_snd.aemeasurable
      (f := (id : ℝ → ℝ)) aestronglyMeasurable_id
    rw [hmapsnd] at this
    have h2 : ∫ y : ℝ, id y ∂(nuG η) = 0 := by unfold nuG; exact integral_id_gaussianReal
    rw [h2] at this
    exact this.symm
  have hTvar : variance (fun ω : EuclideanSpace ℝ (Fin k) × ℝ => ω.2) (μ.prod (nuG η)) ≤ η := by
    have := variance_map (X := (id : ℝ → ℝ)) (Y := Prod.snd) (μ := μ.prod (nuG η))
      (by rw [hmapsnd]; exact aemeasurable_id) measurable_snd.aemeasurable
    rw [hmapsnd] at this
    have h3 : variance (id : ℝ → ℝ) (nuG η) = η := by
      unfold nuG; rw [variance_id_gaussianReal, Real.coe_toNNReal _ hη.le]
    have h4 : (id ∘ Prod.snd : EuclideanSpace ℝ (Fin k) × ℝ → ℝ) = fun ω => ω.2 := rfl
    rw [h4, h3] at this
    exact this.symm.le
  have h24 := UniversalSubmod.theorem_2_4 n k hn hk η hη hη2 v hv hvv (μ.prod (nuG η))
    (fun ω => ω.1) measurable_fst hmapfst
    (fun ω => ω.2) measurable_snd
    (indepFun_prod (μ := μ) (ν := nuG η) (X := fun z : EuclideanSpace ℝ (Fin k) => z)
      (Y := fun t : ℝ => t) measurable_id measurable_id) hT2 hT0 hTvar f hf0 hf
  have hH : Measurable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (threshSet v p.1 p.2)) := by
    refine meas_comp (fun p : EuclideanSpace ℝ (Fin k) × ℝ => threshSet v p.1 p.2) (fun i => ?_) f
    simp only [threshSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le measurable_snd (by fun_prop)
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (threshSet v p.1 p.2))
      (μ.prod (nuG η)) :=
    Integrable.of_bound hH.aestronglyMeasurable (∑ T, |f T|)
      (ae_of_all _ (fun p => by simpa [Real.norm_eq_abs] using f_bdd f _))
  rw [integral_prod _ hint] at h24
  exact h24

theorem core {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (hvv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ η)
    (F : Finset (Finset (Fin n)))
    (hF : ∀ y : Fin k → ℤ,
      ∑ i, ((y i : ℤ) : ℝ) ^ 2 ≤ ((Real.sqrt (k / η) + η * Real.sqrt k) / η) ^ 2 →
        ∀ t : ℝ, threshSet v (WithLp.toLp 2 (fun i => η * ((y i : ℤ) : ℝ))) t ∈ F)
    (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) :
    ∃ S ∈ F, (1 / 4 - 3 * η) * OPT f ≤ f S := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hμ
  haveI := nuG_prob η
  have hne : F.Nonempty := ⟨_, hF 0 (by simp; positivity) 0⟩
  obtain ⟨S0, hS0⟩ := hne
  set m := F.sup' ⟨S0, hS0⟩ f with hm
  set M := OPT f with hMdef
  have hm0 : 0 ≤ m := (hf0 S0).trans (Finset.le_sup' f hS0)
  have hfM : ∀ S, f S ≤ M := fun S => Finset.le_sup' f (Finset.mem_univ S)
  have hM0 : 0 ≤ M := (hf0 ∅).trans (hfM ∅)
  set s := Real.sqrt (k / η) with hs
  set B : Set (EuclideanSpace ℝ (Fin k)) := {z | s < ‖z‖} with hB
  have hBm : MeasurableSet B := measurableSet_lt measurable_const measurable_norm
  have hpt : ∀ z : EuclideanSpace ℝ (Fin k), (∫ t, f (threshSet v z t) ∂(nuG η))
      ≤ m + M * η + M * B.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have h1 := Dev.Thm11A.step1 f hf0 hf v hv z η hη
    set P := (Measure.pi (fun _ : Fin k => rho1)).prod (nuG η) with hP
    haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
    have h2 : ∫ ω : (Fin k → ℝ) × ℝ, f (threshSet v (Yv η z ω.1) ω.2) ∂P
        ≤ m + M * B.indicator (fun _ => (1 : ℝ)) z := by
      by_cases hz : z ∈ B
      · have : ∫ ω : (Fin k → ℝ) × ℝ, f (threshSet v (Yv η z ω.1) ω.2) ∂P ≤ ∫ _ω : (Fin k → ℝ) × ℝ, M ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => hf0 _) (integrable_const _)
            (ae_of_all _ fun ω => hfM _)
        simp only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul] at this
        simp only [Set.indicator_of_mem hz]
        linarith
      · have hzs : ‖z‖ ≤ s := not_lt.1 hz
        have : ∫ ω : (Fin k → ℝ) × ℝ, f (threshSet v (Yv η z ω.1) ω.2) ∂P ≤ ∫ _ω : (Fin k → ℝ) × ℝ, m ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => hf0 _) (integrable_const _)
            (ae_of_all _ fun ω => Finset.le_sup' f
              (hF (fun j => ri η (z j) (ω.1 j)) (sum_ri_le η hη z ω.1 s hzs) ω.2))
        simp only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul] at this
        simp only [Set.indicator_of_notMem hz]
        linarith
    have h3 : OPT f * (1 / η) * η ^ 2 = M * η := by rw [hMdef]; field_simp
    rw [h3] at h1
    linarith
  have hRint : Integrable (fun z : EuclideanSpace ℝ (Fin k) =>
      m + M * η + M * B.indicator (fun _ => (1 : ℝ)) z) μ :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hBm).const_mul M)
  have hJint : ∫ z, (∫ t, f (threshSet v z t) ∂(nuG η)) ∂μ
      ≤ ∫ z, (m + M * η + M * B.indicator (fun _ => (1 : ℝ)) z) ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ fun z => integral_nonneg fun t => hf0 _) hRint
      (ae_of_all _ hpt)
  have hRval : ∫ z, (m + M * η + M * B.indicator (fun _ => (1 : ℝ)) z) ∂μ
      = m + M * η + M * μ.real B := by
    rw [integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator hBm).const_mul M),
      integral_const, integral_const_mul, integral_indicator_const _ hBm]
    simp
  have hmk : μ.real B ≤ η := markov_norm k hk η hη
  have hav := avg_bound hn hk η hη hη2 v hv hvv f hf0 hf
  have hmax : (1 / 4 - 3 * η) * M ≤ m := by
    have := mul_le_mul_of_nonneg_left hmk hM0
    nlinarith
  obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup' ⟨S0, hS0⟩ f
  exact ⟨S, hS, hSeq ▸ hmax⟩

end UniversalSubmod.Dev.Thm11B
end

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Thm11C

open MeasureTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

open Classical in
/-- one threshold chain has at most `n+1` distinct sets -/
lemma chain_card {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin k)) :
    (Finset.univ.filter (fun S : Finset (Fin n) => ∃ t : ℝ, threshSet v w t = S)).card ≤ n + 1 := by
  have hsub : ∀ t1 t2 : ℝ, t1 ≤ t2 → threshSet v w t2 ⊆ threshSet v w t1 := by
    intro t1 t2 h i hi
    simp only [threshSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  have := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (fun S : Finset (Fin n) => ∃ t : ℝ, threshSet v w t = S))
    (t := Finset.range (n + 1)) Finset.card
    (fun S _ => Finset.mem_range.2 (Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)))
    (by
      intro S1 h1 S2 h2 heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h1 h2
      obtain ⟨t1, rfl⟩ := h1
      obtain ⟨t2, rfl⟩ := h2
      have heq' : (threshSet v w t1).card = (threshSet v w t2).card := heq
      rcases le_total t1 t2 with h | h
      · exact (Finset.eq_of_subset_of_card_le (hsub t1 t2 h) (by omega)).symm
      · exact Finset.eq_of_subset_of_card_le (hsub t2 t1 h) (by omega))
  simpa using this

open Classical in
lemma exists_family {n k : ℕ} (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) :
    ∃ F : Finset (Finset (Fin n)),
      (F.card : ℝ) ≤ (n + 1 : ℝ) * (2 * ((Real.sqrt (k / η) + η * Real.sqrt k) / η) *
        Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ^ k ∧
      ∀ y : Fin k → ℤ,
        ∑ i, ((y i : ℤ) : ℝ) ^ 2 ≤ ((Real.sqrt (k / η) + η * Real.sqrt k) / η) ^ 2 →
          ∀ t : ℝ, threshSet v (WithLp.toLp 2 (fun i => η * ((y i : ℤ) : ℝ))) t ∈ F := by
  set ρ := (Real.sqrt (k / η) + η * Real.sqrt k) / η with hρ
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hρk : Real.sqrt k / 2 ≤ ρ := by
    have h1 : Real.sqrt k ≤ Real.sqrt (k / η) :=
      Real.sqrt_le_sqrt (le_div_self hkpos.le hη hη1)
    have h2 : 0 ≤ η * Real.sqrt k := by positivity
    have h3 : Real.sqrt (k / η) / η ≤ ρ := by
      rw [hρ]; exact div_le_div_of_nonneg_right (by linarith) hη.le
    have h4 : Real.sqrt k ≤ Real.sqrt (k / η) / η := by
      calc Real.sqrt k ≤ Real.sqrt (k / η) := h1
        _ ≤ Real.sqrt (k / η) / η := le_div_self (Real.sqrt_nonneg _) hη hη1
    have : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
    linarith
  obtain ⟨hfin, hc1, hc2, hc3⟩ := UniversalSubmod.lattice_count k hk ρ hρk
  set Bset : Set (Fin k → ℤ) := {y | ∑ i, ((y i : ℤ) : ℝ) ^ 2 ≤ ρ ^ 2} with hBset
  set L := hfin.toFinset with hL
  refine ⟨L.biUnion (fun y => Finset.univ.filter (fun S : Finset (Fin n) =>
      ∃ t : ℝ, threshSet v (WithLp.toLp 2 (fun i => η * ((y i : ℤ) : ℝ))) t = S)), ?_, ?_⟩
  · have h1 : (L.biUnion (fun y => Finset.univ.filter (fun S : Finset (Fin n) =>
        ∃ t : ℝ, threshSet v (WithLp.toLp 2 (fun i => η * ((y i : ℤ) : ℝ))) t = S))).card
        ≤ L.card * (n + 1) := by
      refine Finset.card_biUnion_le.trans ?_
      calc _ ≤ ∑ _y ∈ L, (n + 1) := Finset.sum_le_sum (fun y _ => chain_card v _)
        _ = L.card * (n + 1) := by simp
    have h2 : (L.card : ℝ) = (Bset.ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card Bset hfin]
    have h3 : (Bset.ncard : ℝ) ≤ (2 * ρ * Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ^ k := by
      rw [← hc3]; exact hc1.trans (mul_le_mul_of_nonneg_left hc2 (by positivity))
    calc ((L.biUnion _).card : ℝ) ≤ ((L.card * (n + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (L.card : ℝ) * (n + 1) := by push_cast; ring
      _ ≤ _ := by rw [h2, mul_comm]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
  · intro y hy t
    rw [Finset.mem_biUnion]
    refine ⟨y, ?_, ?_⟩
    · rw [hL, Set.Finite.mem_toFinset]; exact hy
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨t, rfl⟩

lemma A_bound {k : ℕ} (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    2 * ((Real.sqrt (k / η) + η * Real.sqrt k) / η) * Real.sqrt (2 * Real.pi * Real.exp 1 / k)
      ≤ 20 / η ^ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hX : 2 * Real.pi * Real.exp 1 ≤ 25 := by
    have h1 := Real.pi_lt_d2
    have h2 := Real.exp_one_lt_d9
    have h3 := Real.pi_pos
    have h4 := Real.exp_pos 1
    nlinarith
  have hX0 : 0 ≤ 2 * Real.pi * Real.exp 1 := by positivity
  have hac : Real.sqrt (k / η) * Real.sqrt (2 * Real.pi * Real.exp 1 / k) ≤ 5 / η := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    have e : (k : ℝ) / η * (2 * Real.pi * Real.exp 1 / k) = 2 * Real.pi * Real.exp 1 / η := by
      field_simp
    rw [e, div_pow, div_le_div_iff₀ hη (by positivity)]
    nlinarith [mul_nonneg hX0 hη.le, mul_le_mul_of_nonneg_right hX hη.le]
  have hbc : Real.sqrt k * Real.sqrt (2 * Real.pi * Real.exp 1 / k) ≤ 5 := by
    rw [← Real.sqrt_mul hkpos.le]
    have e : (k : ℝ) * (2 * Real.pi * Real.exp 1 / k) = 2 * Real.pi * Real.exp 1 := by
      field_simp
    rw [e]
    apply Real.sqrt_le_iff.2
    exact ⟨by norm_num, by nlinarith⟩
  have hbc' : η * Real.sqrt k * Real.sqrt (2 * Real.pi * Real.exp 1 / k) ≤ 5 / η := by
    rw [mul_assoc]
    calc η * (Real.sqrt k * Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ≤ η * 5 :=
          mul_le_mul_of_nonneg_left hbc hη.le
      _ ≤ 5 / η := by
          rw [le_div_iff₀ hη]; nlinarith
  have : 2 * ((Real.sqrt (k / η) + η * Real.sqrt k) / η) * Real.sqrt (2 * Real.pi * Real.exp 1 / k)
      = 2 / η * (Real.sqrt (k / η) * Real.sqrt (2 * Real.pi * Real.exp 1 / k)
        + η * Real.sqrt k * Real.sqrt (2 * Real.pi * Real.exp 1 / k)) := by ring
  rw [this]
  calc 2 / η * (_ + _) ≤ 2 / η * (5 / η + 5 / η) :=
        mul_le_mul_of_nonneg_left (add_le_add hac hbc') (by positivity)
    _ = 20 / η ^ 2 := by field_simp; ring

lemma final_bound (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4) (n k : ℕ) (hn : 2 ≤ n)
    (hk : (k : ℝ) ≤ 45 * (1 / ε ^ 2) * Real.log n) (A : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 180 / ε ^ 2) :
    ((n : ℝ) + 1) * A ^ k ≤ (n : ℝ) ^ (300 * (1 / ε ^ 2) * Real.log (1 / ε)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hinv : 4 < 1 / ε := by
    rw [lt_div_iff₀ hε0]; linarith
  have hL : 1 ≤ Real.log (1 / ε) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have he2 : 16 ≤ 1 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  set L := Real.log (1 / ε) with hLdef
  set e2 := 1 / ε ^ 2 with he2def
  have hA6 : A ≤ (1 / ε) ^ 6 := by
    refine hA.trans ?_
    have h4 : 256 ≤ (1 / ε) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hinv.le 4]
    have : (1 / ε) ^ 6 = (1 / ε) ^ 4 * (1 / ε ^ 2) := by field_simp
    rw [this, div_eq_mul_one_div]
    have : 0 ≤ 1 / ε ^ 2 := by positivity
    nlinarith
  have h1 : A ^ k ≤ ((1 / ε) ^ 6) ^ k := pow_le_pow_left₀ hA0 hA6 k
  have hexp : (1 / ε) = Real.exp L := (Real.exp_log (by positivity)).symm
  have h2 : ((1 / ε) ^ 6) ^ k = Real.exp (6 * k * L) := by
    rw [hexp, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have h3 : (n : ℝ) + 1 ≤ Real.exp (2 * Real.log n) := by
    rw [show 2 * Real.log n = Real.log n + Real.log n by ring, Real.exp_add, Real.exp_log hn0]
    nlinarith
  have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hQ : 1 ≤ e2 * L := by nlinarith
  have hexpo : 2 * Real.log n + 6 * k * L ≤ Real.log n * (300 * e2 * L) := by
    have a1 : 6 * (k : ℝ) * L ≤ 6 * (45 * e2 * Real.log n) * L := by
      have : 0 ≤ L := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hk this]
    have a2 : 2 * Real.log n ≤ 2 * (e2 * L) * Real.log n := by
      nlinarith [mul_le_mul_of_nonneg_right hQ hlogn.le]
    nlinarith [a1, a2]
  rw [Real.rpow_def_of_pos hn0]
  calc ((n : ℝ) + 1) * A ^ k ≤ Real.exp (2 * Real.log n) * Real.exp (6 * k * L) := by
        rw [← h2]
        exact mul_le_mul h3 h1 (pow_nonneg hA0 k) (Real.exp_pos _).le
    _ = Real.exp (2 * Real.log n + 6 * k * L) := by rw [Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.2 hexpo

/-- the fallback family: everything but the full set -/
lemma fallback {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
    (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) :
    ∃ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ,
      (1 / 4 - ε) * OPT f ≤ f S := by
  classical
  have hO0 : 0 ≤ OPT f := (hf0 ∅).trans (Finset.le_sup' f (Finset.mem_univ ∅))
  obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Finset (Fin n))) f
  have hOPT : OPT f = f S := hS
  by_cases hSu : S = Finset.univ
  · subst hSu
    let i0 : Fin n := ⟨0, by omega⟩
    let j0 : Fin n := ⟨1, by omega⟩
    have hij : i0 ≠ j0 := by simp [i0, j0, Fin.ext_iff]
    have h := hf {i0} {i0}ᶜ
    have hu : ({i0} : Finset (Fin n)) ∪ {i0}ᶜ = Finset.univ := by simp
    have hi : ({i0} : Finset (Fin n)) ∩ {i0}ᶜ = ∅ := by simp
    rw [hu, hi] at h
    have h0 := hf0 (∅ : Finset (Fin n))
    have hA : ({i0} : Finset (Fin n)) ∈ (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
      intro hh
      have : j0 ∈ ({i0} : Finset (Fin n)) := by rw [hh]; exact Finset.mem_univ _
      simp at this; exact hij this.symm
    have hB : ({i0} : Finset (Fin n))ᶜ ∈ (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
      intro hh
      have : i0 ∈ ({i0} : Finset (Fin n))ᶜ := by rw [hh]; exact Finset.mem_univ _
      simp at this
    rw [hOPT]
    have hU0 := hf0 Finset.univ
    have hε' := mul_nonneg hε0.le hU0
    by_cases hc : f {i0} ≥ f {i0}ᶜ
    · exact ⟨_, hA, by nlinarith⟩
    · exact ⟨_, hB, by nlinarith⟩
  · refine ⟨S, by simp [hSu], ?_⟩
    rw [← hOPT]
    nlinarith [mul_nonneg hε0.le hO0]

end UniversalSubmod.Dev.Thm11C

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

theorem chk_theorem_1_1_universal_family :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∀ n : ℕ, 2 ≤ n →
      ∃ F : Finset (Finset (Fin n)),
        F ≠ Finset.univ ∧
        (F.card : ℝ) ≤ (n : ℝ) ^ (C * (1 / ε ^ 2) * Real.log (1 / ε)) ∧
        ∀ f : Finset (Fin n) → ℝ, (∀ S, 0 ≤ f S) → Submodular f →
          ∃ S ∈ F, (1 / 4 - ε) * OPT f ≤ f S := by
  classical
  refine ⟨300, ?_⟩
  intro ε hε0 hε1 n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hη : 0 < ε / 3 := by positivity
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  set η := ε / 3 with hηdef
  set k := ⌈4 / η ^ 2 * Real.log n⌉₊ with hkdef
  have hkpos : 0 < k := Nat.ceil_pos.2 (by positivity)
  have hk1 : 1 ≤ k := hkpos
  have hkn : 4 / η ^ 2 * Real.log n ≤ (k : ℝ) := Nat.le_ceil _
  obtain ⟨v, hv, hvv⟩ := UniversalSubmod.lemma_2_5 n (by omega) η hη k hkpos hkn
  obtain ⟨F, hcard, hF⟩ := Dev.Thm11C.exists_family (n := n) hk1 η hη (by linarith) v
  have hkle : (k : ℝ) ≤ 45 * (1 / ε ^ 2) * Real.log n := by
    have h1 : (k : ℝ) < 4 / η ^ 2 * Real.log n + 1 := Nat.ceil_lt_add_one (by positivity)
    have hl2 : (0.69 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hlogn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
    have he2 : 16 ≤ 1 / ε ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have e : 4 / η ^ 2 = 36 * (1 / ε ^ 2) := by rw [hηdef]; field_simp; ring
    rw [e] at h1
    nlinarith [mul_le_mul he2 (le_of_lt (lt_of_lt_of_le hl2 hlogn2)) (by norm_num) (by positivity)]
  have hA := Dev.Thm11C.A_bound hk1 η hη (by linarith)
  have hA0 : 0 ≤ 2 * ((Real.sqrt (k / η) + η * Real.sqrt k) / η) *
      Real.sqrt (2 * Real.pi * Real.exp 1 / k) := by positivity
  have h180 : 20 / η ^ 2 = 180 / ε ^ 2 := by rw [hηdef]; field_simp; norm_num
  have hbound : (F.card : ℝ) ≤ (n : ℝ) ^ (300 * (1 / ε ^ 2) * Real.log (1 / ε)) := by
    refine hcard.trans ?_
    exact Dev.Thm11C.final_bound ε hε0 hε1 n k hn hkle _ hA0 (h180 ▸ hA)
  have hcore : ∀ f : Finset (Fin n) → ℝ, (∀ S, 0 ≤ f S) → Submodular f →
      ∃ S ∈ F, (1 / 4 - ε) * OPT f ≤ f S := by
    intro f hf0 hf
    have := Dev.Thm11B.core (n := n) (k := k) (by omega) hk1 η hη (by linarith) v hv
      (fun i j hij => (le_abs_self _).trans (hvv i j hij)) F hF f hf0 hf
    have e : 3 * η = ε := by rw [hηdef]; ring
    rw [e] at this
    exact this
  by_cases hFu : F = Finset.univ
  · refine ⟨(Finset.univ : Finset (Finset (Fin n))).erase Finset.univ, ?_, ?_, ?_⟩
    · intro h
      have := congrArg Finset.card h
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
      have h2 : 0 < Fintype.card (Finset (Fin n)) := Fintype.card_pos
      omega
    · refine le_trans ?_ hbound
      rw [hFu]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      have : 1 ≤ (Finset.univ : Finset (Finset (Fin n))).card := by
        rw [Finset.card_univ]; exact Fintype.card_pos
      exact_mod_cast Nat.sub_le _ _
    · exact fun f hf0 hf => Dev.Thm11C.fallback hn ε hε0 hε1 f hf0 hf
  · exact ⟨F, hFu, hbound, hcore⟩

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_theorem_1_1_universal_family := @UniversalSubmod.chk_theorem_1_1_universal_family
