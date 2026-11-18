-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.lemma_B_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T20:40:46.905989+00:00
-- url     : https://prove2.me/submissions/65b98301-0422-49d1-95ca-68afb14c85c0

import Theorems.Thm_Concentration_hoeffding_two_sided
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
namespace PrivateAgnosticHalfspace.Gaussian

lemma empiricalError_neighbors {X : Type*} {m : ℕ} (hm : 0 < m)
    (h : X → Bool) (S S' : Fin m → X × Bool)
    (hSS : PrivateUniformGen.Characterization.Neighbors S S') :
    |(m : ℝ) * empiricalError S h - m * empiricalError S' h| ≤ 1 := by
  classical
  rcases hSS with ⟨i, _, heq⟩
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [empiricalError, mul_div_cancel₀ _ hm0]
  rw [← Finset.sum_sub_distrib]
  have hs : (∑ j, ((if h (S j).1 = (S j).2 then (0 : ℝ) else 1) -
      (if h (S' j).1 = (S' j).2 then 0 else 1))) =
      (if h (S i).1 = (S i).2 then (0 : ℝ) else 1) -
      (if h (S' i).1 = (S' i).2 then 0 else 1) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [heq j hji, sub_self]
    · simp
  rw [hs]
  split_ifs <;> norm_num

lemma validation_weight_sum_pos {X : Type*} {K m : ℕ} (hK : 0 < K)
    (h : Fin K → X → Bool) (ε : ℝ) (S : Fin m → X × Bool) :
    0 < ∑ j, Real.exp (-ε * m * empiricalError S (h j) / 2) := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0,hK⟩, Finset.mem_univ _⟩

lemma validationLaw_probability {X : Type*} {K m : ℕ} (hK : 0 < K)
    (h : Fin K → X → Bool) (ε : ℝ) (S : Fin m → X × Bool) :
    IsProbabilityMeasure (validationLaw h ε S) := by
  classical
  have hw := validation_weight_sum_pos hK h ε S
  constructor
  simp only [validationLaw, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← Finset.sum_div]
  rw [div_self hw.ne']
  norm_num

lemma measurable_empiricalError {X : Type*} [MeasurableSpace X] {m : ℕ}
    (h : X → Bool) (hh : Measurable h) :
    Measurable (fun S : Fin m → X × Bool => empiricalError S h) := by
  classical
  unfold empiricalError
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun (hh.comp (measurable_fst.comp (measurable_pi_apply i)))
    (measurable_snd.comp (measurable_pi_apply i))

lemma measurable_validationLaw {X : Type*} [MeasurableSpace X] {K m : ℕ}
    (h : Fin K → X → Bool) (hh : ∀ j, Measurable (h j)) (ε : ℝ) :
    Measurable (fun S : Fin m → X × Bool => validationLaw h ε S) := by
  classical
  have hw (j : Fin K) : Measurable (fun S : Fin m → X × Bool =>
      Real.exp (-ε * m * empiricalError S (h j) / 2)) := by
    exact (((measurable_empiricalError (h j) (hh j)).const_mul (-ε * m)).div_const 2).exp
  unfold validationLaw
  apply Finset.measurable_sum
  intro j _
  exact ((hw j).div (Finset.measurable_sum _ (fun i _ => hw i))).ennreal_ofReal.smul_measure _

end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma normalized_ratio_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (w w' : ι → ℝ) (hw0 : ∀ i, 0 < w i) (hw0' : ∀ i, 0 < w' i)
    (a : ℝ) (ha : 0 ≤ a) (hw : ∀ i, w i ≤ a * w' i)
    (hw' : ∀ i, w' i ≤ a * w i) (j : ι) :
    w j / ∑ i, w i ≤ a ^ 2 * (w' j / ∑ i, w' i) := by
  have hW : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw0 i) Finset.univ_nonempty
  have hW' : 0 < ∑ i, w' i := Finset.sum_pos (fun i _ => hw0' i) Finset.univ_nonempty
  have hs : ∑ i, w' i ≤ a * ∑ i, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hw' i)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hW hW').2
  have hh := mul_le_mul_of_nonneg_left hs (hw0 j).le
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw j) ha) hW.le
  nlinarith

lemma validation_weight_le {X : Type*} {K m : ℕ} (hm : 0 < m)
    (h : Fin K → X → Bool) (ε : ℝ) (hε : 0 ≤ ε)
    (S S' : Fin m → X × Bool)
    (hSS : PrivateUniformGen.Characterization.Neighbors S S') (j : Fin K) :
    Real.exp (-ε * m * empiricalError S (h j) / 2) ≤
      Real.exp (ε / 2) * Real.exp (-ε * m * empiricalError S' (h j) / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := (abs_le.mp (empiricalError_neighbors hm (h j) S S' hSS)).1
  nlinarith

lemma neighbors_symm {X : Type*} {n : ℕ} {S S' : Fin n → X}
    (h : PrivateUniformGen.Characterization.Neighbors S S') :
    PrivateUniformGen.Characterization.Neighbors S' S := by
  rcases h with ⟨i, hne, heq⟩
  exact ⟨i, hne.symm, fun j hj => (heq j hj).symm⟩

lemma validationLaw_measure_le {X : Type*} {K m : ℕ} (hK : 0 < K) (hm : 0 < m)
    (h : Fin K → X → Bool) (ε : ℝ) (hε : 0 ≤ ε)
    (S S' : Fin m → X × Bool)
    (hSS : PrivateUniformGen.Characterization.Neighbors S S') :
    validationLaw h ε S ≤ ENNReal.ofReal (Real.exp ε) • validationLaw h ε S' := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  have hprob (j : Fin K) :
      Real.exp (-ε * m * empiricalError S (h j) / 2) /
        (∑ i, Real.exp (-ε * m * empiricalError S (h i) / 2)) ≤
      Real.exp ε * (Real.exp (-ε * m * empiricalError S' (h j) / 2) /
        (∑ i, Real.exp (-ε * m * empiricalError S' (h i) / 2))) := by
    have hh := normalized_ratio_le
      (fun j => Real.exp (-ε * m * empiricalError S (h j) / 2))
      (fun j => Real.exp (-ε * m * empiricalError S' (h j) / 2))
      (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _) (Real.exp (ε / 2))
      (Real.exp_pos _).le (validation_weight_le hm h ε hε S S' hSS)
      (validation_weight_le hm h ε hε S' S (neighbors_symm hSS)) j
    have he : Real.exp (ε / 2) ^ 2 = Real.exp ε := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [he] using hh
  unfold validationLaw
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos ε).le]
  intro U
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact hprob j

lemma validationLaw_private {X : Type*} {K m : ℕ} (hK : 0 < K) (hm : 0 < m)
    (h : Fin K → X → Bool) (ε : ℝ) (hε : 0 ≤ ε) :
    PrivateUniformGen.Characterization.IsDP
      (fun S : Fin m → X × Bool => (⟨validationLaw h ε S, validationLaw_probability hK h ε S⟩ :
        ProbabilityMeasure (Fin K))) ε 0 := by
  intro S S' hSS U hU
  simp only [add_zero]
  haveI := validationLaw_probability hK h ε S'
  have hh := validationLaw_measure_le hK hm h ε hε S S' hSS U
  have ht : (ENNReal.ofReal (Real.exp ε) • validationLaw h ε S') U ≠ ∞ := by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hh' := ENNReal.toReal_mono ht hh
  change ((validationLaw h ε S) U).toReal ≤ Real.exp ε * ((validationLaw h ε S') U).toReal
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos ε).le, Measure.real] using hh'
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma measurable_mistake {X : Type*} [MeasurableSpace X]
    (h : X → Bool) (hh : Measurable h) :
    Measurable (fun z : X × Bool => if h z.1 = z.2 then (0 : ℝ) else 1) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd)
    measurable_const measurable_const

lemma integral_mistake {X : Type*} [MeasurableSpace X] (P : Measure (X × Bool))
    (h : X → Bool) (hh : Measurable h) :
    (∫ z, (if h z.1 = z.2 then (0 : ℝ) else 1) ∂P) = error P h := by
  classical
  have hset : MeasurableSet {z : X × Bool | h z.1 ≠ z.2} :=
    (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl
  change (∫ z, (if h z.1 = z.2 then (0 : ℝ) else 1) ∂P) =
    P.real {z | h z.1 ≠ z.2}
  rw [← integral_indicator_one hset]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    by_cases hz : h z.1 = z.2 <;> simp [Set.indicator, hz])

lemma empiricalError_concentration {X : Type*} [MeasurableSpace X]
    (m : ℕ) (hm : 0 < m) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (h : X → Bool) (hh : Measurable h) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin m => P)).real
      {S | t ≤ |empiricalError S h - error P h|} ≤ 2 * Real.exp (-2 * m * t ^ 2) := by
  classical
  let loss : X × Bool → ℝ := fun z => if h z.1 = z.2 then 0 else 1
  have hl : Measurable loss := measurable_mistake h hh
  have hind := iIndepFun_pi (μ := fun _ : Fin m => P)
    (X := fun _ : Fin m => loss) (fun _ => hl.aemeasurable)
  have hmeas (i : Fin m) : AEMeasurable (fun S : Fin m → X × Bool => loss (S i))
      (Measure.pi (fun _ : Fin m => P)) := (hl.comp (measurable_pi_apply i)).aemeasurable
  have hbd (i : Fin m) : ∀ᵐ S ∂Measure.pi (fun _ : Fin m => P),
      loss (S i) ∈ Set.Icc (0 : ℝ) 1 := by
    apply ae_of_all
    intro S
    dsimp [loss]
    split_ifs <;> norm_num
  have htail := Concentration.hoeffding_two_sided hind (s := Finset.univ)
    hmeas hbd (ε := (m : ℝ) * t) (by positivity)
  have hmean (i : Fin m) : (∫ S, loss (S i) ∂Measure.pi (fun _ : Fin m => P)) = error P h := by
    rw [integral_comp_eval hl.aestronglyMeasurable]
    exact integral_mistake P h hh
  simp_rw [hmean] at htail
  have heq : {S : Fin m → X × Bool | t ≤ |empiricalError S h - error P h|} =
      {S | (m : ℝ) * t ≤ |(∑ i, loss (S i)) - ∑ _ : Fin m, error P h|} := by
    ext S
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Set.mem_setOf_eq]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have he : (∑ i, loss (S i)) - (m : ℝ) * error P h =
        (m : ℝ) * (empiricalError S h - error P h) := by
      simp only [empiricalError, loss]
      field_simp
    rw [he, abs_mul, abs_of_pos hm0]
    exact (mul_le_mul_iff_right₀ hm0).symm
  rw [heq]
  convert htail using 1
  norm_num [Finset.sum_const]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  congr 1
  field_simp
  <;> ring
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma validationLaw_real_apply {X : Type*} {K m : ℕ}
    (h : Fin K → X → Bool) (ε : ℝ) (S : Fin m → X × Bool) (U : Set (Fin K)) :
    (validationLaw h ε S).real U =
      ∑ j, if j ∈ U then
        Real.exp (-ε * m * empiricalError S (h j) / 2) /
          (∑ i, Real.exp (-ε * m * empiricalError S (h i) / 2)) else 0 := by
  classical
  unfold validationLaw Measure.real
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (Set.toFinite U).measurableSet, Set.indicator]
  rw [ENNReal.toReal_sum (fun _ _ => by split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all only [Pi.one_apply, ENNReal.toReal_mul, ENNReal.toReal_one, mul_one, mul_zero,
    ENNReal.toReal_zero, ENNReal.toReal_ofReal (show 0 ≤
      Real.exp (-ε * m * empiricalError S (h j) / 2) /
        (∑ i, Real.exp (-ε * m * empiricalError S (h i) / 2)) by positivity)]

lemma empiricalError_uniform_tail {X : Type*} [MeasurableSpace X]
    (K m : ℕ) (hm : 0 < m) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (h : Fin K → X → Bool) (hh : ∀ j, Measurable (h j)) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin m => P)).real
      {S | ∃ j, t < |empiricalError S (h j) - error P (h j)|} ≤
      (K : ℝ) * (2 * Real.exp (-2 * m * t ^ 2)) := by
  classical
  have heq : {S : Fin m → X × Bool | ∃ j, t < |empiricalError S (h j) - error P (h j)|} =
      ⋃ j, {S | t < |empiricalError S (h j) - error P (h j)|} := by ext S; simp
  rw [heq]
  calc
    _ ≤ ∑ j, (Measure.pi (fun _ : Fin m => P)).real
        {S | t < |empiricalError S (h j) - error P (h j)|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ j : Fin K, (2 * Real.exp (-2 * m * t ^ 2)) := by
      apply Finset.sum_le_sum
      intro j _
      have hsub : {S : Fin m → X × Bool | t < |empiricalError S (h j) - error P (h j)|} ⊆
          {S | t ≤ |empiricalError S (h j) - error P (h j)|} := by
        intro S hs
        change t < |empiricalError S (h j) - error P (h j)| at hs
        exact le_of_lt hs
      exact (measureReal_mono hsub).trans (empiricalError_concentration m hm P (h j) (hh j) t ht)
    _ = _ := by simp

lemma validation_slack_identity (K m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (η : ℝ) (hη : 0 < η ∧ η < 1) :
    (K : ℝ) * (2 * Real.exp (-2 * m *
      (Real.sqrt (Real.log (4 * (K : ℝ) / η) / (2 * m))) ^ 2)) = η / 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (4 * (K : ℝ) / η) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hη.1).2
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith [hη.2]
  rw [Real.sq_sqrt (div_nonneg hlog (by positivity))]
  have he : -2 * (m : ℝ) * (Real.log (4 * (K : ℝ) / η) / (2 * m)) =
      -Real.log (4 * (K : ℝ) / η) := by field_simp <;> ring
  have harg : 0 < 4 * (K : ℝ) / η := div_pos (mul_pos (by norm_num) hK0) hη.1
  rw [he, Real.exp_neg, Real.exp_log harg]
  field_simp
  <;> ring
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma validationLaw_tail {X : Type*} {K m : ℕ} (hK : 0 < K) (hm : 0 < m)
    (h : Fin K → X → Bool) (ε : ℝ) (hε : 0 < ε)
    (S : Fin m → X × Bool) (j₀ : Fin K) (s : ℝ) :
    (validationLaw h ε S).real {j | empiricalError S (h j₀) + s < empiricalError S (h j)} ≤
      (K : ℝ) * Real.exp (-ε * m * s / 2) := by
  classical
  rw [validationLaw_real_apply]
  have hW := validation_weight_sum_pos hK h ε S
  have hW0 : Real.exp (-ε * m * empiricalError S (h j₀) / 2) ≤
      ∑ i, Real.exp (-ε * m * empiricalError S (h i) / 2) :=
    Finset.single_le_sum (f := fun i : Fin K => Real.exp (-ε * m * empiricalError S (h i) / 2))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j₀)
  calc
    _ ≤ ∑ _ : Fin K, Real.exp (-ε * m * s / 2) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · apply (div_le_iff₀ hW).2
        have he : Real.exp (-ε * m * empiricalError S (h j) / 2) ≤
            Real.exp (-ε * m * s / 2) * Real.exp (-ε * m * empiricalError S (h j₀) / 2) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
          have hj' : empiricalError S (h j₀) + s < empiricalError S (h j) := hj
          have hmul := mul_le_mul_of_nonneg_left hj'.le (mul_pos hε hm0).le
          nlinarith
        exact he.trans (mul_le_mul_of_nonneg_left hW0 (Real.exp_pos _).le)
      · exact (Real.exp_pos _).le
    _ = _ := by simp

lemma validation_selection_slack_identity (K m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    (K : ℝ) * Real.exp (-ε * m *
      (2 * Real.log (2 * (K : ℝ) / η) / (ε * m)) / 2) = η / 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he : -ε * m * (2 * Real.log (2 * (K : ℝ) / η) / (ε * m)) / 2 =
      -Real.log (2 * (K : ℝ) / η) := by field_simp <;> ring
  rw [he, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp
  <;> ring
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma bind_real_apply {Ω Υ : Type*} [MeasurableSpace Ω] [MeasurableSpace Υ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Ω → Measure Υ)
    (hκ : Measurable κ) (hprob : ∀ ω, IsProbabilityMeasure (κ ω))
    (U : Set Υ) (hU : MeasurableSet U) :
    (μ.bind κ).real U = ∫ ω, (κ ω).real U ∂μ := by
  have hmeas : Measurable (fun ω => (κ ω).real U) :=
    ((Measure.measurable_coe hU).comp hκ).ennreal_toReal
  have hbd (ω : Ω) : (κ ω).real U ≤ 1 := by
    haveI := hprob ω
    exact measureReal_le_one
  have hqint : Integrable (fun ω => (κ ω).real U) μ :=
    (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using hbd ω))
  have hconv (ω : Ω) : ENNReal.ofReal ((κ ω).real U) = (κ ω) U := by
    haveI := hprob ω
    exact ofReal_measureReal
  rw [Measure.real_def, Measure.bind_apply hU hκ.aemeasurable]
  calc
    (∫⁻ ω, (κ ω) U ∂μ).toReal =
        (∫⁻ ω, ENNReal.ofReal ((κ ω).real U) ∂μ).toReal := by
          congr 1
          exact lintegral_congr (fun ω => (hconv ω).symm)
    _ = (ENNReal.ofReal (∫ ω, (κ ω).real U ∂μ)).toReal := by
      rw [← ofReal_integral_eq_lintegral_ofReal hqint (ae_of_all _ (fun _ => measureReal_nonneg))]
    _ = _ := ENNReal.toReal_ofReal (integral_nonneg (fun _ => measureReal_nonneg))
end PrivateAgnosticHalfspace.Gaussian

open PrivateAgnosticHalfspace.Gaussian

theorem solution {X : Type*} [MeasurableSpace X]
    (K m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (h : Fin K → X → Bool) (hh : ∀ j, Measurable (h j))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η ∧ η < 1) :
    ∃ A : PrivateUniformGen.Characterization.Mechanism (X × Bool) (Fin K) m,
      (∀ S, (A S : Measure (Fin K)) = validationLaw h ε S) ∧
      Measurable (fun S => (A S : Measure (Fin K))) ∧
      PrivateUniformGen.Characterization.IsDP A ε 0 ∧
      let ν := (Measure.pi (fun _ : Fin m => P)).bind (fun S => (A S : Measure (Fin K)))
      IsProbabilityMeasure ν ∧
      ν.real {j | error P (h j) ≤ (Finset.univ.inf' (⟨⟨0, hK⟩, Finset.mem_univ _⟩) (fun i => error P (h i))) +
        2 * Real.sqrt (Real.log (4 * (K : ℝ) / η) / (2 * m)) +
        2 * Real.log (2 * (K : ℝ) / η) / (ε * m)} ≥ 1 - η := by
  classical
  let A : PrivateUniformGen.Characterization.Mechanism (X × Bool) (Fin K) m :=
    fun S => ⟨validationLaw h ε S, validationLaw_probability hK h ε S⟩
  refine ⟨A, (fun _ => rfl), measurable_validationLaw h hh ε,
    validationLaw_private hK hm h ε hε.le, ?_⟩
  let μ := Measure.pi (fun _ : Fin m => P)
  let κ := fun S : Fin m → X × Bool => validationLaw h ε S
  let ν := μ.bind κ
  have hκ : Measurable κ := measurable_validationLaw h hh ε
  have hκprob : ∀ S, IsProbabilityMeasure (κ S) := validationLaw_probability hK h ε
  have hν : IsProbabilityMeasure ν :=
    isProbabilityMeasure_bind hκ.aemeasurable (ae_of_all _ hκprob)
  letI := hν
  change IsProbabilityMeasure ν ∧ _
  refine ⟨hν, ?_⟩
  let t := Real.sqrt (Real.log (4 * (K : ℝ) / η) / (2 * m))
  let s := 2 * Real.log (2 * (K : ℝ) / η) / (ε * m)
  let e := Finset.univ.inf' (⟨⟨0,hK⟩, Finset.mem_univ _⟩) (fun i => error P (h i))
  rcases Finset.exists_mem_eq_inf' (⟨⟨0,hK⟩, Finset.mem_univ _⟩)
    (fun i : Fin K => error P (h i)) with ⟨j₀, _, hj₀⟩
  change e = error P (h j₀) at hj₀
  let B : Set (Fin m → X × Bool) :=
    {S | ∃ j, t < |empiricalError S (h j) - error P (h j)|}
  have hB : MeasurableSet B := by
    have heq : B = ⋃ j : Fin K, {S | t < |empiricalError S (h j) - error P (h j)|} := by ext S; simp [B]
    rw [heq]
    exact MeasurableSet.iUnion (fun j => measurableSet_lt measurable_const
      (((measurable_empiricalError (h j) (hh j)).sub_const _).abs))
  have hBbound : μ.real B ≤ η / 2 := by
    have ht := empiricalError_uniform_tail K m hm P h hh t (Real.sqrt_nonneg _)
    rw [validation_slack_identity K m hK hm η hη] at ht
    exact ht
  let U : Set (Fin K) := {j | e + 2 * t + s < error P (h j)}
  have hU : MeasurableSet U := (Set.toFinite U).measurableSet
  have hqmeas : Measurable (fun S => (κ S).real U) :=
    ((Measure.measurable_coe hU).comp hκ).ennreal_toReal
  have hqbound (S : Fin m → X × Bool) : (κ S).real U ≤ 1 := by
    haveI := hκprob S
    exact measureReal_le_one
  have hqint : Integrable (fun S => (κ S).real U) μ :=
    (integrable_const (1 : ℝ)).mono' hqmeas.aestronglyMeasurable
      (ae_of_all _ (fun S => by simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using hqbound S))
  have hqgood (S : Fin m → X × Bool) (hS : S ∉ B) : (κ S).real U ≤ η / 2 := by
    haveI := hκprob S
    have hS' (j : Fin K) : |empiricalError S (h j) - error P (h j)| ≤ t := by
      apply le_of_not_gt
      intro hj
      exact hS ⟨j,hj⟩
    have hsub : U ⊆ {j | empiricalError S (h j₀) + s < empiricalError S (h j)} := by
      intro j hj
      change e + 2 * t + s < error P (h j) at hj
      have hjj := (abs_le.mp (hS' j)).1
      have hjz := (abs_le.mp (hS' j₀)).2
      change empiricalError S (h j₀) + s < empiricalError S (h j)
      linarith
    have htail := validationLaw_tail hK hm h ε hε S j₀ s
    rw [validation_selection_slack_identity K m hK hm ε η hε hη.1] at htail
    exact (measureReal_mono hsub).trans htail
  have hint : Integrable (B.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hB
  have hconst : Integrable (fun _ : Fin m → X × Bool => η / 2) μ := integrable_const _
  have hfail : ν.real U ≤ η := by
    rw [bind_real_apply μ κ hκ hκprob U hU]
    calc
      _ ≤ ∫ S, B.indicator (fun _ => (1 : ℝ)) S + η / 2 ∂μ := by
        apply integral_mono_ae hqint (hint.add hconst)
        apply ae_of_all
        intro S
        change (κ S).real U ≤ B.indicator (fun _ => (1 : ℝ)) S + η / 2
        by_cases hS : S ∈ B
        · simp only [Set.indicator_of_mem hS]
          linarith [hqbound S, hη.1]
        · simp only [Set.indicator_of_notMem hS, zero_add]
          exact hqgood S hS
      _ = μ.real B + η / 2 := by
        have hIi : (∫ S, B.indicator (fun _ => (1 : ℝ)) S ∂μ) = μ.real B := by
          simpa using integral_indicator_const (μ := μ) (1 : ℝ) hB
        rw [integral_add hint hconst, hIi]
        simp
      _ ≤ η := by linarith
  have hcomp : ν.real Uᶜ = 1 - ν.real U := by rw [measureReal_compl hU]; simp
  have heq : {j : Fin K | error P (h j) ≤ e + 2 * t + s} = Uᶜ := by ext j; simp [U, not_lt]
  change ν.real {j | error P (h j) ≤ e + 2 * t + s} ≥ 1 - η
  rw [heq, hcomp]
  linarith
