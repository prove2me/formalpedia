-- Prove2me | solution 1 for RiskFunctionals.Distortion.dual_representation
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:56:49.68011+00:00
-- url     : https://prove2.me/submissions/7895bbaa-d6c1-4883-8719-8ed3f7cefeee

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional
import Definitions.Def_RiskFunctionals_Distortion_Orders

open MeasureTheory ProbabilityTheory RiskFunctionals.Distortion

noncomputable def g79s_mu : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

instance g79s_mu_prob : IsProbabilityMeasure g79s_mu := ⟨by simp [g79s_mu]⟩

noncomputable def g79s_P : Measure (ℝ × ℝ) := g79s_mu.prod g79s_mu

instance g79s_P_prob : IsProbabilityMeasure g79s_P := by
  unfold g79s_P; infer_instance

noncomputable def g79s_H : StieltjesFunction ℝ where
  toFun := fun x => (max 0 (min x 1)) ^ 2
  mono' := by
    intro x y hxy
    have h0 : (0:ℝ) ≤ max 0 (min x 1) := le_max_left _ _
    have h1 : max 0 (min x 1) ≤ max 0 (min y 1) :=
      max_le_max le_rfl (min_le_min hxy le_rfl)
    exact pow_le_pow_left₀ h0 h1 2
  right_continuous' := fun x =>
    ((continuous_const.max (continuous_id.min continuous_const)).pow 2).continuousWithinAt

theorem g79s_H_apply (x : ℝ) : g79s_H x = (max 0 (min x 1)) ^ 2 := rfl

theorem g79s_H_on (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : g79s_H p = p ^ 2 := by
  rw [g79s_H_apply, min_eq_left hp.2, max_eq_right hp.1]

def g79s_S : Set (ℝ × ℝ) := {ω | ω.1 < 1/2}

theorem g79s_S_meas : MeasurableSet g79s_S := measurableSet_lt measurable_fst measurable_const

noncomputable def g79s_Y : ℝ × ℝ → ℝ := g79s_S.indicator 1

theorem g79s_Y_meas : Measurable g79s_Y := measurable_one.indicator g79s_S_meas

theorem g79s_PS : g79s_P g79s_S = 1/2 := by
  have : g79s_S = Set.Iio (1/2 : ℝ) ×ˢ Set.univ := by
    ext ω; simp [g79s_S]
  rw [this, g79s_P, Measure.prod_prod, measure_univ, mul_one, g79s_mu,
    Measure.restrict_apply measurableSet_Iio]
  have e : Set.Iio (1/2:ℝ) ∩ Set.Icc 0 1 = Set.Ico 0 (1/2) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [e, Real.volume_Ico]; norm_num [ENNReal.ofReal_div_of_pos]

theorem g79s_PSc : g79s_P g79s_Sᶜ = 1/2 := by
  rw [prob_compl_eq_one_sub g79s_S_meas, g79s_PS]
  rw [ENNReal.sub_eq_of_eq_add (by simp) ]
  rw [ENNReal.div_add_div_same]; norm_num
  exact (ENNReal.div_self (by norm_num) (by norm_num)).symm

-- distribution function of the law of Y
theorem g79s_F (u : ℝ) : distributionFunction (g79s_P.map g79s_Y) u =
    if u < 0 then 0 else if u < 1 then 1/2 else 1 := by
  unfold distributionFunction
  rw [map_measureReal_apply g79s_Y_meas measurableSet_Iic]
  have hY : ∀ ω : ℝ × ℝ, g79s_Y ω = if ω.1 < 1/2 then 1 else 0 := fun ω => by
    unfold g79s_Y; by_cases h : ω.1 < 1/2
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ g79s_S from h)]; rfl
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ g79s_S from h)]
  split_ifs with h1 h2
  · have : g79s_Y ⁻¹' Set.Iic u = ∅ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, hY]
      split_ifs <;> linarith
    simp [this]
  · have : g79s_Y ⁻¹' Set.Iic u = g79s_Sᶜ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_compl_iff, hY]
      have : ω ∉ g79s_S ↔ ¬ ω.1 < 1/2 := Iff.rfl
      rw [this]
      have h1' : 0 ≤ u := le_of_not_gt h1
      by_cases h : ω.1 < 1/2
      · rw [if_pos h]; exact ⟨fun hh => absurd (lt_of_le_of_lt hh h2) (lt_irrefl _), fun hh => absurd h hh⟩
      · rw [if_neg h]; exact ⟨fun _ => h, fun _ => h1'⟩
    rw [this, measureReal_def, g79s_PSc]; norm_num
  · have : g79s_Y ⁻¹' Set.Iic u = Set.univ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true, hY]
      split_ifs <;> linarith
    simp [this]

theorem g79s_q_lo (p : ℝ) (hp : p ∈ Set.Ioc (0:ℝ) (1/2)) :
    quantileFunction (g79s_P.map g79s_Y) p = 0 := by
  unfold quantileFunction
  apply IsLeast.csInf_eq
  refine ⟨?_, fun u hu => ?_⟩
  · show p ≤ distributionFunction _ 0
    rw [g79s_F]; norm_num; linarith [hp.2]
  · have hu' : p ≤ distributionFunction _ u := hu
    rw [g79s_F] at hu'
    by_contra hneg
    rw [if_pos (lt_of_not_ge hneg)] at hu'
    linarith [hp.1]

theorem g79s_q_hi (p : ℝ) (hp : p ∈ Set.Ioc (1/2:ℝ) 1) :
    quantileFunction (g79s_P.map g79s_Y) p = 1 := by
  unfold quantileFunction
  apply IsLeast.csInf_eq
  refine ⟨?_, fun u hu => ?_⟩
  · show p ≤ distributionFunction _ 1
    rw [g79s_F]; norm_num; linarith [hp.2]
  · have hu' : p ≤ distributionFunction _ u := hu
    rw [g79s_F] at hu'
    by_contra hneg
    have h1 : u < 1 := lt_of_not_ge hneg
    rw [if_neg (show ¬ u < 0 by intro h0; rw [if_pos h0] at hu'; linarith [hp.1]), if_pos h1] at hu'
    linarith [hp.1]

theorem g79s_ion (a b : ℝ) (c : ℝ) (f : ℝ → ℝ) (hf : Set.EqOn f (fun _ => c) (Set.Ioc a b)) :
    IntegrableOn f (Set.Ioc a b) g79s_H.measure := by
  have h1 : IntegrableOn (fun _ => c) (Set.Ioc a b) g79s_H.measure :=
    integrableOn_const (by rw [StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_ne_top)
  exact h1.congr_fun hf.symm measurableSet_Ioc

theorem g79s_split : Set.Ioc (0:ℝ) 1 = Set.Ioc 0 (1/2) ∪ Set.Ioc (1/2) 1 :=
  (Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm

theorem g79s_intOn : IntegrableOn (quantileFunction (g79s_P.map g79s_Y)) (Set.Ioc 0 1)
    g79s_H.measure := by
  rw [g79s_split]
  exact (g79s_ion _ _ 0 _ fun p hp => g79s_q_lo p hp).union
    (g79s_ion _ _ 1 _ fun p hp => g79s_q_hi p hp)

theorem g79s_DF : distortionFunctional g79s_H (g79s_P.map g79s_Y) = 3/4 := by
  unfold distortionFunctional
  rw [g79s_split, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (g79s_ion _ _ 0 _ fun p hp => g79s_q_lo p hp) (g79s_ion _ _ 1 _ fun p hp => g79s_q_hi p hp)]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun p hp => g79s_q_lo p hp),
    setIntegral_congr_fun measurableSet_Ioc (fun p hp => g79s_q_hi p hp)]
  simp only [integral_zero, setIntegral_const, smul_eq_mul, mul_one, zero_add]
  rw [measureReal_def, StieltjesFunction.measure_Ioc, g79s_H_on 1 (by norm_num),
    g79s_H_on (1/2) (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem g79s_dom : InDistortionDomain g79s_H (g79s_P.map g79s_Y) := by
  refine ⟨by rw [g79s_H_on 0 (by norm_num)]; norm_num, g79s_intOn, fun _ => ⟨1, ?_⟩⟩
  rw [g79s_F]; norm_num

theorem g79s_Yval (ω : ℝ × ℝ) : g79s_Y ω = if ω.1 < 1/2 then 1 else 0 := by
  unfold g79s_Y; by_cases h : ω.1 < 1/2
  · rw [if_pos h, Set.indicator_of_mem (show ω ∈ g79s_S from h)]; rfl
  · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ g79s_S from h)]

theorem g79s_hind : IndepFun g79s_Y (fun ω : ℝ × ℝ => ω.2) g79s_P := by
  have e : g79s_Y = fun ω : ℝ × ℝ => (Set.Iio (1/2:ℝ)).indicator (fun _ => (1:ℝ)) ω.1 := by
    funext ω
    rw [g79s_Yval]
    by_cases h : ω.1 < 1/2
    · rw [if_pos h, Set.indicator_of_mem (show ω.1 ∈ Set.Iio (1/2:ℝ) from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ω.1 ∉ Set.Iio (1/2:ℝ) from h)]
  rw [e]
  exact indepFun_prod (measurable_const.indicator measurableSet_Iio) measurable_id

theorem g79s_unif2 : IsUniform01 g79s_P (fun ω : ℝ × ℝ => ω.2) :=
  ⟨measurable_snd, by rw [g79s_P, Measure.map_snd_prod, measure_univ, one_smul]; rfl⟩

theorem g79s_unif1 : IsUniform01 g79s_P (fun ω : ℝ × ℝ => ω.1) :=
  ⟨measurable_fst, by rw [g79s_P, Measure.map_fst_prod, measure_univ, one_smul]; rfl⟩

theorem g79s_hint : Integrable (fun ω : ℝ × ℝ => g79s_Y ω * (2 * ω.1)) g79s_P := by
  have hid : Integrable (fun x : ℝ => x) g79s_mu := continuous_id.integrableOn_Icc
  have hb : Integrable (fun ω : ℝ × ℝ => 2 * ω.1) g79s_P := (hid.comp_fst g79s_mu).const_mul 2
  refine hb.norm.mono' (g79s_Y_meas.mul (measurable_const.mul measurable_fst)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [g79s_Yval]
  split_ifs <;> simp

theorem g79s_Yint : Integrable g79s_Y g79s_P :=
  (integrable_const (1:ℝ)).indicator g79s_S_meas

theorem g79s_EY : ∫ ω, g79s_Y ω ∂g79s_P = 1/2 := by
  unfold g79s_Y
  rw [integral_indicator_one g79s_S_meas, measureReal_def, g79s_PS]
  norm_num

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (H : StieltjesFunction ℝ) (h : ℝ → ℝ) (hhm : Measurable h)
    (hhi : IntegrableOn h (Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ p ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H (h p) (Set.Icc (0 : ℝ) 1) p)
    (hH : ∀ p ∈ Set.Icc (0 : ℝ) 1, H p = ∫ q in (0 : ℝ)..p, h q)
    (Y U : Ω → ℝ) (hY : Measurable Y) (hU : IsUniform01 P U) (hind : IndepFun Y U P)
    (hG : InDistortionDomain H (P.map Y)),

    -- (2.70): 𝒜_H(Y) = inf {𝔼(Y Z) : Z = h(U'), U' uniform in [0, 1]}
    IsGLB {x : ℝ | ∃ U' : Ω → ℝ, IsUniform01 P U' ∧
        Integrable (fun ω => Y ω * h (U' ω)) P ∧ x = ∫ ω, Y ω * h (U' ω) ∂P}
      (distortionFunctional H (P.map Y)) ∧
    -- 𝒜_H(Y) = inf {𝔼(Y Z) : Z ≺_CXD Z*}, Z* = h(U') with U' uniform in [0, 1]
    IsGLB {x : ℝ | ∃ Z : Ω → ℝ, Measurable Z ∧ Integrable Z P ∧
        CXD (P.map Z) ((volume.restrict (Set.Icc (0 : ℝ) 1)).map h) ∧
        Integrable (fun ω => Y ω * Z ω) P ∧ x = ∫ ω, Y ω * Z ω ∂P}
      (distortionFunctional H (P.map Y)) ∧
    -- the infimum in (2.70) is attained for Z = h(G(Y) − V_Y), V_Y = (1 − U)[G(Y) − G(Y−)]
    (IsUniform01 P (fun ω => distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω))) ∧
      Integrable (fun ω => Y ω * h (distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω)))) P ∧
      ∫ ω, Y ω * h (distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω))) ∂P = distortionFunctional H (P.map Y))) := by
  intro hall
  have hhi : IntegrableOn (fun x : ℝ => 2 * x) (Set.Icc (0:ℝ) 1) :=
    (continuous_const.mul continuous_id).integrableOn_Icc
  have hderiv : ∀ p ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g79s_H ((fun x : ℝ => 2 * x) p) (Set.Icc (0 : ℝ) 1) p := by
    intro p hp
    have := ((hasDerivAt_pow 2 p).hasDerivWithinAt (s := Set.Icc (0:ℝ) 1)).congr
      (fun y hy => g79s_H_on y hy) (g79s_H_on p hp)
    have e : (fun x : ℝ => 2 * x) p = ((2:ℕ):ℝ) * p ^ (2 - 1) := by norm_num
    rw [e]; exact this
  have hH : ∀ p ∈ Set.Icc (0 : ℝ) 1, g79s_H p = ∫ q in (0 : ℝ)..p, (fun x : ℝ => 2 * x) q := by
    intro p hp
    rw [g79s_H_on p hp, intervalIntegral.integral_const_mul, integral_id]
    ring
  obtain ⟨hglb, -, -⟩ := hall g79s_P g79s_H (fun x => 2 * x) (by fun_prop) hhi hderiv hH g79s_Y
    (fun ω => ω.2) g79s_Y_meas g79s_unif2 g79s_hind g79s_dom
  rw [g79s_DF] at hglb
  have h1 := hglb.1 ⟨fun ω => ω.1, g79s_unif1, g79s_hint, rfl⟩
  have h2 : ∫ ω, g79s_Y ω * (2 * ω.1) ∂g79s_P ≤ ∫ ω, g79s_Y ω ∂g79s_P := by
    refine integral_mono g79s_hint g79s_Yint fun ω => ?_
    show g79s_Y ω * (2 * ω.1) ≤ g79s_Y ω
    rw [g79s_Yval]
    split_ifs with h
    · linarith
    · simp
  rw [g79s_EY] at h2
  simp only at h1
  linarith
