-- Prove2me | solution 1 for QuantumLTF.Membership.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T01:20:48.067738+00:00
-- url     : https://prove2.me/submissions/f5f65d6e-b702-475a-bc3e-8683c2844aa9

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree

section Lemma21Proof

open MeasureTheory ProbabilityTheory QuantumLTF.Membership

private lemma map_inner_stdGaussian {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    Measure.map (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ w x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) = gaussianReal 0 1 := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ w x) :=
    (innerSL ℝ w).continuous.measurable
  have : IsFiniteMeasure (Measure.map (fun x => inner ℝ w x)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
    Measure.isFiniteMeasure_map _ _
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply_real, integral_map hmeas.aemeasurable (by fun_prop), charFun_gaussianReal]
  have h_eq : (fun x : EuclideanSpace ℝ (Fin n) => Complex.exp (↑t * ↑(inner ℝ w x) * Complex.I)) =
      (fun x : EuclideanSpace ℝ (Fin n) => Complex.exp (↑(inner ℝ x (t • w)) * Complex.I)) := by
    ext x
    congr 1
    have : inner ℝ x (t • w) = t * inner ℝ w x := by
      rw [real_inner_comm, inner_smul_left]
      simp
    push_cast [this]
    ring
  rw [h_eq, ← charFun_apply, charFun_stdGaussian, norm_smul, hw]
  simp only [mul_one, Real.norm_eq_abs, Complex.ofReal_zero, mul_zero, zero_sub,
    NNReal.coe_one, one_mul]
  congr 1
  rw [show (↑|t| : ℂ) ^ 2 = ((|t| ^ 2 : ℝ) : ℂ) by norm_cast, sq_abs]
  push_cast
  ring

private lemma map_pair_inner_stdGaussian {n : ℕ} (e₁ e₂ : EuclideanSpace ℝ (Fin n))
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (horth : inner ℝ e₁ e₂ = 0) :
    Measure.map (fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e₁ x, inner ℝ e₂ x))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let Φ : EuclideanSpace ℝ (Fin n) → WithLp 2 (ℝ × ℝ) :=
    fun x => WithLp.toLp 2 (inner ℝ e₁ x, inner ℝ e₂ x)
  have hΦ_meas : Measurable Φ :=
    (WithLp.prod_continuous_toLp 2 ℝ ℝ).measurable.comp
      (((innerSL ℝ e₁).continuous.measurable).prodMk ((innerSL ℝ e₂).continuous.measurable))
  have h_lp : Measure.map Φ (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      Measure.map (WithLp.toLp 2) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have : IsFiniteMeasure (Measure.map Φ (stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
      Measure.isFiniteMeasure_map _ _
    have : IsFiniteMeasure (Measure.map (WithLp.toLp 2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1))) :=
      Measure.isFiniteMeasure_map _ _
    apply Measure.ext_of_charFun
    ext t
    rw [charFun_prod, charFun_gaussianReal, charFun_gaussianReal,
      charFun_apply, integral_map hΦ_meas.aemeasurable (by fun_prop)]
    have h_inner : ∀ x : EuclideanSpace ℝ (Fin n),
        inner ℝ (Φ x) t = inner ℝ x (t.ofLp.1 • e₁ + t.ofLp.2 • e₂) := by
      intro x
      simp only [Φ, WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial]
      rw [inner_add_right, inner_smul_right, inner_smul_right,
        real_inner_comm e₁ x, real_inner_comm e₂ x]
    simp_rw [h_inner]
    rw [← charFun_apply, charFun_stdGaussian]
    have h_norm : ‖t.ofLp.1 • e₁ + t.ofLp.2 • e₂‖ ^ 2 = t.ofLp.1 ^ 2 + t.ofLp.2 ^ 2 := by
      rw [norm_add_sq_real]
      simp [norm_smul, he₁, he₂, inner_smul_left, inner_smul_right, horth, sq_abs]
    rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_zero, mul_zero, NNReal.coe_one]
    rw [show (↑‖t.ofLp.1 • e₁ + t.ofLp.2 • e₂‖ : ℂ) ^ 2 =
        ((‖t.ofLp.1 • e₁ + t.ofLp.2 • e₂‖ ^ 2 : ℝ) : ℂ) by norm_cast, h_norm]
    push_cast
    ring
  have h_ofLp : Measurable (WithLp.ofLp : WithLp 2 (ℝ × ℝ) → ℝ × ℝ) :=
    (WithLp.prod_continuous_ofLp 2 ℝ ℝ).measurable
  have h1 := congrArg (Measure.map (WithLp.ofLp : WithLp 2 (ℝ × ℝ) → ℝ × ℝ)) h_lp
  rw [Measure.map_map h_ofLp hΦ_meas,
    Measure.map_map h_ofLp (WithLp.prod_continuous_toLp 2 ℝ ℝ).measurable] at h1
  simpa [Function.comp_def, Φ] using h1

private lemma disagree_triangle {n : ℕ} (f g h : EuclideanSpace ℝ (Fin n) → ℤ) :
    disagree f h ≤ disagree f g + disagree g h := by
  unfold disagree
  set μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hsub : {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x} := by
    intro x hx
    by_cases hfg : f x = g x
    · exact Or.inr (fun hgh => hx (hfg.trans hgh))
    · exact Or.inl hfg
  have hle : μ {x | f x ≠ h x} ≤ μ {x | f x ≠ g x} + μ {x | g x ≠ h x} :=
    (measure_mono hsub).trans (measure_union_le _ _)
  rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top μ _, measure_ne_top μ _⟩) hle

private lemma disagree_shift_le {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (θ₁ θ₂ : ℝ) :
    disagree (ltf w θ₁) (ltf w θ₂) ≤ |θ₁ - θ₂| / Real.sqrt (2 * Real.pi) := by
  unfold disagree ltf
  set μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let a := min θ₁ θ₂
  let b := max θ₁ θ₂
  have hab : a ≤ b := min_le_max
  have hsub : {x : EuclideanSpace ℝ (Fin n) | sgn (inner ℝ w x - θ₁) ≠ sgn (inner ℝ w x - θ₂)} ⊆
      (fun x => inner ℝ w x) ⁻¹' Set.Icc a b := by
    intro x hx
    change sgn (inner ℝ w x - θ₁) ≠ sgn (inner ℝ w x - θ₂) at hx
    simp only [sgn] at hx
    simp only [Set.mem_preimage, Set.mem_Icc, a, b]
    constructor
    · by_contra hlt
      have hmin := lt_min_iff.mp (lt_of_not_ge hlt)
      have h1 : ¬ (0 ≤ inner ℝ w x - θ₁) := by linarith
      have h2 : ¬ (0 ≤ inner ℝ w x - θ₂) := by linarith
      simp [h1, h2] at hx
    · by_contra hgt
      have hmax := max_lt_iff.mp (lt_of_not_ge hgt)
      have h1 : 0 ≤ inner ℝ w x - θ₁ := by linarith
      have h2 : 0 ≤ inner ℝ w x - θ₂ := by linarith
      simp [h1, h2] at hx
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ w x) :=
    (innerSL ℝ w).continuous.measurable
  have h1 : μ {x | sgn (inner ℝ w x - θ₁) ≠ sgn (inner ℝ w x - θ₂)} ≤
      (gaussianReal 0 1) (Set.Icc a b) := by
    calc μ {x | sgn (inner ℝ w x - θ₁) ≠ sgn (inner ℝ w x - θ₂)}
        ≤ μ ((fun x => inner ℝ w x) ⁻¹' Set.Icc a b) := measure_mono hsub
      _ = (Measure.map (fun x => inner ℝ w x) μ) (Set.Icc a b) :=
          (Measure.map_apply hmeas measurableSet_Icc).symm
      _ = (gaussianReal 0 1) (Set.Icc a b) := by rw [map_inner_stdGaussian w hw]
  have h2 : (μ {x | sgn (inner ℝ w x - θ₁) ≠ sgn (inner ℝ w x - θ₂)}).toReal ≤
      ((gaussianReal 0 1) (Set.Icc a b)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) h1
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero] at h2
  have hint_nonneg : 0 ≤ ∫ x in Set.Icc a b, gaussianPDFReal 0 1 x :=
    setIntegral_nonneg measurableSet_Icc (fun x _ => gaussianPDFReal_nonneg 0 1 x)
  rw [ENNReal.toReal_ofReal hint_nonneg] at h2
  have h_bound : ∫ x in Set.Icc a b, gaussianPDFReal 0 1 x ≤
      ∫ _ in Set.Icc a b, (Real.sqrt (2 * Real.pi))⁻¹ := by
    refine setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
      (integrableOn_const (by simp)) measurableSet_Icc ?_
    intro x _
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have hexp : Real.exp (-x ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg x]
    exact mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) hexp
  have h_const : ∫ _ in Set.Icc a b, (Real.sqrt (2 * Real.pi))⁻¹ =
      (b - a) / Real.sqrt (2 * Real.pi) := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul, div_eq_mul_inv]
  have hab_abs : b - a = |θ₁ - θ₂| := by
    by_cases hle : θ₁ ≤ θ₂
    · simp [a, b, min_eq_left hle, max_eq_right hle, abs_of_nonpos (sub_nonpos.2 hle)]
    · have hge : θ₂ ≤ θ₁ := le_of_not_ge hle
      simp [a, b, min_eq_right hge, max_eq_left hge, abs_of_nonneg (sub_nonneg.2 hge)]
  rw [h_const, hab_abs] at h_bound
  exact h2.trans h_bound

private lemma gaussian_Ico_shift_le (m r : ℝ) (hr : 0 ≤ r) :
    (gaussianReal 0 1) (Set.Ico (m - r) (m + r)) ≤ (gaussianReal 0 1) (Set.Ico (-r) r) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, gaussianReal_apply_eq_integral 0 one_ne_zero]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_Ico_eq_integral_Ioc, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by linarith)]
  let φ : ℝ → ℝ := fun x => gaussianPDFReal 0 1 x
  have hφ_cont : Continuous φ := by
    unfold φ
    rw [gaussianPDFReal_def]
    fun_prop
  have hφ_even : ∀ x, φ (-x) = φ x := by
    intro x
    simp [φ, gaussianPDFReal_def]
  let g : ℝ → ℝ := fun u => ∫ x in (u - r)..(u + r), φ x
  have hg0 : g 0 = ∫ x in (-r)..r, φ x := by simp [g]
  change g m ≤ ∫ x in (-r)..r, φ x
  rw [← hg0]
  have hg_even : ∀ u, g (-u) = g u := by
    intro u
    simp only [g]
    have hcomp := intervalIntegral.integral_comp_neg (a := -u - r) (b := -u + r) φ
    simp only [hφ_even] at hcomp
    rw [hcomp]
    congr 1 <;> ring
  have hg_nonneg_le : ∀ u ≥ 0, g u ≤ g 0 := by
    intro u hu
    let F : ℝ → ℝ := fun y => ∫ x in (0 : ℝ)..y, φ x
    have hF_deriv : ∀ y, HasDerivAt F (φ y) y := fun y =>
      intervalIntegral.integral_hasDerivAt_right
        (hφ_cont.intervalIntegrable (μ := volume) 0 y)
        (hφ_cont.stronglyMeasurableAtFilter volume _)
        hφ_cont.continuousAt
    have hg_eq : ∀ y, g y = F (y + r) - F (y - r) := by
      intro y
      simp only [g, F]
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hφ_cont.intervalIntegrable (μ := volume) 0 (y - r))
        (hφ_cont.intervalIntegrable (μ := volume) (y - r) (y + r))
      linarith
    have hg_deriv : ∀ y, HasDerivAt g (φ (y + r) - φ (y - r)) y := by
      intro y
      rw [show g = fun z => F (z + r) - F (z - r) from funext hg_eq]
      exact ((hF_deriv (y + r)).comp_add_const y r).sub ((hF_deriv (y - r)).comp_sub_const y r)
    have hanti : AntitoneOn g (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · exact Continuous.continuousOn (continuous_iff_continuousAt.mpr
          fun y => (hg_deriv y).continuousAt)
      · exact fun y _ => (hg_deriv y).differentiableAt.differentiableWithinAt
      · intro y hy
        have hy0 : 0 ≤ y := interior_subset hy
        rw [(hg_deriv y).deriv]
        simp only [φ, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
        have hexp : Real.exp (-(y + r) ^ 2 / 2) ≤ Real.exp (-(y - r) ^ 2 / 2) := by
          rw [Real.exp_le_exp]
          nlinarith
        have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hexp hc]
    exact hanti (le_refl (0 : ℝ)) hu hu
  rcases le_total 0 m with hm | hm
  · exact hg_nonneg_le m hm
  · rw [← hg_even m]
    exact hg_nonneg_le (-m) (by linarith)

private lemma hasDerivAt_neg_exp_half_sq (r : ℝ) :
    HasDerivAt (fun x : ℝ => -Real.exp (-x ^ 2 / 2)) (r * Real.exp (-r ^ 2 / 2)) r := by
  have h0 : HasDerivAt (fun x : ℝ => (-1 / 2 : ℝ) * x ^ 2)
      ((-1 / 2 : ℝ) * (↑(2 : ℕ) * r ^ (2 - 1))) r :=
    (hasDerivAt_pow 2 r).const_mul (-1 / 2)
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-r) r := by
    rw [show ((-1 / 2 : ℝ) * (↑(2 : ℕ) * r ^ (2 - 1))) = -r by norm_num; ring] at h0
    exact h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by ring)
  have h2 : HasDerivAt (fun x : ℝ => (-1 : ℝ) * Real.exp (-x ^ 2 / 2))
      ((-1 : ℝ) * (Real.exp (-r ^ 2 / 2) * (-r))) r :=
    (h1.exp).const_mul (-1)
  have h3 : HasDerivAt (fun x : ℝ => -Real.exp (-x ^ 2 / 2))
      ((-1 : ℝ) * (Real.exp (-r ^ 2 / 2) * (-r))) r :=
    h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by ring)
  rw [show (-1 : ℝ) * (Real.exp (-r ^ 2 / 2) * (-r)) = r * Real.exp (-r ^ 2 / 2) by ring] at h3
  exact h3

private lemma r_exp_integrableOn_Ioi :
    IntegrableOn (fun r : ℝ => r * Real.exp (-r ^ 2 / 2)) (Set.Ioi 0) volume := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun r => -Real.exp (-r ^ 2 / 2)) (l := 0)
    (Continuous.continuousWithinAt (by fun_prop))
    (fun r _ => hasDerivAt_neg_exp_half_sq r)
    (fun r hr => mul_nonneg (le_of_lt hr) (Real.exp_nonneg _)) ?_
  have htend : Filter.Tendsto (fun r : ℝ => -r ^ 2 / 2) Filter.atTop Filter.atBot := by
    have hsq : Filter.Tendsto (fun r : ℝ => r ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (by norm_num)
    exact (Filter.tendsto_neg_atTop_atBot.comp hsq).atBot_div_const (by norm_num)
  simpa using (Real.tendsto_exp_atBot.comp htend).neg

private lemma r_exp_integral_Ioi :
    ∫ r : ℝ in Set.Ioi 0, r * Real.exp (-r ^ 2 / 2) = 1 := by
  have htend : Filter.Tendsto (fun r : ℝ => -Real.exp (-r ^ 2 / 2)) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun r : ℝ => -r ^ 2 / 2) Filter.atTop Filter.atBot := by
      have h2 : Filter.Tendsto (fun r : ℝ => r ^ 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_pow_atTop (by norm_num)
      exact (Filter.tendsto_neg_atTop_atBot.comp h2).atBot_div_const (by norm_num)
    simpa using (Real.tendsto_exp_atBot.comp hsq).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ => hasDerivAt_neg_exp_half_sq r) r_exp_integrableOn_Ioi htend]
  simp

private lemma cos_nonneg_iff_in_strip {u : ℝ} (hu1 : -3 * Real.pi / 2 < u)
    (hu2 : u < 3 * Real.pi / 2) :
    0 ≤ Real.cos u ↔ -Real.pi / 2 ≤ u ∧ u ≤ Real.pi / 2 := by
  constructor
  · intro hcos
    constructor
    · by_contra hlt
      push Not at hlt
      have hsin : Real.cos u < 0 := by
        have : Real.cos (-u) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
        rwa [Real.cos_neg] at this
      linarith
    · by_contra hgt
      push Not at hgt
      have hsin : Real.cos u < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
      linarith
  · rintro ⟨h1, h2⟩
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩

private lemma measurableSet_sgn_pair_ne (c s t : ℝ) :
    MeasurableSet {p : ℝ × ℝ | sgn (c * p.2 + s * p.1 - t) ≠ sgn (c * p.2 - s * p.1 - t)} := by
  have h_eq : {p : ℝ × ℝ | sgn (c * p.2 + s * p.1 - t) ≠ sgn (c * p.2 - s * p.1 - t)} =
      ({p : ℝ × ℝ | 0 ≤ c * p.2 + s * p.1 - t} ∩ {p : ℝ × ℝ | c * p.2 - s * p.1 - t < 0}) ∪
      ({p : ℝ × ℝ | c * p.2 + s * p.1 - t < 0} ∩ {p : ℝ × ℝ | 0 ≤ c * p.2 - s * p.1 - t}) := by
    ext p
    change (sgn (c * p.2 + s * p.1 - t) ≠ sgn (c * p.2 - s * p.1 - t)) ↔
      (0 ≤ c * p.2 + s * p.1 - t ∧ c * p.2 - s * p.1 - t < 0) ∨
      (c * p.2 + s * p.1 - t < 0 ∧ 0 ≤ c * p.2 - s * p.1 - t)
    simp only [sgn]
    by_cases h1 : 0 ≤ c * p.2 + s * p.1 - t <;> by_cases h2 : 0 ≤ c * p.2 - s * p.1 - t
    · simp only [h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, true_and, and_true, false_iff]
      rintro (ha | ha) <;> linarith
    · simp only [h1, h2, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, true_and, true_iff]
      exact Or.inl (lt_of_not_ge h2)
    · simp only [h1, h2, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, and_true, true_iff]
      exact Or.inr (lt_of_not_ge h1)
    · simp only [h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_and, and_false, or_self]
  rw [h_eq]
  have hc1 : Measurable (fun p : ℝ × ℝ => c * p.2 + s * p.1 - t) :=
    Continuous.measurable (by fun_prop)
  have hc2 : Measurable (fun p : ℝ × ℝ => c * p.2 - s * p.1 - t) :=
    Continuous.measurable (by fun_prop)
  exact ((measurableSet_Ici.preimage hc1).inter (measurableSet_Iio.preimage hc2)).union
    ((measurableSet_Iio.preimage hc1).inter (measurableSet_Ici.preimage hc2))

private lemma polar_sector_measure {α : ℝ} (hα0 : 0 < α) (hαπ : α < Real.pi) :
    let c := Real.cos (α / 2)
    let s := Real.sin (α / 2)
    let S₀ : Set (ℝ × ℝ) := {p | sgn (c * p.1 + s * p.2) ≠ sgn (c * p.1 - s * p.2)}
    (((gaussianReal 0 1).prod (gaussianReal 0 1)) S₀).toReal = α / Real.pi := by
  intro c s S₀
  have hS₀_meas : MeasurableSet S₀ := by
    have heq : S₀ = Prod.swap ⁻¹' {p : ℝ × ℝ | sgn (c * p.2 + s * p.1 - 0) ≠ sgn (c * p.2 - s * p.1 - 0)} := by
      ext p; simp [S₀]
    rw [heq]
    exact (measurableSet_sgn_pair_ne c s 0).preimage measurable_swap
  set γ := gaussianReal 0 1
  have h_toReal : ((γ.prod γ) S₀).toReal = ∫ p, S₀.indicator (1 : ℝ × ℝ → ℝ) p ∂(γ.prod γ) := by
    rw [integral_indicator_one hS₀_meas]
    rfl
  have hint_prod : Integrable (S₀.indicator (1 : ℝ × ℝ → ℝ)) (γ.prod γ) :=
    (integrable_const (1 : ℝ)).indicator hS₀_meas
  rw [h_toReal, integral_prod _ hint_prod]
  have h_inner_int : ∀ u, ∫ v, S₀.indicator (1 : ℝ × ℝ → ℝ) (u, v) ∂γ =
      ∫ v, gaussianPDFReal 0 1 v * S₀.indicator (1 : ℝ × ℝ → ℝ) (u, v) := by
    intro u
    simpa [smul_eq_mul] using integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1)
      (f := fun v => S₀.indicator (1 : ℝ × ℝ → ℝ) (u, v)) one_ne_zero
  simp_rw [h_inner_int]
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  simp_rw [← integral_const_mul]
  let f : ℝ × ℝ → ℝ := fun p =>
    gaussianPDFReal 0 1 p.1 * (gaussianPDFReal 0 1 p.2 * S₀.indicator (1 : ℝ × ℝ → ℝ) p)
  have hf_int : Integrable f (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2)
        (volume.prod volume) :=
      (integrable_gaussianPDFReal 0 1).mul_prod (integrable_gaussianPDFReal 0 1)
    have hpdf_meas : Measurable (gaussianPDFReal 0 1) := by
      rw [gaussianPDFReal_def]
      exact Continuous.measurable (by fun_prop)
    refine hdom.mono' ?_ ?_
    · exact ((hpdf_meas.comp measurable_fst).mul
        ((hpdf_meas.comp measurable_snd).mul (measurable_const.indicator hS₀_meas))).aestronglyMeasurable
    · filter_upwards with p
      simp only [f, Real.norm_eq_abs]
      by_cases hp : p ∈ S₀
      · simp [hp, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _)]
      · simp only [hp, not_false_eq_true, Set.indicator_of_notMem, mul_zero, abs_zero]
        exact mul_nonneg (gaussianPDFReal_nonneg 0 1 _) (gaussianPDFReal_nonneg 0 1 _)
  change ∫ u, (∫ v, f (u, v)) = α / Real.pi
  rw [← integral_prod f hf_int]
  change ∫ p : ℝ × ℝ, f p = α / Real.pi
  rw [← integral_comp_polarCoord_symm f, polarCoord_target]
  let A : Set ℝ := Set.Ico (-Real.pi / 2 - α / 2) (-Real.pi / 2 + α / 2) ∪
    Set.Ioc (Real.pi / 2 - α / 2) (Real.pi / 2 + α / 2)
  have hA_meas : MeasurableSet A := measurableSet_Ico.union measurableSet_Ioc
  have h_ae_eq : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      q.1 • f (polarCoord.symm q) =
        ((2 * Real.pi)⁻¹ * (q.1 * Real.exp (-q.1 ^ 2 / 2))) *
          A.indicator (1 : ℝ → ℝ) q.2 := by
    rintro ⟨r, φ⟩ ⟨hr, hφ⟩
    simp only [Set.mem_Ioi] at hr
    simp only [Set.mem_Ioo] at hφ
    rw [polarCoord_symm_apply]
    simp only [smul_eq_mul, f, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    have hpdf : (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (- (r * Real.cos φ) ^ 2 / 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (- (r * Real.sin φ) ^ 2 / 2)) =
        (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2) := by
      have hsq_pi : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
      have htrig : -(r * Real.cos φ) ^ 2 / 2 + -(r * Real.sin φ) ^ 2 / 2 = -r ^ 2 / 2 := by
        have := Real.sin_sq_add_cos_sq φ
        nlinarith
      calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r * Real.cos φ) ^ 2 / 2) *
              ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r * Real.sin φ) ^ 2 / 2))
          = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
              (Real.exp (-(r * Real.cos φ) ^ 2 / 2) * Real.exp (-(r * Real.sin φ) ^ 2 / 2)) := by ring
        _ = (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2) := by
              rw [hsq_pi, ← Real.exp_add, htrig]
    have hmem_iff : (r * Real.cos φ, r * Real.sin φ) ∈ S₀ ↔ φ ∈ A := by
      change (sgn (c * (r * Real.cos φ) + s * (r * Real.sin φ)) ≠
          sgn (c * (r * Real.cos φ) - s * (r * Real.sin φ))) ↔ φ ∈ A
      simp only [sgn]
      have ht1 : c * (r * Real.cos φ) + s * (r * Real.sin φ) = r * Real.cos (φ - α / 2) := by
        simp only [c, s]
        rw [Real.cos_sub]
        ring
      have ht2 : c * (r * Real.cos φ) - s * (r * Real.sin φ) = r * Real.cos (φ + α / 2) := by
        simp only [c, s]
        rw [Real.cos_add]
        ring
      rw [ht1, ht2]
      have hc1 : (0 ≤ r * Real.cos (φ - α / 2)) ↔ (-Real.pi / 2 + α / 2 ≤ φ ∧ φ ≤ Real.pi / 2 + α / 2) := by
        rw [mul_nonneg_iff_right_nonneg_of_pos hr,
          cos_nonneg_iff_in_strip (by linarith [hφ.1]) (by linarith [hφ.2])]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
      have hc2 : (0 ≤ r * Real.cos (φ + α / 2)) ↔ (-Real.pi / 2 - α / 2 ≤ φ ∧ φ ≤ Real.pi / 2 - α / 2) := by
        rw [mul_nonneg_iff_right_nonneg_of_pos hr,
          cos_nonneg_iff_in_strip (by linarith [hφ.1]) (by linarith [hφ.2])]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
      simp only [A, Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
      by_cases hp1 : 0 ≤ r * Real.cos (φ - α / 2) <;> by_cases hp2 : 0 ≤ r * Real.cos (φ + α / 2)
      · simp only [hp1, hp2, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
        rw [hc1] at hp1; rw [hc2] at hp2
        rintro (⟨_, h⟩ | ⟨h, _⟩) <;> linarith
      · simp only [hp1, hp2, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
        rw [hc1] at hp1; rw [hc2] at hp2
        push Not at hp2
        by_cases hleft : -Real.pi / 2 - α / 2 ≤ φ
        · exact Or.inr ⟨hp2 hleft, hp1.2⟩
        · linarith [hp1.1]
      · simp only [hp1, hp2, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
        rw [hc1] at hp1; rw [hc2] at hp2
        push Not at hp1
        by_cases hleft : -Real.pi / 2 + α / 2 ≤ φ
        · linarith [hp1 hleft, hp2.2]
        · exact Or.inl ⟨hp2.1, lt_of_not_ge hleft⟩
      · simp only [hp1, hp2, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
        rw [hc1] at hp1; rw [hc2] at hp2
        push Not at hp1 hp2
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · linarith [hp2 h1]
        · linarith [hp1 (by linarith)]
    by_cases hA : φ ∈ A
    · have hS : (r * Real.cos φ, r * Real.sin φ) ∈ S₀ := hmem_iff.mpr hA
      simp only [hS, hA, Set.indicator_of_mem, Pi.one_apply, mul_one]
      linear_combination r * hpdf
    · have hS : (r * Real.cos φ, r * Real.sin φ) ∉ S₀ := mt hmem_iff.mp hA
      simp [hS, hA]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) h_ae_eq]
  have hint_prod_polar : IntegrableOn (fun q : ℝ × ℝ =>
      ((2 * Real.pi)⁻¹ * (q.1 * Real.exp (-q.1 ^ 2 / 2))) *
        A.indicator (1 : ℝ → ℝ) q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    have hr_int : IntegrableOn (fun r : ℝ => (2 * Real.pi)⁻¹ * (r * Real.exp (-r ^ 2 / 2)))
        (Set.Ioi 0) volume := r_exp_integrableOn_Ioi.const_mul _
    have hφ_int : IntegrableOn (A.indicator (1 : ℝ → ℝ))
        (Set.Ioo (-Real.pi) Real.pi) volume :=
      (integrableOn_const (by simp [Real.volume_Ioo])).indicator hA_meas
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hr_int.mul_prod hφ_int
  change ∫ q in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ((2 * Real.pi)⁻¹ * (q.1 * Real.exp (-q.1 ^ 2 / 2))) *
        A.indicator (1 : ℝ → ℝ) q.2 ∂(volume.prod volume) = α / Real.pi
  rw [setIntegral_prod _ hint_prod_polar]
  simp_rw [integral_const_mul]
  have hA_sub : A ⊆ Set.Ioo (-Real.pi) Real.pi := by
    intro φ hφ
    rcases hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  have hφ_val : ∫ φ in Set.Ioo (-Real.pi) Real.pi, A.indicator (1 : ℝ → ℝ) φ = 2 * α := by
    rw [setIntegral_indicator hA_meas, Set.inter_eq_self_of_subset_right hA_sub]
    simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
    have hdisj : Disjoint (Set.Ico (-Real.pi / 2 - α / 2) (-Real.pi / 2 + α / 2))
        (Set.Ioc (Real.pi / 2 - α / 2) (Real.pi / 2 + α / 2)) := by
      rw [Set.disjoint_left]
      intro φ h1 h2
      linarith [h1.2, h2.1]
    rw [Measure.real, measure_union hdisj measurableSet_Ioc, Real.volume_Ico, Real.volume_Ioc,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hφ_val, integral_mul_const, integral_const_mul, r_exp_integral_Ioi]
  field_simp [Real.pi_ne_zero]

private lemma disagree_common_and_zero {n : ℕ} (w₁ w₂ : EuclideanSpace ℝ (Fin n))
    (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1) (θ : ℝ) :
    disagree (ltf w₁ θ) (ltf w₂ θ) ≤ disagree (ltf w₁ 0) (ltf w₂ 0) ∧
      disagree (ltf w₁ 0) (ltf w₂ 0) = Real.arccos (inner ℝ w₁ w₂) / Real.pi := by
  have hcs := abs_real_inner_le_norm w₁ w₂
  rw [h₁, h₂, mul_one] at hcs
  have h_le_one : inner ℝ w₁ w₂ ≤ 1 := (abs_le.mp hcs).2
  have h_ge_neg_one : -1 ≤ inner ℝ w₁ w₂ := (abs_le.mp hcs).1
  rcases eq_or_lt_of_le h_le_one with h_eq1 | h_lt1
  · have hw_eq : w₁ = w₂ := by
      have hsq : ‖w₁ - w₂‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, h₁, h₂, h_eq1]
        ring
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    rw [← hw_eq] at h_eq1 ⊢
    have hd : ∀ t, disagree (ltf w₁ t) (ltf w₁ t) = 0 := by
      intro t
      unfold disagree
      have hempty : {x : EuclideanSpace ℝ (Fin n) | ltf w₁ t x ≠ ltf w₁ t x} = ∅ := by
        ext x; simp
      rw [hempty, measure_empty, ENNReal.toReal_zero]
    rw [hd θ, hd 0, h_eq1, Real.arccos_one, zero_div]
    exact ⟨le_rfl, rfl⟩
  · rcases eq_or_lt_of_le h_ge_neg_one with h_eq_neg1 | h_gt_neg1
    · have hw_neg : w₂ = -w₁ := by
        have hsq : ‖w₁ + w₂‖ ^ 2 = 0 := by
          rw [norm_add_sq_real, h₁, h₂, ← h_eq_neg1]
          ring
        exact eq_neg_of_add_eq_zero_right (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
      have hzero : disagree (ltf w₁ 0) (ltf w₂ 0) = 1 := by
        rw [hw_neg]
        unfold disagree ltf
        set μ := stdGaussian (EuclideanSpace ℝ (Fin n))
        have hset : {x : EuclideanSpace ℝ (Fin n) |
            sgn (inner ℝ w₁ x - 0) ≠ sgn (inner ℝ (-w₁) x - 0)} =
            (fun x => inner ℝ w₁ x) ⁻¹' ({0}ᶜ : Set ℝ) := by
          ext x
          change (sgn (inner ℝ w₁ x - 0) ≠ sgn (inner ℝ (-w₁) x - 0)) ↔ inner ℝ w₁ x ≠ 0
          simp only [sub_zero, inner_neg_left, sgn]
          rcases lt_trichotomy (inner ℝ w₁ x) 0 with hlt | heq | hgt
          · have h1 : ¬ (0 ≤ inner ℝ w₁ x) := by linarith
            have h2 : 0 ≤ -inner ℝ w₁ x := by linarith
            simp [h1, h2, ne_of_lt hlt]
          · simp [heq]
          · have h1 : 0 ≤ inner ℝ w₁ x := by linarith
            have h2 : ¬ (0 ≤ -inner ℝ w₁ x) := by linarith
            simp [h1, h2, ne_of_gt hgt]
        have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ w₁ x) :=
          (innerSL ℝ w₁).continuous.measurable
        rw [hset, ← Measure.map_apply hmeas (MeasurableSet.compl (measurableSet_singleton 0)),
          map_inner_stdGaussian w₁ h₁]
        have h0 : (gaussianReal 0 1) ({0} : Set ℝ) = 0 := by
          rw [gaussianReal_apply_eq_integral 0 one_ne_zero,
            setIntegral_measure_zero _ Real.volume_singleton, ENNReal.ofReal_zero]
        rw [prob_compl_eq_one_sub (measurableSet_singleton 0), h0, tsub_zero, ENNReal.toReal_one]
      refine ⟨?_, ?_⟩
      · rw [hzero]
        unfold disagree
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      · rw [hzero, ← h_eq_neg1, Real.arccos_neg_one, div_self Real.pi_ne_zero]
    · let β := inner ℝ w₁ w₂
      let α := Real.arccos β
      have hα0 : 0 < α := Real.arccos_pos.mpr h_lt1
      have hαπ : α < Real.pi := Real.arccos_lt_pi.mpr h_gt_neg1
      have hcosα : Real.cos α = β := Real.cos_arccos h_ge_neg_one h_le_one
      let c := Real.cos (α / 2)
      let s := Real.sin (α / 2)
      have hc_pos : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hs_pos : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hc_sq : 4 * c ^ 2 = 2 * (1 + β) := by
        have h := Real.cos_sq (α / 2)
        rw [show 2 * (α / 2) = α by ring, hcosα] at h
        simp only [c]
        linarith
      have hs_sq : 4 * s ^ 2 = 2 * (1 - β) := by
        have h := Real.sin_sq (α / 2)
        have hc := Real.cos_sq (α / 2)
        rw [show 2 * (α / 2) = α by ring, hcosα] at hc
        simp only [s]
        linarith
      let e₁ := (2 * c)⁻¹ • (w₁ + w₂)
      let e₂ := (2 * s)⁻¹ • (w₁ - w₂)
      have he₁ : ‖e₁‖ = 1 := by
        have hsq : ‖w₁ + w₂‖ ^ 2 = 4 * c ^ 2 := by
          rw [norm_add_sq_real, h₁, h₂, hc_sq]
          ring
        have hnorm : ‖w₁ + w₂‖ = 2 * c := by
          nlinarith [norm_nonneg (w₁ + w₂), hc_pos]
        rw [show e₁ = (2 * c)⁻¹ • (w₁ + w₂) from rfl, norm_smul, hnorm, Real.norm_eq_abs,
          abs_inv, abs_of_pos (by positivity : 0 < 2 * c)]
        field_simp [ne_of_gt hc_pos]
      have he₂ : ‖e₂‖ = 1 := by
        have hsq : ‖w₁ - w₂‖ ^ 2 = 4 * s ^ 2 := by
          rw [norm_sub_sq_real, h₁, h₂, hs_sq]
          ring
        have hnorm : ‖w₁ - w₂‖ = 2 * s := by
          nlinarith [norm_nonneg (w₁ - w₂), hs_pos]
        rw [show e₂ = (2 * s)⁻¹ • (w₁ - w₂) from rfl, norm_smul, hnorm, Real.norm_eq_abs,
          abs_inv, abs_of_pos (by positivity : 0 < 2 * s)]
        field_simp [ne_of_gt hs_pos]
      have horth : inner ℝ e₂ e₁ = 0 := by
        simp only [e₁, e₂, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
        have hdiff : inner ℝ (w₁ - w₂) (w₁ + w₂) = 0 := by
          rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_comm w₂ w₁,
            real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h₁, h₂]
          ring
        rw [hdiff, mul_zero, mul_zero]
      have hw₁_decomp : ∀ x, inner ℝ w₁ x = c * inner ℝ e₁ x + s * inner ℝ e₂ x := by
        intro x
        have hw₁_eq : w₁ = c • e₁ + s • e₂ := by
          simp only [e₁, e₂, smul_smul]
          have hc2 : c * (2 * c)⁻¹ = (2 : ℝ)⁻¹ := by field_simp [ne_of_gt hc_pos]
          have hs2 : s * (2 * s)⁻¹ = (2 : ℝ)⁻¹ := by field_simp [ne_of_gt hs_pos]
          rw [hc2, hs2, smul_add, smul_sub, add_add_sub_cancel, ← add_smul,
            show ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 by norm_num, one_smul]
        calc inner ℝ w₁ x = inner ℝ (c • e₁ + s • e₂) x :=
              congrArg (fun v => inner ℝ v x) hw₁_eq
          _ = c * inner ℝ e₁ x + s * inner ℝ e₂ x := by
              rw [inner_add_left, real_inner_smul_left e₁ x c, real_inner_smul_left e₂ x s]
      have hw₂_decomp : ∀ x, inner ℝ w₂ x = c * inner ℝ e₁ x - s * inner ℝ e₂ x := by
        intro x
        have hw₂_eq : w₂ = c • e₁ - s • e₂ := by
          simp only [e₁, e₂, smul_smul]
          have hc2 : c * (2 * c)⁻¹ = (2 : ℝ)⁻¹ := by field_simp [ne_of_gt hc_pos]
          have hs2 : s * (2 * s)⁻¹ = (2 : ℝ)⁻¹ := by field_simp [ne_of_gt hs_pos]
          have hab : (2 : ℝ)⁻¹ • w₁ + (2 : ℝ)⁻¹ • w₂ - ((2 : ℝ)⁻¹ • w₁ - (2 : ℝ)⁻¹ • w₂) =
              (2 : ℝ)⁻¹ • w₂ + (2 : ℝ)⁻¹ • w₂ := by abel
          rw [hc2, hs2, smul_add, smul_sub, hab, ← add_smul,
            show ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 by norm_num, one_smul]
        calc inner ℝ w₂ x = inner ℝ (c • e₁ - s • e₂) x :=
              congrArg (fun v => inner ℝ v x) hw₂_eq
          _ = c * inner ℝ e₁ x - s * inner ℝ e₂ x := by
              rw [inner_sub_left, real_inner_smul_left e₁ x c, real_inner_smul_left e₂ x s]
      let S : ℝ → Set (ℝ × ℝ) := fun t =>
        {p | sgn (c * p.2 + s * p.1 - t) ≠ sgn (c * p.2 - s * p.1 - t)}
      have hS_meas : ∀ t, MeasurableSet (S t) := fun t => measurableSet_sgn_pair_ne c s t
      have h_disagree_eq : ∀ t,
          disagree (ltf w₁ t) (ltf w₂ t) =
            (((gaussianReal 0 1).prod (gaussianReal 0 1)) (S t)).toReal := by
        intro t
        unfold disagree ltf
        have hpre : {x : EuclideanSpace ℝ (Fin n) |
            sgn (inner ℝ w₁ x - t) ≠ sgn (inner ℝ w₂ x - t)} =
            (fun x => (inner ℝ e₂ x, inner ℝ e₁ x)) ⁻¹' (S t) := by
          ext x
          simp [S, hw₁_decomp x, hw₂_decomp x]
        have hmeas_pair : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
            (inner ℝ e₂ x, inner ℝ e₁ x)) :=
          ((innerSL ℝ e₂).continuous.measurable).prodMk ((innerSL ℝ e₁).continuous.measurable)
        rw [hpre, ← Measure.map_apply hmeas_pair (hS_meas t),
          map_pair_inner_stdGaussian e₂ e₁ he₂ he₁ horth]
      refine ⟨?_, ?_⟩
      · rw [h_disagree_eq θ, h_disagree_eq 0]
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        rw [Measure.prod_apply (hS_meas θ), Measure.prod_apply (hS_meas 0)]
        apply lintegral_mono
        intro v
        by_cases hv : v = 0
        · subst hv
          simp [S]
        · have hslice : ∀ t, (Prod.mk v ⁻¹' S t) =
              Set.Ico ((t - s * |v|) / c) ((t + s * |v|) / c) := by
            intro t
            ext u
            change (sgn (c * u + s * v - t) ≠ sgn (c * u - s * v - t)) ↔
              (t - s * |v|) / c ≤ u ∧ u < (t + s * |v|) / c
            simp only [sgn]
            rcases lt_or_gt_of_ne hv with hlt | hgt
            · rw [abs_of_neg hlt]
              have hord : c * u + s * v - t < c * u - s * v - t := by nlinarith
              by_cases h1 : 0 ≤ c * u + s * v - t <;> by_cases h2 : 0 ≤ c * u - s * v - t
              · simp only [h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
                intro ⟨_, h⟩
                have := (lt_div_iff₀ hc_pos).mp h
                linarith
              · exfalso; linarith
              · simp only [h1, h2, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
                rw [div_le_iff₀ hc_pos, lt_div_iff₀ hc_pos]
                constructor <;> linarith
              · simp only [h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
                intro ⟨h, _⟩
                have := (div_le_iff₀ hc_pos).mp h
                linarith
            · rw [abs_of_pos hgt]
              have hord : c * u - s * v - t < c * u + s * v - t := by nlinarith
              by_cases h1 : 0 ≤ c * u + s * v - t <;> by_cases h2 : 0 ≤ c * u - s * v - t
              · simp only [h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
                intro ⟨_, h⟩
                have := (lt_div_iff₀ hc_pos).mp h
                linarith
              · simp only [h1, h2, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
                rw [div_le_iff₀ hc_pos, lt_div_iff₀ hc_pos]
                constructor <;> linarith
              · exfalso; linarith
              · simp only [h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
                intro ⟨h, _⟩
                have := (div_le_iff₀ hc_pos).mp h
                linarith
          dsimp only
          rw [hslice θ, hslice 0]
          have heq1 : (θ - s * |v|) / c = θ / c - s * |v| / c := sub_div _ _ _
          have heq2 : (θ + s * |v|) / c = θ / c + s * |v| / c := add_div _ _ _
          have heq3 : (0 - s * |v|) / c = -(s * |v| / c) := by ring
          have heq4 : (0 + s * |v|) / c = s * |v| / c := by ring
          rw [heq1, heq2, heq3, heq4]
          exact gaussian_Ico_shift_le (θ / c) (s * |v| / c) (by positivity)
      · unfold disagree ltf
        let S₀' : Set (ℝ × ℝ) := {p | sgn (c * p.1 + s * p.2) ≠ sgn (c * p.1 - s * p.2)}
        have hS₀'_meas : MeasurableSet S₀' := by
          have heq : S₀' = Prod.swap ⁻¹' S 0 := by ext p; simp [S₀', S]
          rw [heq]
          exact (hS_meas 0).preimage measurable_swap
        have hpre0 : {x : EuclideanSpace ℝ (Fin n) |
            sgn (inner ℝ w₁ x - 0) ≠ sgn (inner ℝ w₂ x - 0)} =
            (fun x => (inner ℝ e₁ x, inner ℝ e₂ x)) ⁻¹' S₀' := by
          ext x
          simp [S₀', hw₁_decomp x, hw₂_decomp x]
        have hmeas_pair0 : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
            (inner ℝ e₁ x, inner ℝ e₂ x)) :=
          ((innerSL ℝ e₁).continuous.measurable).prodMk ((innerSL ℝ e₂).continuous.measurable)
        have horth12 : inner ℝ e₁ e₂ = 0 := by rw [real_inner_comm, horth]
        rw [hpre0, ← Measure.map_apply hmeas_pair0 hS₀'_meas,
          map_pair_inner_stdGaussian e₁ e₂ he₁ he₂ horth12]
        exact polar_sector_measure hα0 hαπ

end Lemma21Proof

open QuantumLTF.Membership in
theorem solution {n : ℕ} (w₁ w₂ : EuclideanSpace ℝ (Fin n)) (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1)
    (θ₁ θ₂ : ℝ) :
    disagree (ltf w₁ θ₁) (ltf w₂ θ₂) ≤ ‖w₁ - w₂‖ / 2 + |θ₁ - θ₂| / Real.sqrt (2 * Real.pi) ∧
      disagree (ltf w₁ 0) (ltf w₂ 0) = Real.arccos (inner ℝ w₁ w₂) / Real.pi := by
  obtain ⟨h_common, h_zero⟩ := disagree_common_and_zero w₁ w₂ h₁ h₂ θ₂
  refine ⟨?_, h_zero⟩
  have h_tri := disagree_triangle (ltf w₁ θ₁) (ltf w₁ θ₂) (ltf w₂ θ₂)
  have h_shift := disagree_shift_le w₁ h₁ θ₁ θ₂
  have hcs := abs_real_inner_le_norm w₁ w₂
  rw [h₁, h₂, mul_one] at hcs
  let α := Real.arccos (inner ℝ w₁ w₂)
  have hα_nonneg : 0 ≤ α / 2 := by
    have := Real.arccos_nonneg (inner ℝ w₁ w₂)
    linarith
  have hα_le : α / 2 ≤ Real.pi / 2 := by
    have := Real.arccos_le_pi (inner ℝ w₁ w₂)
    linarith
  have hjordan : α / Real.pi ≤ Real.sin (α / 2) := by
    have h := Real.mul_le_sin hα_nonneg hα_le
    linarith [show 2 / Real.pi * (α / 2) = α / Real.pi by ring]
  have hsin_eq : Real.sin (α / 2) = ‖w₁ - w₂‖ / 2 := by
    have hcos : Real.cos α = inner ℝ w₁ w₂ :=
      Real.cos_arccos (abs_le.mp hcs).1 (abs_le.mp hcs).2
    have h1 : Real.sin (α / 2) ^ 2 = (1 - Real.cos α) / 2 := by
      have hs := Real.sin_sq (α / 2)
      have hc := Real.cos_sq (α / 2)
      rw [show 2 * (α / 2) = α by ring] at hc
      linarith
    have h2 : (‖w₁ - w₂‖ / 2) ^ 2 = (1 - inner ℝ w₁ w₂) / 2 := by
      have hn := norm_sub_sq_real w₁ w₂
      rw [h₁, h₂] at hn
      linarith [show (‖w₁ - w₂‖ / 2) ^ 2 = ‖w₁ - w₂‖ ^ 2 / 4 by ring]
    have hsq_eq : Real.sin (α / 2) ^ 2 = (‖w₁ - w₂‖ / 2) ^ 2 := by
      rw [h1, h2, hcos]
    have hsin_nonneg : 0 ≤ Real.sin (α / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hα_nonneg (by linarith)
    have hnorm_nonneg : 0 ≤ ‖w₁ - w₂‖ / 2 := by positivity
    nlinarith [sq_abs (Real.sin (α / 2)), sq_abs (‖w₁ - w₂‖ / 2)]
  linarith [h_tri, h_shift, h_common, h_zero, hjordan, hsin_eq]
