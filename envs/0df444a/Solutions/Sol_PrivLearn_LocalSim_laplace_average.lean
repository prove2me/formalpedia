-- Prove2me | solution 1 for PrivLearn.LocalSim.laplace_average
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:17:03.487428+00:00
-- url     : https://prove2.me/submissions/d232830f-bed0-4988-8325-7c62fda85c23

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy

open MeasureTheory Set

private lemma laplace_mgf_le (s t : ℝ) (hs : 0 < s) (ht : |t| ≤ 1 / (2 * s)) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (t * x)) ∂(PrivLearn.Generic.laplace s)) ≤
      ENNReal.ofReal (Real.exp (2 * s ^ 2 * t ^ 2)) := by
  obtain ⟨ht_lo, ht_hi⟩ := abs_le.mp ht
  have hs_inv : 0 < 1 / s := by positivity
  have h2s_lt : 1 / (2 * s) < 1 / s := by
    rw [div_lt_div_iff₀ (by positivity) hs]
    linarith
  set a₁ := t + 1 / s
  set a₂ := t - 1 / s
  have ha₁ : 0 < a₁ := by dsimp [a₁]; linarith
  have ha₂ : a₂ < 0 := by dsimp [a₂]; linarith
  have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s))) := by
    fun_prop
  have hm2 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x))) := by
    fun_prop
  unfold PrivLearn.Generic.laplace
  rw [lintegral_withDensity_eq_lintegral_mul volume hm1 hm2]
  have h_prod : (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s)) *
      ENNReal.ofReal (Real.exp (t * x))) =
      fun x : ℝ => ENNReal.ofReal (1 / (2 * s)) *
        ENNReal.ofReal (Real.exp (t * x - |x| / s)) := by
    ext x
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_eq_inv_mul, mul_assoc, ← Real.exp_add]
    ring_nf
  change (∫⁻ a, (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s)) *
    ENNReal.ofReal (Real.exp (t * x))) a) ≤ _
  rw [h_prod, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_compl _ measurableSet_Iic, compl_Iic]
  have h_iic : (∫⁻ x in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (t * x - |x| / s))) =
      ENNReal.ofReal (1 / a₁) := by
    have heq : EqOn (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x - |x| / s)))
        (fun x : ℝ => ENNReal.ofReal (Real.exp (a₁ * x))) (Iic 0) := by
      intro x hx
      dsimp [a₁]
      rw [abs_of_nonpos hx]
      ring_nf
    rw [setLIntegral_congr_fun measurableSet_Iic heq,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic ha₁ 0)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
      integral_exp_mul_Iic ha₁ 0]
    simp
  have h_ioi : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (t * x - |x| / s))) =
      ENNReal.ofReal (-1 / a₂) := by
    have heq : EqOn (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x - |x| / s)))
        (fun x : ℝ => ENNReal.ofReal (Real.exp (a₂ * x))) (Ioi 0) := by
      intro x hx
      dsimp [a₂]
      rw [abs_of_pos hx]
      ring_nf
    rw [setLIntegral_congr_fun measurableSet_Ioi heq,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha₂ 0)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
      integral_exp_mul_Ioi ha₂ 0]
    simp [neg_div]
  rw [h_iic, h_ioi]
  have ha₂_pos : 0 < -1 / a₂ := div_pos_of_neg_of_neg (by norm_num) ha₂
  rw [← ENNReal.ofReal_add (by positivity) ha₂_pos.le,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hst : |s * t| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hs]
    calc s * |t| ≤ s * (1 / (2 * s)) := mul_le_mul_of_nonneg_left ht hs.le
      _ = 1 / 2 := by field_simp
  have hst_sq : s ^ 2 * t ^ 2 ≤ 1 / 4 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hst
    nlinarith
  have h_denom : 0 < 1 - s ^ 2 * t ^ 2 := by linarith
  have h_alg : 1 / (2 * s) * (1 / a₁ + -1 / a₂) = 1 / (1 - s ^ 2 * t ^ 2) := by
    dsimp [a₁, a₂]
    have ha₁_ne : t + 1 / s ≠ 0 := ha₁.ne'
    have ha₂_ne : t - 1 / s ≠ 0 := ha₂.ne
    have hs_ne : s ≠ 0 := hs.ne'
    have hd_ne : 1 - s ^ 2 * t ^ 2 ≠ 0 := h_denom.ne'
    have h1 : t + 1 / s = (s * t + 1) / s := by field_simp
    have h2 : t - 1 / s = (s * t - 1) / s := by field_simp
    have hst1 : s * t + 1 ≠ 0 := by obtain ⟨_, _⟩ := abs_le.mp hst; linarith
    have hst2 : s * t - 1 ≠ 0 := by obtain ⟨_, _⟩ := abs_le.mp hst; linarith
    rw [h1, h2]
    field_simp
    ring
  rw [h_alg]
  calc 1 / (1 - s ^ 2 * t ^ 2) ≤ 1 + 2 * s ^ 2 * t ^ 2 := by
        rw [div_le_iff₀ h_denom]
        nlinarith [sq_nonneg (s * t)]
    _ ≤ Real.exp (2 * s ^ 2 * t ^ 2) := by
        linarith [Real.add_one_le_exp (2 * s ^ 2 * t ^ 2)]

private lemma lintegral_pi_prod (μ : Measure ℝ) [SigmaFinite μ] (g : ℝ → ENNReal)
    (hg : Measurable g) :
    ∀ n : ℕ, (∫⁻ η : Fin n → ℝ, (∏ i : Fin n, g (η i)) ∂(Measure.pi fun _ : Fin n => μ)) =
      (∫⁻ x : ℝ, g x ∂μ) ^ n
  | 0 => by simp [Measure.pi_empty_univ]
  | m + 1 => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp : (μ.prod (Measure.pi fun _ : Fin m => μ)).map e.symm =
        Measure.pi (fun _ : Fin (m + 1) => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm.map_eq
    have hm_prod : Measurable (fun η : Fin (m + 1) → ℝ => ∏ i : Fin (m + 1), g (η i)) :=
      Finset.measurable_prod Finset.univ fun i _ => hg.comp (measurable_pi_apply i)
    rw [← hmp, lintegral_map hm_prod e.symm.measurable]
    have h_split : (fun p : ℝ × (Fin m → ℝ) => ∏ i : Fin (m + 1), g (e.symm p i)) =
        fun p : ℝ × (Fin m → ℝ) => g p.1 * ∏ j : Fin m, g (p.2 j) := by
      ext ⟨x, y⟩
      have he : e.symm (x, y) = (0 : Fin (m + 1)).insertNth x y := rfl
      rw [he, Fin.prod_univ_succAbove _ 0, Fin.insertNth_apply_same]
      simp
    rw [h_split]
    have hm_prod_m : Measurable (fun y : Fin m → ℝ => ∏ j : Fin m, g (y j)) :=
      Finset.measurable_prod Finset.univ fun j _ => hg.comp (measurable_pi_apply j)
    rw [lintegral_prod_mul hg.aemeasurable hm_prod_m.aemeasurable,
      lintegral_pi_prod μ g hg m, pow_succ']

private lemma laplace_sum_tail (s t a : ℝ) (hs : 0 < s) (ht : |t| ≤ 1 / (2 * s)) (n : ℕ) :
    (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s)
      {η : Fin n → ℝ | a ≤ t * ∑ i, η i} ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2) - a)) := by
  set μ : Measure ℝ := PrivLearn.Generic.laplace s
  have : SigmaFinite μ := by
    dsimp [μ, PrivLearn.Generic.laplace]
    infer_instance
  set P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
  set f : (Fin n → ℝ) → ENNReal := fun η => ENNReal.ofReal (Real.exp (t * ∑ i, η i))
  have hf_meas : Measurable f := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact measurable_const.mul (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)
  have h_sub : {η : Fin n → ℝ | a ≤ t * ∑ i, η i} ⊆
      {η : Fin n → ℝ | ENNReal.ofReal (Real.exp a) ≤ f η} := by
    intro η hη
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hη)
  have h_markov := mul_meas_ge_le_lintegral (μ := P) hf_meas (ENNReal.ofReal (Real.exp a))
  have h_prod_eq : ∀ η : Fin n → ℝ, f η = ∏ i : Fin n, ENNReal.ofReal (Real.exp (t * η i)) := by
    intro η
    dsimp [f]
    rw [Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  have h_lint : ∫⁻ η, f η ∂P ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2))) := by
    have hg_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x))) := by fun_prop
    rw [lintegral_congr h_prod_eq]
    dsimp [P]
    rw [lintegral_pi_prod μ _ hg_meas]
    calc (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (t * x)) ∂μ) ^ n
        ≤ (ENNReal.ofReal (Real.exp (2 * s ^ 2 * t ^ 2))) ^ n :=
          pow_le_pow_left' (laplace_mgf_le s t hs ht) n
      _ = ENNReal.ofReal ((Real.exp (2 * s ^ 2 * t ^ 2)) ^ n) :=
          (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
      _ = ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2))) := by
          rw [← Real.exp_nat_mul]
  have h_le : ENNReal.ofReal (Real.exp a) * P {η : Fin n → ℝ | a ≤ t * ∑ i, η i} ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2))) :=
    (mul_le_mul_of_nonneg_left (measure_mono h_sub) zero_le).trans (h_markov.trans h_lint)
  have h_mul := mul_le_mul_of_nonneg_left h_le (zero_le : 0 ≤ ENNReal.ofReal (Real.exp (-a)))
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, ENNReal.ofReal_one, one_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at h_mul
  rw [sub_eq_neg_add]
  exact h_mul

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (b ε τ β : ℝ) (n : ℕ), 0 < b → 0 < ε → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β ≤ 1 / 2 →
        c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ n →
        (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε))
            {η | τ / 2 < |(1 / (n : ℝ)) * ∑ i, η i|}
          ≤ ENNReal.ofReal (β / 2) := by
  refine ⟨384, by norm_num, ?_⟩
  intro b ε τ β n hb hε hτ hετ hβ hβ_half hn
  have hlog : 0 < Real.log (1 / β) := by
    apply Real.log_pos
    rw [one_lt_div hβ]
    linarith
  have hn_pos_real : 0 < (n : ℝ) := by
    refine lt_of_lt_of_le ?_ hn
    positivity
  set s := 2 * b / ε
  have hs : 0 < s := by positivity
  set δ := τ / 2
  have hδ : 0 < δ := by positivity
  have hδ_le_s : δ ≤ s := by
    dsimp [δ, s]
    rw [div_le_div_iff₀ (by norm_num) hε]
    linarith
  set t := δ / (4 * s ^ 2)
  have ht_pos : 0 < t := by positivity
  have ht_bound : |t| ≤ 1 / (2 * s) := by
    rw [abs_of_pos ht_pos]
    dsimp [t]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hnt_bound : |-t| ≤ 1 / (2 * s) := by
    rwa [abs_neg]
  set P := Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s
  set a := (n : ℝ) * (t * δ)
  have h_sub : {η : Fin n → ℝ | τ / 2 < |(1 / (n : ℝ)) * ∑ i, η i|} ⊆
      {η : Fin n → ℝ | a ≤ t * ∑ i, η i} ∪ {η : Fin n → ℝ | a ≤ (-t) * ∑ i, η i} := by
    intro η hη
    change τ / 2 < |(1 / (n : ℝ)) * ∑ i, η i| at hη
    simp only [mem_union]
    have h1 : δ < |∑ i, η i| / (n : ℝ) := by
      have : (1 / (n : ℝ)) * ∑ i, η i = (∑ i, η i) / (n : ℝ) := one_div_mul_eq_div _ _
      rwa [this, abs_div, abs_of_pos hn_pos_real] at hη
    rw [lt_div_iff₀ hn_pos_real] at h1
    rcases le_abs'.mp h1.le with hneg | hpos
    · right
      show a ≤ (-t) * ∑ i, η i
      dsimp [a]
      nlinarith
    · left
      show a ≤ t * ∑ i, η i
      dsimp [a]
      nlinarith
  have h_exp_eq : (n : ℝ) * (2 * s ^ 2 * t ^ 2) - a = -(n : ℝ) * (ε ^ 2 * τ ^ 2) / (128 * b ^ 2) := by
    dsimp [a, t, δ, s]
    have hb_ne : b ≠ 0 := hb.ne'
    have hε_ne : ε ≠ 0 := hε.ne'
    field_simp
    ring
  have h_exp_eq_neg : (n : ℝ) * (2 * s ^ 2 * (-t) ^ 2) - a =
      -(n : ℝ) * (ε ^ 2 * τ ^ 2) / (128 * b ^ 2) := by
    rw [neg_sq, h_exp_eq]
  have h1 := laplace_sum_tail s t a hs ht_bound n
  have h2 := laplace_sum_tail s (-t) a hs hnt_bound n
  rw [h_exp_eq] at h1
  rw [h_exp_eq_neg] at h2
  calc P {η : Fin n → ℝ | τ / 2 < |(1 / (n : ℝ)) * ∑ i, η i|}
      ≤ P ({η : Fin n → ℝ | a ≤ t * ∑ i, η i} ∪ {η : Fin n → ℝ | a ≤ (-t) * ∑ i, η i}) :=
        measure_mono h_sub
    _ ≤ P {η : Fin n → ℝ | a ≤ t * ∑ i, η i} + P {η : Fin n → ℝ | a ≤ (-t) * ∑ i, η i} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * (ε ^ 2 * τ ^ 2) / (128 * b ^ 2))) +
        ENNReal.ofReal (Real.exp (-(n : ℝ) * (ε ^ 2 * τ ^ 2) / (128 * b ^ 2))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 * τ ^ 2) / (128 * b ^ 2))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        ring_nf
    _ ≤ ENNReal.ofReal (β / 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hn' : 384 * Real.log (1 / β) * b ^ 2 ≤ (n : ℝ) * (ε ^ 2 * τ ^ 2) := by
          rwa [div_le_iff₀ (by positivity)] at hn
        have hexp_le : -(n : ℝ) * (ε ^ 2 * τ ^ 2) / (128 * b ^ 2) ≤
            -(Real.log (1 / β) + Real.log (1 / β) + Real.log (1 / β)) := by
          rw [div_le_iff₀ (by positivity)]
          linarith
        have h_exp3 : Real.exp (-(Real.log (1 / β) + Real.log (1 / β) + Real.log (1 / β))) =
            β ^ 3 := by
          rw [Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]
          field_simp
        have h_mon := Real.exp_le_exp.mpr hexp_le
        rw [h_exp3] at h_mon
        nlinarith [sq_nonneg β]
