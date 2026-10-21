-- Prove2me | solution 1 for RetailerMarketplace.PositiveFee.lemma_2_derivative_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:16:13.049307+00:00
-- url     : https://prove2.me/submissions/5348786e-91ac-4372-a48a-7329b414966f

import Mathlib
import Definitions.Def_RetailerMarketplace_PositiveFee_Model

set_option autoImplicit false
open MeasureTheory RetailerMarketplace.Entry RetailerMarketplace.PositiveFee

lemma rmp_mp_meas (c f : ℝ) : MeasurableSet (mp c f) := by
  unfold mp
  exact measurableSet_le measurable_const (measurable_id.mul_const _)

noncomputable def rmpPhi (c f lam : ℝ) (A : Set ℝ) (v : ℝ) : ℝ :=
  (A \ mp c f).indicator (fun v => piSBM c v) v
    + (A ∩ mp c f).indicator (fun v => piSBMT_M c f lam v) v
    + (mp c f \ A).indicator (fun v => piSBT_M f v) v

lemma rmp_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam : ℝ)
    (hint : Integrable (fun v : ℝ => v) μ) :
    Integrable (fun v => piSBM c v) μ ∧ Integrable (fun v => piSBMT_M c f lam v) μ ∧
      Integrable (fun v => piSBT_M f v) μ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold piSBM; exact hint.sub (integrable_const c)
  · unfold piSBMT_M pbarT
    exact ((hint.sub (integrable_const c)).const_mul lam).add
      ((((hint.const_mul lam).add (integrable_const _)).div_const _).const_mul _)
  · unfold piSBT_M; exact hint.const_mul f

lemma rmp_profit_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam : ℝ)
    (hint : Integrable (fun v : ℝ => v) μ) (A : Set ℝ) (hA : MeasurableSet A) :
    profitM μ c f lam A = ∫ v, rmpPhi c f lam A v ∂μ := by
  obtain ⟨h1, h2, h3⟩ := rmp_integrable μ c f lam hint
  have hm := rmp_mp_meas c f
  unfold profitM rmpPhi
  rw [← integral_indicator (hA.diff hm), ← integral_indicator (hA.inter hm),
    ← integral_indicator (hm.diff hA)]
  rw [integral_add, integral_add]
  · exact h1.indicator (hA.diff hm)
  · exact h2.indicator (hA.inter hm)
  · exact (h1.indicator (hA.diff hm)).add (h2.indicator (hA.inter hm))
  · exact h3.indicator (hm.diff hA)

lemma rmp_pbar_ge (c f lam v : ℝ) (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hv : c ≤ v) : c ≤ pbarT c f lam v := by
  obtain ⟨hl1, hl2⟩ := hlam
  unfold pbarT
  have hD : 0 < 1 - f * (1 - lam) := by nlinarith
  have hD1 : 1 - f * (1 - lam) ≤ 1 := by nlinarith
  rw [le_div_iff₀ hD]
  nlinarith

lemma rmp_pointwise (c f lam v : ℝ) (A : Set ℝ) (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hv : c ≤ v) :
    rmpPhi c 0 lam A v + (f * c * (mp c f).indicator (fun _ => (1 : ℝ)) v
        - f * c * lam * (mp c f ∩ A).indicator (fun _ => (1 : ℝ)) v) ≤ rmpPhi c f lam A v := by
  obtain ⟨hl1, hl2⟩ := hlam
  have hp := rmp_pbar_ge c f lam v hc ⟨hl1, hl2⟩ hf0 hf1 hv
  have h0 : c ≤ v * (1 - 0) := by simpa using hv
  have hfv : f * c ≤ f * v := mul_le_mul_of_nonneg_left hv hf0
  have hpf : f * c ≤ f * pbarT c f lam v := mul_le_mul_of_nonneg_left hp hf0
  have hpf' : (1 - lam) * (f * c) ≤ (1 - lam) * (f * pbarT c f lam v) :=
    mul_le_mul_of_nonneg_left hpf (by linarith)
  have hv1 : 0 ≤ (1 - lam) * (v - c) := mul_nonneg (by linarith) (by linarith)
  by_cases hA : v ∈ A <;> by_cases hM : c ≤ v * (1 - f)
  · simp [rmpPhi, Set.indicator_apply, hA, hM, mp, piSBM, piSBMT_M, piSBT_M, hv]
    nlinarith
  · simp [rmpPhi, Set.indicator_apply, hA, hM, mp, piSBM, piSBMT_M, piSBT_M, hv]
    nlinarith
  · simp [rmpPhi, Set.indicator_apply, hA, hM, mp, piSBM, piSBMT_M, piSBT_M, hv]
    nlinarith
  · simp [rmpPhi, Set.indicator_apply, hA, hM, mp, piSBM, piSBMT_M, piSBT_M, hv]

lemma rmp_phi_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam : ℝ)
    (hint : Integrable (fun v : ℝ => v) μ) (A : Set ℝ) (hA : MeasurableSet A) :
    Integrable (rmpPhi c f lam A) μ := by
  obtain ⟨h1, h2, h3⟩ := rmp_integrable μ c f lam hint
  have hm := rmp_mp_meas c f
  unfold rmpPhi
  exact ((h1.indicator (hA.diff hm)).add (h2.indicator (hA.inter hm))).add
    (h3.indicator (hm.diff hA))

lemma rmp_profit_ge (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam : ℝ)
    (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hsupp : μ (Set.Iio c) = 0) (hint : Integrable (fun v : ℝ => v) μ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    profitM μ c 0 lam A + f * c * (μ.real (mp c f) - lam * μ.real (mp c f ∩ A))
      ≤ profitM μ c f lam A := by
  have hm := rmp_mp_meas c f
  rw [rmp_profit_eq μ c f lam hint A hA, rmp_profit_eq μ c 0 lam hint A hA]
  have hI1 : Integrable ((mp c f).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hm
  have hI2 : Integrable ((mp c f ∩ A).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hm.inter hA)
  have hR : Integrable (fun v => f * c * (mp c f).indicator (fun _ => (1 : ℝ)) v
        - f * c * lam * (mp c f ∩ A).indicator (fun _ => (1 : ℝ)) v) μ :=
    (hI1.const_mul _).sub (hI2.const_mul _)
  have hint0 := rmp_phi_integrable μ c 0 lam hint A hA
  have hintf := rmp_phi_integrable μ c f lam hint A hA
  have hRint : ∫ v, (f * c * (mp c f).indicator (fun _ => (1 : ℝ)) v
        - f * c * lam * (mp c f ∩ A).indicator (fun _ => (1 : ℝ)) v) ∂μ
      = f * c * (μ.real (mp c f) - lam * μ.real (mp c f ∩ A)) := by
    rw [integral_sub (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
      integral_indicator_const _ hm, integral_indicator_const _ (hm.inter hA)]
    simp only [smul_eq_mul, mul_one]
    ring
  have hae : ∀ᵐ v ∂μ, c ≤ v := by
    have e : {a : ℝ | ¬ c ≤ a} = Set.Iio c := by ext a; simp
    rw [ae_iff, e]; exact hsupp
  have := integral_mono_ae (hint0.add hR) hintf (by
    filter_upwards [hae] with v hv
    exact rmp_pointwise c f lam v A hc hlam hf0 hf1 hv)
  simp only [Pi.add_apply] at this
  rw [integral_add hint0 hR, hRint] at this
  linarith

lemma rmp_bdd (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam k : ℝ)
    (hint : Integrable (fun v : ℝ => v) μ) :
    BddAbove (profitM μ c f lam '' {A | Admissible μ k A}) := by
  obtain ⟨h1, h2, h3⟩ := rmp_integrable μ c f lam hint
  have hG : Integrable (fun v => |piSBM c v| + |piSBMT_M c f lam v| + |piSBT_M f v|) μ :=
    ((h1.abs).add h2.abs).add h3.abs
  refine ⟨∫ v, (|piSBM c v| + |piSBMT_M c f lam v| + |piSBT_M f v|) ∂μ, ?_⟩
  rintro _ ⟨A, ⟨hAm, hAk⟩, rfl⟩
  rw [rmp_profit_eq μ c f lam hint A hAm]
  apply integral_mono (rmp_phi_integrable μ c f lam hint A hAm) hG
  intro v
  have a1 := abs_nonneg (piSBM c v)
  have a2 := abs_nonneg (piSBMT_M c f lam v)
  have a3 := abs_nonneg (piSBT_M f v)
  have b1 := le_abs_self (piSBM c v)
  have b2 := le_abs_self (piSBMT_M c f lam v)
  have b3 := le_abs_self (piSBT_M f v)
  unfold rmpPhi
  classical
  simp only [Set.indicator_apply]
  split_ifs <;> linarith

lemma rmp_tail_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume) (r : ENNReal) (hr : r < 1) :
    ∃ t : ℝ, c < t ∧ r < μ (Set.Ici t) := by
  have hsing : μ {c} = 0 := hac (by simp)
  have hIic : μ (Set.Iic c) = 0 := by
    have : Set.Iic c ⊆ Set.Iio c ∪ {c} := by
      intro x hx
      have hx' : x ≤ c := hx
      rcases lt_or_eq_of_le hx' with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact measure_mono_null this (measure_union_null hsupp hsing)
  have hIoi : μ (Set.Ioi c) = 1 := by
    have := prob_compl_eq_one_sub (μ := μ) (measurableSet_Iic (a := c))
    rw [Set.compl_Iic, hIic] at this
    simpa using this
  have hmono : Monotone (fun n : ℕ => Set.Ici (c + 1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    apply Set.Ici_subset_Ici.2
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  have hunion : (⋃ n : ℕ, Set.Ici (c + 1 / ((n : ℝ) + 1))) = Set.Ioi c := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hv
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hv)
      exact ⟨n, by linarith⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion, hIoi] at ht
  have := (tendsto_order.1 ht).1 r hr
  obtain ⟨n, hn⟩ := this.exists
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact ⟨c + 1 / ((n : ℝ) + 1), by linarith, hn⟩


noncomputable def rmpW (c f lam v : ℝ) : ℝ :=
  lam * (v - c) - f * (v - (1 - lam) * (lam * v + c * (1 - lam)))

lemma rmp_pbar_diff (c f lam v : ℝ) (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1 / 2) (hv : c ≤ v) :
    0 ≤ pbarT c f lam v - (lam * v + c * (1 - lam)) ∧
      pbarT c f lam v - (lam * v + c * (1 - lam)) ≤ f * v := by
  obtain ⟨hl1, hl2⟩ := hlam
  unfold pbarT
  have hD : 0 < 1 - f * (1 - lam) := by nlinarith
  have hN : 0 ≤ lam * v + c * (1 - lam) := by nlinarith
  have e : (lam * v + c * (1 - lam)) / (1 - f * (1 - lam)) - (lam * v + c * (1 - lam))
      = (lam * v + c * (1 - lam)) * (f * (1 - lam)) / (1 - f * (1 - lam)) := by
    rw [eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne']
    ring
  rw [e]
  constructor
  · positivity
  · rw [div_le_iff₀ hD]
    have hNv : lam * v + c * (1 - lam) ≤ v := by nlinarith
    have h1 : f * (1 - lam) ≤ 1 / 4 := by nlinarith
    have h2 : (lam * v + c * (1 - lam)) * (f * (1 - lam)) ≤ v * (f * (1 - lam)) :=
      mul_le_mul_of_nonneg_right hNv (by nlinarith)
    nlinarith [mul_nonneg hf0 (by linarith : 0 ≤ v), mul_nonneg (mul_nonneg hf0 hf0) (by linarith : 0 ≤ v)]

lemma rmp_pw2 (c f lam v : ℝ) (A : Set ℝ) (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1 / 2) (hv : c ≤ v) :
    |rmpPhi c f lam A v - (f * v + A.indicator (fun v => rmpW c f lam v) v)| ≤
      2 * f ^ 2 * v + f * (2 * v + 2 * c) *
        (Set.Ico c (c / (1 - f))).indicator (fun _ => (1 : ℝ)) v := by
  obtain ⟨hl1, hl2⟩ := hlam
  have hf1' : 0 < 1 - f := by linarith
  have hIco : v ∈ Set.Ico c (c / (1 - f)) ↔ ¬ (c ≤ v * (1 - f)) := by
    rw [Set.mem_Ico, lt_div_iff₀ hf1', not_le]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  have hpd := rmp_pbar_diff c f lam v hc ⟨hl1, hl2⟩ hf0 hf1 hv
  have h0 : c ≤ v * (1 - 0) := by simpa using hv
  have hv0 : 0 < v := lt_of_lt_of_le hc hv
  have hfv : 0 ≤ f * v := mul_nonneg hf0 hv0.le
  have hf2v : 0 ≤ f ^ 2 * v := mul_nonneg (sq_nonneg f) hv0.le
  have hN0 : 0 ≤ lam * v + c * (1 - lam) := by nlinarith
  have hN0v : lam * v + c * (1 - lam) ≤ v := by nlinarith
  have hl0 : 0 ≤ 1 - lam := by linarith
  have hl1' : 1 - lam ≤ 1 / 2 := by linarith
  by_cases hA : v ∈ A <;> by_cases hM : c ≤ v * (1 - f)
  · have hI : v ∉ Set.Ico c (c / (1 - f)) := fun h => (hIco.1 h) hM
    simp [rmpPhi, Set.indicator_apply, hA, hM, hI, mp, rmpW, piSBM, piSBMT_M, piSBT_M]
    have e : lam * (v - c) + (1 - lam) * f * pbarT c f lam v - (f * v + (lam * (v - c)
        - f * (v - (1 - lam) * (lam * v + c * (1 - lam)))))
        = (1 - lam) * f * (pbarT c f lam v - (lam * v + c * (1 - lam))) := by ring
    rw [e, abs_of_nonneg (mul_nonneg (mul_nonneg hl0 hf0) hpd.1)]
    have := mul_le_mul_of_nonneg_left hpd.2 (mul_nonneg hl0 hf0)
    nlinarith
  · have hI : v ∈ Set.Ico c (c / (1 - f)) := hIco.2 hM
    simp [rmpPhi, Set.indicator_apply, hA, hM, hI, mp, rmpW, piSBM, piSBMT_M, piSBT_M]
    have hlt : v * (1 - f) < c := not_le.mp hM
    have e : v - c - (f * v + (lam * (v - c) - f * (v - (1 - lam) * (lam * v + c * (1 - lam)))))
        = (1 - lam) * (v - c) - f * (1 - lam) * (lam * v + c * (1 - lam)) := by ring
    rw [e]
    have h1 : 0 ≤ (1 - lam) * (v - c) := mul_nonneg hl0 (by linarith)
    have h2 : (1 - lam) * (v - c) ≤ (1 - lam) * (f * v) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hl0
    have h3 : 0 ≤ f * (1 - lam) * (lam * v + c * (1 - lam)) :=
      mul_nonneg (mul_nonneg hf0 hl0) hN0
    have h4 : f * (1 - lam) * (lam * v + c * (1 - lam)) ≤ f * (1 - lam) * v :=
      mul_le_mul_of_nonneg_left hN0v (mul_nonneg hf0 hl0)
    have h5 : (1 - lam) * (f * v) ≤ f * v / 2 := by nlinarith
    have h6 : f * (1 - lam) * v ≤ f * v / 2 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hf0 hc.le]
  · have hI : v ∉ Set.Ico c (c / (1 - f)) := fun h => (hIco.1 h) hM
    simp [rmpPhi, Set.indicator_apply, hA, hM, hI, mp, rmpW, piSBM, piSBMT_M, piSBT_M]
    linarith
  · have hI : v ∈ Set.Ico c (c / (1 - f)) := hIco.2 hM
    simp [rmpPhi, Set.indicator_apply, hA, hM, hI, mp, rmpW, piSBM, piSBMT_M, piSBT_M]
    rw [abs_of_nonneg hf0, abs_of_pos hv0]
    nlinarith [mul_nonneg hf0 hc.le]

lemma rmp_J_close (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam : ℝ)
    (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hsupp : μ (Set.Iio c) = 0)
    (hint : Integrable (fun v : ℝ => v) μ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1 / 2)
    (A : Set ℝ) (hA : MeasurableSet A) :
    |profitM μ c f lam A - (f * ∫ v, v ∂μ + ∫ v in A, rmpW c f lam v ∂μ)| ≤
      2 * f ^ 2 * (∫ v, v ∂μ) + 6 * c * f * μ.real (Set.Ico c (c / (1 - f))) := by
  have hmI : MeasurableSet (Set.Ico c (c / (1 - f))) := measurableSet_Ico
  have hWint : Integrable (fun v => rmpW c f lam v) μ := by
    unfold rmpW
    exact ((hint.sub (integrable_const c)).const_mul lam).sub
      ((hint.sub (((hint.const_mul lam).add (integrable_const _)).const_mul _)).const_mul f)
  have hcmp : Integrable (fun v => f * v + A.indicator (fun v => rmpW c f lam v) v) μ :=
    (hint.const_mul f).add (hWint.indicator hA)
  have hΦ := rmp_phi_integrable μ c f lam hint A hA
  have e1 : profitM μ c f lam A - (f * ∫ v, v ∂μ + ∫ v in A, rmpW c f lam v ∂μ)
      = ∫ v, (rmpPhi c f lam A v - (f * v + A.indicator (fun v => rmpW c f lam v) v)) ∂μ := by
    rw [integral_sub hΦ hcmp, integral_add (hint.const_mul f) (hWint.indicator hA),
      integral_const_mul, integral_indicator hA, rmp_profit_eq μ c f lam hint A hA]
  have hB : Integrable (fun v => 2 * f ^ 2 * v + f * (2 * (c / (1 - f)) + 2 * c) *
      (Set.Ico c (c / (1 - f))).indicator (fun _ => (1 : ℝ)) v) μ :=
    (hint.const_mul _).add (((integrable_const (1 : ℝ)).indicator hmI).const_mul _)
  have hae : ∀ᵐ v ∂μ, c ≤ v := by
    have e : {a : ℝ | ¬ c ≤ a} = Set.Iio c := by ext a; simp
    rw [ae_iff, e]; exact hsupp
  rw [e1]
  have hn := norm_integral_le_of_norm_le hB (by
    filter_upwards [hae] with v hv
    rw [Real.norm_eq_abs]
    refine (rmp_pw2 c f lam v A hc hlam hf0 hf1 hv).trans ?_
    by_cases hm : v ∈ Set.Ico c (c / (1 - f))
    · simp only [Set.indicator_of_mem hm]
      have : v < c / (1 - f) := hm.2
      nlinarith
    · simp only [Set.indicator_of_notMem hm]
      simp)
  rw [Real.norm_eq_abs] at hn
  refine hn.trans ?_
  rw [integral_add (hint.const_mul _) (((integrable_const (1 : ℝ)).indicator hmI).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator_const _ hmI]
  simp only [smul_eq_mul, mul_one]
  have hS : 0 ≤ μ.real (Set.Ico c (c / (1 - f))) := measureReal_nonneg
  have h1f : c / (1 - f) ≤ 2 * c := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  nlinarith [mul_nonneg hf0 hS]

lemma rmp_strip (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) (hac : μ ≪ volume) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ μ.real (Set.Ico c (c + δ)) < ε := by
  intro ε hε
  have hsing : μ {c} = 0 := hac (by simp)
  have hanti : Antitone (fun n : ℕ => Set.Ico c (c + 1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    apply Set.Ico_subset_Ico_right
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  have hinter : (⋂ n : ℕ, Set.Ico c (c + 1 / ((n : ℝ) + 1))) = {c} := by
    ext v
    simp only [Set.mem_iInter, Set.mem_Ico, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      have hlt : c < v := lt_of_le_of_ne (h 0).1 (Ne.symm hne)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
      have := (h n).2
      linarith
    · intro h
      subst h
      intro n
      refine ⟨le_rfl, ?_⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (measurableSet_Ico).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter, hsing] at ht
  have hε' : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have := (tendsto_order.1 ht).2 _ hε'
  obtain ⟨n, hn⟩ := this.exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  have h2 : μ (Set.Ico c (c + 1 / ((n : ℝ) + 1))) < ENNReal.ofReal ε := hn
  exact ENNReal.toReal_lt_of_lt_ofReal h2

lemma rmp_Iic_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume) :
    Continuous (fun t : ℝ => μ.real (Set.Iic t)) := by
  set ρ : ℝ → ℝ := fun v => (μ.rnDeriv volume v).toReal with hρ
  have hρi : Integrable ρ volume := Measure.integrable_toReal_rnDeriv
  have hreal : ∀ s : Set ℝ, μ.real s = ∫ x in s, ρ x := fun s =>
    (Measure.setIntegral_toReal_rnDeriv hac s).symm
  have hcont : Continuous (fun t : ℝ => ∫ x in (0 : ℝ)..t, ρ x) :=
    intervalIntegral.continuous_primitive (fun a b => hρi.intervalIntegrable) 0
  have : (fun t : ℝ => μ.real (Set.Iic t)) =
      fun t => (∫ x in Set.Iic (0 : ℝ), ρ x) + ∫ x in (0 : ℝ)..t, ρ x := by
    funext t
    rw [hreal]
    have := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := t) hρi.integrableOn hρi.integrableOn
    linarith
  rw [this]
  exact continuous_const.add hcont

lemma rmp_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (c k : ℝ) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume) :
    ∃ q : ℝ, c ≤ q ∧ μ.real (Set.Ici q) = k := by
  have hsing : ∀ t : ℝ, μ {t} = 0 := fun t => hac (by simp)
  have hcompl : ∀ t : ℝ, μ.real (Set.Ici t) = 1 - μ.real (Set.Iio t) := by
    intro t
    have := prob_compl_eq_one_sub (μ := μ) (measurableSet_Iio (a := t))
    rw [Set.compl_Iio] at this
    rw [measureReal_def, this, measureReal_def]
    rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp
  have hIio : ∀ t : ℝ, μ.real (Set.Iio t) = μ.real (Set.Iic t) := by
    intro t
    have h : μ (Set.Iic t) = μ (Set.Iio t) := by
      apply le_antisymm
      · calc μ (Set.Iic t) ≤ μ (Set.Iio t ∪ {t}) := by rw [Set.Iio_union_right]
          _ ≤ μ (Set.Iio t) + μ {t} := measure_union_le _ _
          _ = μ (Set.Iio t) := by rw [hsing, add_zero]
      · exact measure_mono Set.Iio_subset_Iic_self
    rw [measureReal_def, measureReal_def, h]
  set g : ℝ → ℝ := fun t => μ.real (Set.Ici t) with hg
  have hgc : Continuous g := by
    have : g = fun t => 1 - μ.real (Set.Iic t) := by
      funext t; rw [hg]; simp only; rw [hcompl, hIio]
    rw [this]
    exact continuous_const.sub (rmp_Iic_cont μ hac)
  have hgc0 : g c = 1 := by
    simp only [hg]; rw [hcompl, hIio]
    have : μ.real (Set.Iic c) = 0 := by
      have : μ (Set.Iic c) = 0 := by
        have h1 : Set.Iic c ⊆ Set.Iio c ∪ {c} := by
          intro x hx
          have hx' : x ≤ c := hx
          rcases lt_or_eq_of_le hx' with h | h
          · exact Or.inl h
          · exact Or.inr h
        exact measure_mono_null h1 (measure_union_null hsupp (hsing c))
      simp [measureReal_def, this]
    rw [this]; norm_num
  -- a point where the tail is below k
  have hanti : Antitone (fun n : ℕ => Set.Ici ((n : ℝ))) := by
    intro m n hmn
    apply Set.Ici_subset_Ici.2
    exact_mod_cast hmn
  have hinter : (⋂ n : ℕ, Set.Ici ((n : ℝ))) = ∅ := by
    ext v
    simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt v
    exact ⟨n, hn⟩
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (measurableSet_Ici).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter, measure_empty] at ht
  have hk' : (0 : ENNReal) < ENNReal.ofReal k := ENNReal.ofReal_pos.2 hk0
  obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).2 _ hk').exists
  have hn' : μ (Set.Ici (n : ℝ)) < ENNReal.ofReal k := hn
  have hgn : g (max c n) ≤ k := by
    have h1 : g (max c n) ≤ g n := by
      simp only [hg]
      exact measureReal_mono (Set.Ici_subset_Ici.2 (le_max_right _ _))
    have h2 : g n ≤ k := by
      simp only [hg, measureReal_def]
      exact (ENNReal.toReal_lt_of_lt_ofReal hn').le
    linarith
  have hcm : c ≤ max c n := le_max_left _ _
  obtain ⟨q, hq, hqk⟩ := intermediate_value_Icc' hcm hgc.continuousOn
    (show k ∈ Set.Icc (g (max c n)) (g c) from ⟨hgn, by rw [hgc0]; exact hk1⟩)
  exact ⟨q, hq.1, hqk⟩

lemma rmp_bath_gen (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (a r q k : ℝ) (ha : 0 < a) (hk : μ.real (Set.Ici q) = k) (A : Set ℝ) (hA : MeasurableSet A)
    (hAk : μ.real A ≤ k) :
    ∫ v in A, a * (v - r) ∂μ ≤
      ∫ v in Set.Ici q, a * (v - r) ∂μ + a * (r - q) * μ.real (Set.Ico q r) := by
  have hw : Integrable (fun v : ℝ => a * (v - r)) μ := (hint.sub (integrable_const r)).const_mul a
  have hmq : MeasurableSet (Set.Ici q) := measurableSet_Ici
  have hI1 : Integrable (A.indicator (fun _ => (1 : ℝ))) μ := (integrable_const (1 : ℝ)).indicator hA
  rcases le_or_gt r q with hrq | hrq
  · -- case r ≤ q
    have hIco : Set.Ico q r = ∅ := Set.Ico_eq_empty_of_le hrq
    rw [hIco]; simp only [measureReal_empty, mul_zero, add_zero]
    set ν : ℝ := a * (q - r) with hν
    have hν0 : 0 ≤ ν := mul_nonneg ha.le (by linarith)
    have hpt : ∀ v : ℝ, A.indicator (fun v => a * (v - r)) v ≤
        (Set.Ici q).indicator (fun v => a * (v - r) - ν) v + ν * A.indicator (fun _ => (1 : ℝ)) v := by
      intro v
      by_cases hvA : v ∈ A <;> by_cases hvq : q ≤ v
      · simp only [Set.indicator_of_mem hvA, Set.mem_Ici, hvq, Set.indicator_of_mem, hν]; nlinarith
      · have hvq' : v ∉ Set.Ici q := hvq
        simp only [Set.indicator_of_mem hvA, Set.indicator_of_notMem hvq', hν]; nlinarith [not_le.mp hvq]
      · have hvA' : v ∉ A := hvA
        have : v ∈ Set.Ici q := hvq
        simp only [Set.indicator_of_notMem hvA', Set.indicator_of_mem this, hν]; nlinarith
      · have hvA' : v ∉ A := hvA
        have hvq' : v ∉ Set.Ici q := hvq
        simp [Set.indicator_of_notMem hvA', Set.indicator_of_notMem hvq']
    have hwν : Integrable (fun v : ℝ => a * (v - r) - ν) μ := hw.sub (integrable_const ν)
    have hR : Integrable (fun v : ℝ => (Set.Ici q).indicator (fun v => a * (v - r) - ν) v
        + ν * A.indicator (fun _ => (1 : ℝ)) v) μ :=
      (hwν.indicator hmq).add (hI1.const_mul ν)
    have hm := integral_mono (hw.indicator hA) hR hpt
    rw [integral_indicator hA] at hm
    have hA1 : ∫ v, ν * A.indicator (fun _ => (1 : ℝ)) v ∂μ = ν * μ.real A := by
      rw [integral_const_mul, integral_indicator_const _ hA]; simp
    rw [integral_add (hwν.indicator hmq) (hI1.const_mul ν), integral_indicator hmq, hA1,
      integral_sub hw.integrableOn (integrable_const ν).integrableOn] at hm
    simp only [setIntegral_const, smul_eq_mul] at hm
    rw [hk] at hm
    have := mul_le_mul_of_nonneg_left hAk hν0
    nlinarith
  · -- case q < r
    set e : ℝ := a * (r - q) with he
    have he0 : 0 ≤ e := mul_nonneg ha.le (by linarith)
    have hmIco : MeasurableSet (Set.Ico q r) := measurableSet_Ico
    have hpt : ∀ v : ℝ, A.indicator (fun v => a * (v - r)) v ≤
        (Set.Ici q).indicator (fun v => a * (v - r)) v +
          e * (Set.Ico q r).indicator (fun _ => (1 : ℝ)) v := by
      intro v
      by_cases hvA : v ∈ A
      · rw [Set.indicator_of_mem hvA]
        by_cases hvq : q ≤ v
        · have h1 : v ∈ Set.Ici q := hvq
          rw [Set.indicator_of_mem h1]
          by_cases hvr : v < r
          · have h2 : v ∈ Set.Ico q r := ⟨hvq, hvr⟩
            rw [Set.indicator_of_mem h2]; nlinarith
          · have h2 : v ∉ Set.Ico q r := fun h => hvr h.2
            rw [Set.indicator_of_notMem h2]; nlinarith
        · have h1 : v ∉ Set.Ici q := hvq
          have h2 : v ∉ Set.Ico q r := fun h => hvq h.1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
          nlinarith [not_le.mp hvq]
      · rw [Set.indicator_of_notMem hvA]
        by_cases hvq : q ≤ v
        · have h1 : v ∈ Set.Ici q := hvq
          rw [Set.indicator_of_mem h1]
          by_cases hvr : v < r
          · have h2 : v ∈ Set.Ico q r := ⟨hvq, hvr⟩
            rw [Set.indicator_of_mem h2]; nlinarith
          · have h2 : v ∉ Set.Ico q r := fun h => hvr h.2
            rw [Set.indicator_of_notMem h2]; nlinarith [not_lt.mp hvr]
        · have h1 : v ∉ Set.Ici q := hvq
          have h2 : v ∉ Set.Ico q r := fun h => hvq h.1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]; simp
    have hmI := integral_mono (hw.indicator hA)
      ((hw.indicator hmq).add (((integrable_const (1 : ℝ)).indicator hmIco).const_mul e)) hpt
    simp only [Pi.add_apply] at hmI
    rw [integral_indicator hA] at hmI
    have hA2 : ∫ v, e * (Set.Ico q r).indicator (fun _ => (1 : ℝ)) v ∂μ
        = e * μ.real (Set.Ico q r) := by
      rw [integral_const_mul, integral_indicator_const _ hmIco]; simp
    rw [integral_add (hw.indicator hmq) (((integrable_const (1 : ℝ)).indicator hmIco).const_mul e),
      integral_indicator hmq, hA2] at hmI
    exact hmI

lemma rmp_bath (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (c lam f q k : ℝ) (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1 / 4) (hq : c ≤ q) (hk : μ.real (Set.Ici q) = k)
    (A : Set ℝ) (hA : MeasurableSet A) (hAk : μ.real A ≤ k) :
    ∫ v in A, rmpW c f lam v ∂μ ≤
      ∫ v in Set.Ici q, rmpW c f lam v ∂μ + 4 * c * f * μ.real (Set.Ico c (c + 4 * c * f)) := by
  obtain ⟨hl1, hl2⟩ := hlam
  set a : ℝ := lam - f * (1 - lam + lam ^ 2) with ha
  have ha1 : 1 / 4 ≤ a := by rw [ha]; nlinarith [mul_nonneg hf0 (sq_nonneg lam), mul_nonneg hf0 (sub_nonneg.2 hl2)]
  have ha2 : a ≤ 1 := by rw [ha]; nlinarith [mul_nonneg hf0 (sq_nonneg (lam - 1/2))]
  have ha0 : 0 < a := by linarith
  set r : ℝ := c * (lam - f * (1 - lam) ^ 2) / a with hr
  have hw : ∀ v, rmpW c f lam v = a * (v - r) := by
    intro v
    unfold rmpW
    rw [hr, ha]
    have : lam - f * (1 - lam + lam ^ 2) ≠ 0 := by rw [← ha]; exact ha0.ne'
    field_simp
    ring
  have hrc : r - c = c * f * lam / a := by
    rw [hr]
    field_simp
    rw [ha]; ring
  have hr1 : 0 ≤ r - c := by rw [hrc]; positivity
  have hr2 : r - c ≤ 4 * c * f := by
    rw [hrc, div_le_iff₀ ha0]
    nlinarith [mul_nonneg hc.le hf0, mul_nonneg (mul_nonneg hc.le hf0) (sub_nonneg.2 hl2)]
  simp_rw [hw]
  have hb := rmp_bath_gen μ hint a r q k ha0 hk A hA hAk
  refine hb.trans ?_
  have hS : 0 ≤ μ.real (Set.Ico c (c + 4 * c * f)) := measureReal_nonneg
  by_cases hqr : q < r
  · have hsub : Set.Ico q r ⊆ Set.Ico c (c + 4 * c * f) := by
      apply Set.Ico_subset_Ico hq
      linarith
    have h1 : μ.real (Set.Ico q r) ≤ μ.real (Set.Ico c (c + 4 * c * f)) :=
      measureReal_mono hsub
    have h2 : 0 ≤ a * (r - q) := mul_nonneg ha0.le (by linarith)
    have h3 : a * (r - q) ≤ 4 * c * f := by nlinarith
    have : a * (r - q) * μ.real (Set.Ico q r) ≤ 4 * c * f * μ.real (Set.Ico c (c + 4 * c * f)) :=
      mul_le_mul h3 h1 measureReal_nonneg (by nlinarith [mul_nonneg hc.le hf0])
    linarith
  · have : Set.Ico q r = ∅ := Set.Ico_eq_empty (not_lt.2 (not_lt.1 hqr) |> fun h => by
      exact not_lt.2 (not_lt.1 hqr))
    rw [this]
    simp only [measureReal_empty, mul_zero, add_zero]
    nlinarith [mul_nonneg (mul_nonneg hc.le hf0) hS]

lemma rmp_opt_set (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (c lam k : ℝ) (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume) :
    ∃ Astar : Set ℝ, MeasurableSet Astar ∧ μ.real Astar ≤ k ∧
      ∀ f : ℝ, 0 ≤ f → f ≤ 1 / 4 → ∀ A : Set ℝ, MeasurableSet A → μ.real A ≤ k →
        ∫ v in A, rmpW c f lam v ∂μ ≤ ∫ v in Astar, rmpW c f lam v ∂μ
          + 4 * c * f * μ.real (Set.Ico c (c + 4 * c * f)) := by
  obtain ⟨hk0, hk1⟩ := hk
  rcases hk0.eq_or_lt with h0 | hpos
  · refine ⟨∅, MeasurableSet.empty, by simp [← h0], ?_⟩
    intro f hf0 hf1 A hA hAk
    have hAz : μ A = 0 := by
      have : μ.real A = 0 := le_antisymm (by rw [h0]; exact hAk) measureReal_nonneg
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
    rw [setIntegral_measure_zero _ hAz]
    simp only [Measure.restrict_empty, integral_zero_measure, zero_add]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.le) hf0) measureReal_nonneg
  · obtain ⟨q, hq, hqk⟩ := rmp_quantile μ c k hpos hk1 hsupp hac
    refine ⟨Set.Ici q, measurableSet_Ici, hqk.le, ?_⟩
    intro f hf0 hf1 A hA hAk
    exact rmp_bath μ hint c lam f q k hc hlam hf0 hf1 hq hqk A hA hAk

set_option maxHeartbeats 2000000 in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (c lam k : ℝ)
    (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume) (hint : Integrable (fun v : ℝ => v) μ)
    (hslip : ¬ (k = 1 ∧ lam = 1)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivWithinAt (fun f : ℝ => PiM μ c f lam k) d (Set.Ici 0) 0 := by
  have hlam' := hlam
  obtain ⟨hl1, hl2⟩ := hlam
  obtain ⟨hk0, hk1⟩ := hk
  obtain ⟨Astar, hAm, hAk, hbath⟩ := rmp_opt_set μ hint c lam k hc hlam' ⟨hk0, hk1⟩ hsupp hac
  have hae : ∀ᵐ v ∂μ, c ≤ v := by
    have e : {a : ℝ | ¬ c ≤ a} = Set.Iio c := by ext a; simp
    rw [ae_iff, e]; exact hsupp
  set I := ∫ v, v ∂μ with hI
  have hI0 : c ≤ I := by
    have := integral_mono_ae (integrable_const c) hint hae
    simpa using this
  set Q : ℝ → ℝ := fun v => v - (1 - lam) * (lam * v + c * (1 - lam)) with hQ
  have hQint : Integrable Q μ :=
    hint.sub (((hint.const_mul lam).add (integrable_const _)).const_mul _)
  have hwQ : ∀ f v, rmpW c f lam v = rmpW c 0 lam v - f * Q v := by
    intro f v; unfold rmpW; simp only [hQ]; ring
  have hWint : ∀ f, Integrable (fun v => rmpW c f lam v) μ := by
    intro f
    unfold rmpW
    exact ((hint.sub (integrable_const c)).const_mul lam).sub
      ((hint.sub (((hint.const_mul lam).add (integrable_const _)).const_mul _)).const_mul f)
  have hintw : ∀ f (A : Set ℝ), ∫ v in A, rmpW c f lam v ∂μ
      = ∫ v in A, rmpW c 0 lam v ∂μ - f * ∫ v in A, Q v ∂μ := by
    intro f A
    simp_rw [hwQ f]
    rw [integral_sub (hWint 0).integrableOn (hQint.integrableOn.const_mul f), integral_const_mul]
  set d : ℝ := I - ∫ v in Astar, Q v ∂μ with hd
  have hadm : ∀ A : Set ℝ, MeasurableSet A → μ.real A ≤ k → Admissible μ k A :=
    fun A hA hAk' => ⟨hA, (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hk0).2 hAk'⟩
  have hadm' : ∀ A : Set ℝ, Admissible μ k A → μ.real A ≤ k := by
    rintro A ⟨hA, h⟩
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal hk0] at this
  have hne : ∀ f, (profitM μ c f lam '' {A | Admissible μ k A}).Nonempty := fun f =>
    ⟨profitM μ c f lam ∅, ∅, ⟨MeasurableSet.empty, by simp⟩, rfl⟩
  have hJ0 : ∀ A : Set ℝ, MeasurableSet A →
      profitM μ c 0 lam A = ∫ v in A, rmpW c 0 lam v ∂μ := by
    intro A hA
    have := rmp_J_close μ c 0 lam hc hlam' hsupp hint le_rfl (by norm_num) A hA
    simp only [zero_mul, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, abs_nonpos_iff] at this
    linarith
  have hP0 : PiM μ c 0 lam k = ∫ v in Astar, rmpW c 0 lam v ∂μ := by
    unfold PiM
    apply le_antisymm
    · apply csSup_le (hne 0)
      rintro _ ⟨A, hA, rfl⟩
      rw [hJ0 A hA.1]
      have := hbath 0 le_rfl (by norm_num) A hA.1 (hadm' A hA)
      simpa using this
    · rw [← hJ0 Astar hAm]
      exact le_csSup (rmp_bdd μ c 0 lam k hint) ⟨Astar, hadm Astar hAm hAk, rfl⟩
  have hest : ∀ f : ℝ, 0 < f → f ≤ 1 / 4 →
      |PiM μ c f lam k - PiM μ c 0 lam k - f * d| ≤
        f * (2 * f * I + 10 * c * μ.real (Set.Ico c (c + 4 * c * f))) := by
    intro f hf0 hf1
    have hf1' : f ≤ 1 / 2 := by linarith
    have hsub : Set.Ico c (c / (1 - f)) ⊆ Set.Ico c (c + 4 * c * f) := by
      apply Set.Ico_subset_Ico_right
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_pos hc hf0, mul_nonneg (mul_pos hc hf0).le hf0.le]
    have hS' : μ.real (Set.Ico c (c / (1 - f))) ≤ μ.real (Set.Ico c (c + 4 * c * f)) :=
      measureReal_mono hsub
    set S := μ.real (Set.Ico c (c + 4 * c * f)) with hS
    have hS0 : 0 ≤ S := measureReal_nonneg
    have hS'0 : 0 ≤ μ.real (Set.Ico c (c / (1 - f))) := measureReal_nonneg
    have hJ := fun A (hA : MeasurableSet A) =>
      rmp_J_close μ c f lam hc hlam' hsupp hint hf0.le hf1' A hA
    have hAstar := abs_le.1 (hJ Astar hAm)
    have hlow : PiM μ c f lam k ≥ profitM μ c f lam Astar :=
      le_csSup (rmp_bdd μ c f lam k hint) ⟨Astar, hadm Astar hAm hAk, rfl⟩
    have hup : PiM μ c f lam k ≤ PiM μ c 0 lam k + f * d
        + (2 * f ^ 2 * I + 6 * c * f * μ.real (Set.Ico c (c / (1 - f))))
        + 4 * c * f * S := by
      apply csSup_le (hne f)
      rintro _ ⟨A, hA, rfl⟩
      have h1 := (abs_le.1 (hJ A hA.1)).2
      have h2 := hbath f hf0.le hf1 A hA.1 (hadm' A hA)
      have h3 := hintw f Astar
      have h4 : f * d = f * I - f * ∫ v in Astar, Q v ∂μ := by rw [hd]; ring
      rw [hP0]
      nlinarith [h1, h2, h3, h4]
    have hfS : 0 ≤ c * f * S := mul_nonneg (mul_nonneg hc.le hf0.le) hS0
    have hfS' : c * f * μ.real (Set.Ico c (c / (1 - f))) ≤ c * f * S :=
      mul_le_mul_of_nonneg_left hS' (mul_nonneg hc.le hf0.le)
    have h3 := hintw f Astar
    have h4 : f * d = f * I - f * ∫ v in Astar, Q v ∂μ := by rw [hd]; ring
    have hlowbd : PiM μ c 0 lam k + f * d - (2 * f ^ 2 * I + 6 * c * f * μ.real (Set.Ico c (c / (1 - f))))
        ≤ PiM μ c f lam k := by
      rw [hP0]
      nlinarith [hAstar.1, hlow, h3, h4]
    rw [abs_le]
    constructor <;> nlinarith [hlowbd, hup, hfS, hfS']
  have hlk : lam * k < 1 := by
    rcases lt_or_eq_of_le (show lam * k ≤ 1 by nlinarith) with h | h
    · exact h
    · exfalso; apply hslip
      constructor <;> nlinarith
  have hdpos : 0 < d := by
    have hAmeas := hAm
    have hg : Integrable (fun v => v - Astar.indicator Q v) μ := hint.sub (hQint.indicator hAmeas)
    have hdint : d = ∫ v, (v - Astar.indicator Q v) ∂μ := by
      rw [integral_sub hint (hQint.indicator hAmeas), integral_indicator hAmeas]
    have hlower : Integrable (fun v => c - c * lam * Astar.indicator (fun _ => (1 : ℝ)) v) μ :=
      (integrable_const c).sub (((integrable_const (1 : ℝ)).indicator hAmeas).const_mul _)
    have hmono := integral_mono_ae hlower hg (by
      filter_upwards [hae] with v hv
      by_cases hvA : v ∈ Astar
      · rw [Set.indicator_of_mem hvA, Set.indicator_of_mem hvA]
        simp only [hQ]
        nlinarith [mul_nonneg (sub_nonneg.2 hl2) (sub_nonneg.2 hv)]
      · rw [Set.indicator_of_notMem hvA, Set.indicator_of_notMem hvA]
        simp; linarith)
    rw [integral_sub (integrable_const c) (((integrable_const (1 : ℝ)).indicator hAmeas).const_mul _),
      integral_const_mul, integral_indicator_const _ hAmeas] at hmono
    have hu : μ.real Set.univ = 1 := by simp [measureReal_def]
    simp only [integral_const, hu, one_smul, smul_eq_mul, mul_one] at hmono
    rw [hdint]
    have : c * lam * μ.real Astar ≤ c * lam * k :=
      mul_le_mul_of_nonneg_left hAk (mul_nonneg hc.le (by linarith))
    nlinarith [mul_pos hc (sub_pos.2 hlk)]
  refine ⟨d, hdpos, ?_⟩
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine Metric.tendsto_nhdsWithin_nhds.2 ?_
  intro ε hε
  have hI1 : 0 < I + 1 := by linarith
  obtain ⟨δ0, hδ0, hS0⟩ := rmp_strip μ c hac (ε / (20 * c)) (by positivity)
  refine ⟨min (1 / 4) (min (δ0 / (4 * c)) (ε / (4 * (I + 1)))), by positivity, ?_⟩
  intro f hfs hfd
  have hfpos : 0 < f := by
    have h1 : 0 ≤ f := hfs.1
    have h2 : f ≠ 0 := hfs.2
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  have hfd' : f < min (1 / 4) (min (δ0 / (4 * c)) (ε / (4 * (I + 1)))) := by
    have := hfd
    rw [Real.dist_eq, sub_zero, abs_of_pos hfpos] at this
    exact this
  have hf14 : f ≤ 1 / 4 := (lt_of_lt_of_le hfd' (min_le_left _ _)).le
  have hfδ : f < δ0 / (4 * c) :=
    lt_of_lt_of_le hfd' ((min_le_right _ _).trans (min_le_left _ _))
  have hfε : f < ε / (4 * (I + 1)) :=
    lt_of_lt_of_le hfd' ((min_le_right _ _).trans (min_le_right _ _))
  have hest' := hest f hfpos hf14
  have hSle : μ.real (Set.Ico c (c + 4 * c * f)) ≤ μ.real (Set.Ico c (c + δ0)) := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    apply Set.Ico_subset_Ico_right
    have : 4 * c * f < δ0 := by
      rw [lt_div_iff₀ (by positivity)] at hfδ
      nlinarith
    linarith
  rw [Real.dist_eq, slope_def_field]
  have e : (PiM μ c f lam k - PiM μ c 0 lam k) / (f - 0) - d
      = (PiM μ c f lam k - PiM μ c 0 lam k - f * d) / f := by
    have hf0' : f ≠ 0 := hfpos.ne'
    rw [sub_zero]
    field_simp
  rw [e, abs_div, abs_of_pos hfpos, div_lt_iff₀ hfpos]
  refine lt_of_le_of_lt hest' ?_
  have h1 : 2 * f * I < ε / 2 := by
    have : f * (4 * (I + 1)) < ε := by rwa [lt_div_iff₀ (by positivity)] at hfε
    nlinarith
  have h2 : 10 * c * μ.real (Set.Ico c (c + 4 * c * f)) < ε / 2 := by
    have : 10 * c * μ.real (Set.Ico c (c + δ0)) < 10 * c * (ε / (20 * c)) :=
      mul_lt_mul_of_pos_left hS0 (by positivity)
    have e2 : 10 * c * (ε / (20 * c)) = ε / 2 := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 10 * c)]
  nlinarith
