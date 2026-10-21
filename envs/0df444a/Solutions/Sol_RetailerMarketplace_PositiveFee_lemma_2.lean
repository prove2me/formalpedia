-- Prove2me | solution 1 for RetailerMarketplace.PositiveFee.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:50:36.400913+00:00
-- url     : https://prove2.me/submissions/3275448d-c987-49a3-b1e5-17ccd92e4d40

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

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (c lam k : ℝ)
    (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume) (hint : Integrable (fun v : ℝ => v) μ)
    (hslip : ¬ (k = 1 ∧ lam = 1))
    (fstar : ℝ) (hfstar : fstar ∈ Set.Icc (0 : ℝ) 1)
    (hopt : ∀ f ∈ Set.Icc (0 : ℝ) 1, PiM μ c f lam k ≤ PiM μ c fstar lam k) :
    0 < fstar := by
  by_contra hneg
  have hf0' : fstar = 0 := le_antisymm (not_lt.mp hneg) hfstar.1
  subst hf0'
  obtain ⟨hl1, hl2⟩ := hlam
  obtain ⟨hk0, hk1⟩ := hk
  have hlk : lam * k < 1 := by
    rcases lt_or_eq_of_le (show lam * k ≤ 1 by nlinarith) with h | h
    · exact h
    · exfalso; apply hslip
      constructor <;> nlinarith
  have hlt : ENNReal.ofReal (lam * k) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hlk
  obtain ⟨t, hct, ht⟩ := rmp_tail_mass μ c hsupp hac _ hlt
  have ht0 : 0 < t := lt_trans hc hct
  set f : ℝ := 1 - c / t with hf
  have hct1 : c / t < 1 := (div_lt_one ht0).2 hct
  have hct0 : 0 < c / t := div_pos hc ht0
  have hf0 : 0 < f := by rw [hf]; linarith
  have hf1 : f < 1 := by rw [hf]; linarith
  have hmp : mp c f = Set.Ici t := by
    ext v
    simp only [mp, Set.mem_setOf_eq, Set.mem_Ici]
    have : 1 - f = c / t := by rw [hf]; ring
    rw [this]
    constructor
    · intro h
      by_contra hv
      rw [not_le] at hv
      have : v * (c / t) < c := by
        rw [mul_div_assoc', div_lt_iff₀ ht0]
        nlinarith
      linarith
    · intro h
      have : t * (c / t) ≤ v * (c / t) := mul_le_mul_of_nonneg_right h hct0.le
      have e : t * (c / t) = c := by field_simp
      linarith
  have hm : lam * k < μ.real (mp c f) := by
    rw [hmp]
    have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (measure_ne_top μ _)).1 ht
    exact this
  set d := f * c * (μ.real (mp c f) - lam * k) with hd
  have hdpos : 0 < d := by
    rw [hd]; apply mul_pos (mul_pos hf0 hc); linarith
  have hne : (profitM μ c 0 lam '' {A | Admissible μ k A}).Nonempty :=
    ⟨_, ⟨∅, ⟨MeasurableSet.empty, by simp⟩, rfl⟩⟩
  have hlt0 : PiM μ c 0 lam k - d / 2 < PiM μ c 0 lam k := by linarith
  obtain ⟨y, ⟨A, ⟨hAm, hAk⟩, rfl⟩, hy⟩ := exists_lt_of_lt_csSup hne hlt0
  have hAk' : μ.real A ≤ k := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hAk
    rwa [ENNReal.toReal_ofReal hk0] at this
  have hinter : μ.real (mp c f ∩ A) ≤ k :=
    le_trans (measureReal_mono Set.inter_subset_right) hAk'
  have hge := rmp_profit_ge μ c f lam hc ⟨hl1, hl2⟩ hf0.le hf1.le hsupp hint A hAm
  have hbdd := rmp_bdd μ c f lam k hint
  have hle : profitM μ c f lam A ≤ PiM μ c f lam k := le_csSup hbdd ⟨A, ⟨hAm, hAk⟩, rfl⟩
  have hopt' := hopt f ⟨hf0.le, hf1.le⟩
  have h1 : f * c * (μ.real (mp c f) - lam * μ.real (mp c f ∩ A)) ≥ d := by
    rw [hd]
    apply mul_le_mul_of_nonneg_left _ (mul_pos hf0 hc).le
    have : lam * μ.real (mp c f ∩ A) ≤ lam * k := mul_le_mul_of_nonneg_left hinter (by linarith)
    linarith
  unfold PiM at hopt' hy hlt0 hle
  linarith
