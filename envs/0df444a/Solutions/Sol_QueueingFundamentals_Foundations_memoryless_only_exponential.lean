-- Prove2me | solution 1 for QueueingFundamentals.Foundations.memoryless_only_exponential
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:48:38.179235+00:00
-- url     : https://prove2.me/submissions/27097d30-6c11-4bbf-a36d-c8381efd9c74

import Mathlib

open MeasureTheory ProbabilityTheory


namespace QueueingFundamentals.Foundations

open Set Filter Topology

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (T : Ω → ℝ) (hTm : Measurable T)

/-- survival function -/
noncomputable def qfbG (t : ℝ) : ℝ := (μ {ω | t < T ω}).toReal

include hTm in
lemma qfb_split (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (t u : ℝ) (htu : t ≤ u) :
    μ {ω | t ≤ T ω ∧ T ω ≤ u} = μ {ω | t < T ω} - μ {ω | u < T ω} := by
  have h1 : μ {ω | t ≤ T ω ∧ T ω ≤ u} = μ {ω | t < T ω ∧ T ω ≤ u} := by
    apply le_antisymm
    · calc μ {ω | t ≤ T ω ∧ T ω ≤ u} ≤ μ ({ω | t < T ω ∧ T ω ≤ u} ∪ {ω | T ω = t}) := by
            apply measure_mono
            intro ω ⟨h1, h2⟩
            rcases h1.lt_or_eq with h | h
            · exact Or.inl ⟨h, h2⟩
            · exact Or.inr h.symm
        _ ≤ _ := measure_union_le _ _
        _ = _ := by rw [hcont t, add_zero]
    · exact measure_mono (fun ω ⟨h1, h2⟩ => ⟨h1.le, h2⟩)
  rw [h1]
  have hs : {ω | t < T ω ∧ T ω ≤ u} = {ω | t < T ω} \ {ω | u < T ω} := by
    ext ω; simp [not_lt]
  have hsub : {ω | u < T ω} ⊆ {ω | t < T ω} := fun ω (h : u < T ω) =>
    (show t < T ω from lt_of_le_of_lt htu h)
  have hms : MeasurableSet {ω | u < T ω} := hTm measurableSet_Ioi
  rw [hs, measure_diff hsub hms.nullMeasurableSet (measure_ne_top _ _)]

include hTm in
lemma qfb_split_real (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (t u : ℝ) (htu : t ≤ u) :
    (μ {ω | t ≤ T ω ∧ T ω ≤ u}).toReal = qfbG μ T t - qfbG μ T u := by
  have hsub : {ω | u < T ω} ⊆ {ω | t < T ω} := fun ω (h : u < T ω) =>
    (show t < T ω from lt_of_le_of_lt htu h)
  rw [qfb_split μ T hTm hcont t u htu, ENNReal.toReal_sub_of_le
    (measure_mono hsub) (measure_ne_top _ _)]
  rfl

lemma qfbG_anti (t u : ℝ) (htu : t ≤ u) : qfbG μ T u ≤ qfbG μ T t := by
  have hsub : {ω | u < T ω} ⊆ {ω | t < T ω} := fun ω (h : u < T ω) =>
    (show t < T ω from lt_of_le_of_lt htu h)
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

lemma qfbG_nonneg (t : ℝ) : 0 ≤ qfbG μ T t := ENNReal.toReal_nonneg

include hTm in
lemma qfb_ge_eq (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (t : ℝ) :
    μ {ω | t ≤ T ω} = μ {ω | t < T ω} := by
  apply le_antisymm
  · calc μ {ω | t ≤ T ω} ≤ μ ({ω | t < T ω} ∪ {ω | T ω = t}) := by
          apply measure_mono
          intro ω (h1 : t ≤ T ω)
          rcases h1.lt_or_eq with h | h
          · exact Or.inl h
          · exact Or.inr h.symm
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [hcont t, add_zero]
  · exact measure_mono (fun ω (h : t < T ω) => (show t ≤ T ω from h.le))

include hTm in
lemma qfbG_zero (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (hnonneg : μ {ω | T ω < 0} = 0) :
    qfbG μ T 0 = 1 := by
  have : μ (T ⁻¹' Ioi 0)ᶜ = 0 := by
    apply measure_mono_null _ (measure_union_null hnonneg (hcont 0))
    intro ω (h : ¬ 0 < T ω)
    rcases (not_lt.mp h).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h
  rw [prob_compl_eq_zero_iff (hTm measurableSet_Ioi)] at this
  unfold qfbG; rw [show {ω | 0 < T ω} = T ⁻¹' Ioi 0 from rfl, this]; simp

include hTm in
lemma qfbG_mul (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (hnonneg : μ {ω | T ω < 0} = 0)
    (hmem : ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ ≤ t₁ →
      cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀})
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    qfbG μ T (t + s) = qfbG μ T t * qfbG μ T s := by
  have h := hmem t (t + s) ht (by linarith)
  rw [cond_apply (show MeasurableSet {ω | t ≤ T ω} from hTm measurableSet_Ici)] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, show t + s - t = s by ring,
    qfb_split_real μ T hTm hcont 0 s hs, qfbG_zero μ T hTm hcont hnonneg,
    qfb_ge_eq μ T hTm hcont t,
    show {ω | t ≤ T ω} ∩ {ω | T ω ≤ t + s} = {ω | t ≤ T ω ∧ T ω ≤ t + s} from rfl,
    qfb_split_real μ T hTm hcont t (t + s) (by linarith)] at h2
  change (qfbG μ T t)⁻¹ * _ = _ at h2
  by_cases h0 : qfbG μ T t = 0
  · have := qfbG_anti μ T t (t + s) (by linarith)
    have := qfbG_nonneg μ T (t + s)
    rw [h0] at *; simp; linarith
  · field_simp at h2
    linarith

end

theorem memoryless_only_exponential_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → ℝ) (hTm : Measurable T)
    (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (hnonneg : μ {ω | T ω < 0} = 0)
    (hmem : ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ ≤ t₁ →
      cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀}) :
    ∃ lam : ℝ, 0 < lam ∧ μ.map T = expMeasure lam := by
  have hmul := qfbG_mul μ T hTm hcont hnonneg hmem
  have hanti := qfbG_anti μ T
  have hnn := qfbG_nonneg μ T
  have hG0 := qfbG_zero μ T hTm hcont hnonneg
  set G := qfbG μ T with hGdef
  have hpow : ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ, G (n * x) = G x ^ n := by
    intro x hx n
    induction n with
    | zero => simp [hG0]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hmul _ _ (by positivity) hx, ih, pow_succ]
  set c := G 1 with hc
  -- c > 0
  have hcpos : 0 < c := by
    by_contra hneg
    have hc0 : c = 0 := le_antisymm (not_lt.mp hneg) (hnn 1)
    have hk : ∀ k : ℕ, G (1 / (k + 1 : ℝ)) = 0 := by
      intro k
      have := hpow (1 / (k + 1 : ℝ)) (by positivity) (k + 1)
      rw [show ((k + 1 : ℕ) : ℝ) * (1 / (k + 1 : ℝ)) = 1 by push_cast; field_simp, ← hc, hc0]
        at this
      exact pow_eq_zero_iff (by omega) |>.mp this.symm
    have hnull : μ {ω | 0 < T ω} = 0 := by
      have : {ω | 0 < T ω} = ⋃ k : ℕ, {ω | 1 / (k + 1 : ℝ) < T ω} := by
        ext ω; simp only [mem_setOf_eq, mem_iUnion]
        constructor
        · intro h
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt h
          exact ⟨k, hk⟩
        · rintro ⟨k, hk⟩; exact lt_trans (by positivity) hk
      rw [this]
      apply measure_iUnion_null
      intro k
      have := hk k
      rw [hGdef, qfbG, ENNReal.toReal_eq_zero_iff] at this
      exact this.resolve_right (measure_ne_top _ _)
    have : G 0 = 0 := by rw [hGdef, qfbG, hnull]; rfl
    rw [hG0] at this; norm_num at this
  -- c < 1
  have hclt : c < 1 := by
    by_contra hneg
    have hc1 : c = 1 := le_antisymm (by rw [← hG0]; exact hanti 0 1 zero_le_one) (not_lt.mp hneg)
    have hk : ∀ n : ℕ, μ {ω | T ω ≤ n} = 0 := by
      intro n
      have h1 := hpow 1 zero_le_one n
      rw [mul_one, ← hc, hc1, one_pow] at h1
      have : μ {ω | (n : ℝ) < T ω} = 1 := by
        rw [hGdef, qfbG] at h1
        have h3 := ENNReal.ofReal_toReal (measure_ne_top μ {ω | (n : ℝ) < T ω})
        rw [h1, ENNReal.ofReal_one] at h3; exact h3.symm
      have h4 := prob_compl_eq_one_sub (μ := μ) (hTm (measurableSet_Ioi (a := (n : ℝ))))
      rw [show (T ⁻¹' Ioi (n : ℝ)) = {ω | (n : ℝ) < T ω} from rfl, this, tsub_self] at h4
      rw [← h4]; congr 1; ext ω; simp
    have : μ univ = 0 := by
      have : (univ : Set Ω) = ⋃ n : ℕ, {ω | T ω ≤ n} := by
        ext ω; simp only [mem_univ, mem_setOf_eq, mem_iUnion, true_iff]
        exact exists_nat_ge (T ω)
      rw [this]; exact measure_iUnion_null hk
    simp at this
  set lam := -Real.log c with hlam
  have hlampos : 0 < lam := by
    rw [hlam, neg_pos]; exact Real.log_neg hcpos hclt
  have hexpc : Real.exp (-lam) = c := by rw [hlam, neg_neg, Real.exp_log hcpos]
  -- G at rationals
  have hrat : ∀ m k : ℕ, 0 < k → G (m / k) = Real.exp (-lam * (m / k)) := by
    intro m k hk
    have h1 := hpow ((m : ℝ) / k) (by positivity) k
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [show (k : ℝ) * (m / k) = (m : ℝ) * 1 by field_simp, hpow 1 zero_le_one m, ← hc, ← hexpc,
      ← Real.exp_nat_mul] at h1
    have h2 : Real.exp (-lam * (m / k)) ^ k = Real.exp (m * -lam) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [← h2] at h1
    exact (pow_left_inj₀ (hnn _) (Real.exp_pos _).le (by omega)).mp h1.symm
  -- squeeze
  have hval : ∀ t : ℝ, 0 ≤ t → G t = Real.exp (-lam * t) := by
    intro t ht
    have hup : ∀ k : ℕ, G t ≤ Real.exp (-lam * (t - 1 / (k + 1 : ℝ))) := by
      intro k
      set m := ⌊(k + 1 : ℝ) * t⌋₊ with hm
      have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have h1 : (m : ℝ) ≤ (k + 1 : ℝ) * t := Nat.floor_le (by positivity)
      have h2 : (k + 1 : ℝ) * t < m + 1 := Nat.lt_floor_add_one _
      have hle : (m : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ t := by
        rw [div_le_iff₀ hk]; push_cast; linarith
      calc G t ≤ G (m / ((k + 1 : ℕ) : ℝ)) := hanti _ _ hle
        _ = Real.exp (-lam * (m / ((k + 1 : ℕ) : ℝ))) := hrat m (k + 1) (by omega)
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonpos_left _ (by linarith)
          rw [le_div_iff₀ hk]; push_cast
          rw [sub_mul, div_mul_cancel₀ _ (by positivity)]; linarith
    have hlow : ∀ k : ℕ, Real.exp (-lam * (t + 1 / (k + 1 : ℝ))) ≤ G t := by
      intro k
      set m := ⌊(k + 1 : ℝ) * t⌋₊ with hm
      have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have h1 : (m : ℝ) ≤ (k + 1 : ℝ) * t := Nat.floor_le (by positivity)
      have h2 : (k + 1 : ℝ) * t < m + 1 := Nat.lt_floor_add_one _
      have hle : t ≤ ((m + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
        rw [le_div_iff₀ hk]; push_cast; linarith
      calc Real.exp (-lam * (t + 1 / (k + 1 : ℝ)))
          ≤ Real.exp (-lam * (((m + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))) := by
            apply Real.exp_le_exp.mpr
            apply mul_le_mul_of_nonpos_left _ (by linarith)
            rw [div_le_iff₀ hk]; push_cast
            rw [add_mul, div_mul_cancel₀ _ (by positivity)]; linarith
        _ = G (((m + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) := (hrat (m + 1) (k + 1) (by omega)).symm
        _ ≤ G t := hanti _ _ hle
    have hlim0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc1 : Continuous (fun x : ℝ => Real.exp (-lam * (t - x))) := by fun_prop
    have hc2 : Continuous (fun x : ℝ => Real.exp (-lam * (t + x))) := by fun_prop
    have l1 := (hc1.tendsto 0).comp hlim0
    have l2 := (hc2.tendsto 0).comp hlim0
    simp only [sub_zero, add_zero] at l1 l2
    apply le_antisymm
    · exact ge_of_tendsto l1 (Eventually.of_forall (fun k => by simpa using hup k))
    · exact le_of_tendsto l2 (Eventually.of_forall (fun k => by simpa using hlow k))
  refine ⟨lam, hlampos, ?_⟩
  haveI := isProbabilityMeasure_expMeasure hlampos
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hTm.aemeasurable
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply hTm measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hlampos]
  split_ifs with ha
  · have h4 := prob_compl_eq_one_sub (μ := μ) (hTm (measurableSet_Ioi (a := a)))
    have h5 : (T ⁻¹' Ioi a)ᶜ = T ⁻¹' Iic a := by ext ω; simp
    rw [h5] at h4
    rw [h4, show (T ⁻¹' Ioi a) = {ω | a < T ω} from rfl,
      ← ENNReal.ofReal_toReal (measure_ne_top μ {ω | a < T ω})]
    change 1 - ENNReal.ofReal (G a) = _
    rw [hval a ha, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
    congr 2; ring
  · rw [ENNReal.ofReal_zero]
    apply measure_mono_null _ hnonneg
    intro ω (h : T ω ≤ a)
    show T ω < 0
    linarith

end QueueingFundamentals.Foundations

open QueueingFundamentals.Foundations


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → ℝ) (hTm : Measurable T)
    (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (hnonneg : μ {ω | T ω < 0} = 0)
    (hmem : ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ ≤ t₁ →
      cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀}) :
    ∃ lam : ℝ, 0 < lam ∧ μ.map T = expMeasure lam := by
  exact memoryless_only_exponential_core μ T hTm hcont hnonneg hmem
