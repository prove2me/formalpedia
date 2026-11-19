-- Prove2me | solution 1 for UnionVolEst.lemma_28
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:35:43.834544+00:00
-- url     : https://prove2.me/submissions/f6af989d-e799-4b7f-8a19-d208adeec567

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- log(1+x) ≥ 2x/(2+x) for x ≥ 0 -/
lemma log_one_add_ge (x : ℝ) (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun y => Real.log (1 + y) - 2 * y / (2 + y)
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy
      have hy : (0:ℝ) ≤ y := hy
      apply ContinuousAt.continuousWithinAt
      have h1 : (1 + y) ≠ 0 := by linarith
      have h2 : (2 + y) ≠ 0 := by linarith
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (0:ℝ) < y := hy
      apply DifferentiableAt.differentiableWithinAt
      have h1 : (1 + y) ≠ 0 := by linarith
      have h2 : (2 + y) ≠ 0 := by linarith
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (0:ℝ) < y := hy
      have hd : HasDerivAt g (1 / (1 + y) - (2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
        have a1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + y)) y := by
          have := ((hasDerivAt_id y).const_add 1).log (by simp; linarith)
          simpa [one_div] using this
        have a2 : HasDerivAt (fun y : ℝ => 2 * y / (2 + y))
            ((2 * 1 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
          have := ((hasDerivAt_id' y).const_mul 2).div ((hasDerivAt_id' y).const_add 2)
            (by linarith)
          exact this
        exact (a1.sub a2).congr_deriv (by ring)
      rw [hd.deriv]
      have : (1:ℝ) / (1 + y) - (2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2 =
          y ^ 2 / ((1 + y) * (2 + y) ^ 2) := by
        field_simp; ring
      rw [this]; positivity
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [g, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at this
  linarith

/-- (1-δ) log(1-δ) ≥ -δ + δ²/2 for δ ∈ [0,1) -/
lemma one_sub_log_ge (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    -δ + δ ^ 2 / 2 ≤ (1 - δ) * Real.log (1 - δ) := by
  let h : ℝ → ℝ := fun y => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2
  have hmono : MonotoneOn h (Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro y hy
      apply ContinuousAt.continuousWithinAt
      have : (1 - y) ≠ 0 := by linarith [hy.2]
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ico] at hy
      apply DifferentiableAt.differentiableWithinAt
      have : (1 - y) ≠ 0 := by linarith [hy.2]
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ico] at hy
      have hne : (1 - y) ≠ 0 := by linarith [hy.2]
      have hd : HasDerivAt h (-Real.log (1 - y) - y) y := by
        have a1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
          simpa using (hasDerivAt_id y).const_sub 1
        have a2 := (a1.mul (a1.log hne))
        have a3 := (a2.add (hasDerivAt_id y)).sub ((hasDerivAt_pow 2 y).div_const 2)
        exact a3.congr_deriv (by field_simp; ring)
      rw [hd.deriv]
      have := Real.log_le_sub_one_of_pos (by linarith [hy.2] : (0:ℝ) < 1 - y)
      linarith
  have := hmono (mem_Ico.mpr ⟨le_rfl, by norm_num⟩) (mem_Ico.mpr ⟨h0, h1⟩) h0
  simp only [h, sub_zero, Real.log_one, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at this
  linarith

lemma chord_exp' (c z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (c * z) ≤ 1 + z * (Real.exp c - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ c) (by linarith : 0 ≤ 1 - z) hz0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc Real.exp (c * z) = Real.exp (z * c) := by ring_nf
    _ ≤ (1 - z) + z * Real.exp c := h
    _ = _ := by ring


section Gen
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (Y : Ω → ℝ) (M : ℝ) (hmgf : ∀ c, mgf Y P c ≤ Real.exp ((Real.exp c - 1) * M))
  (hint : ∀ c, Integrable (fun ω => Real.exp (c * Y ω)) P)
include hmgf hint

lemma lower_gen (t : ℝ) (ht : 0 < t) (htM : t ≤ M) :
    P.real {ω | Y ω ≤ t} ≤ Real.exp (t * Real.log (M / t) + t - M) := by
  have hM0 : 0 < M := lt_of_lt_of_le ht htM
  set c := Real.log (M / t) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hec : Real.exp (-c) = t / M := by
    rw [hc, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := Y) t (neg_nonpos.mpr hc0) (hint (-c))
  refine h1.trans ?_
  have h2 := hmgf (-c)
  rw [hec] at h2
  calc Real.exp (- -c * t) * mgf Y P (-c)
      ≤ Real.exp (- -c * t) * Real.exp ((t / M - 1) * M) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma upper_gen (t : ℝ) (hM : 0 < M) (htM : M ≤ t) :
    P.real {ω | t ≤ Y ω} ≤ Real.exp (-(t * Real.log (t / M)) + t - M) := by
  have ht : 0 < t := lt_of_lt_of_le hM htM
  set c := Real.log (t / M) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ hM]; linarith)
  have hec : Real.exp c = t / M := by rw [hc, Real.exp_log (by positivity)]
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := Y) t hc0 (hint c)
  refine h1.trans ?_
  have h2 := hmgf c
  rw [hec] at h2
  calc Real.exp (-c * t) * mgf Y P c
      ≤ Real.exp (-c * t) * Real.exp ((t / M - 1) * M) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma lower_zero_gen : P.real {ω | Y ω ≤ 0} ≤ Real.exp (-M / 3) := by
  set c := Real.log (3 / 2) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by norm_num)
  have hec : Real.exp (-c) = 2 / 3 := by
    rw [hc, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := Y) 0 (neg_nonpos.mpr hc0) (hint (-c))
  refine h1.trans ?_
  have h2 := hmgf (-c)
  rw [hec] at h2
  rw [mul_zero, Real.exp_zero, one_mul]
  refine h2.trans (le_of_eq ?_)
  congr 1; ring

lemma two_sided_gen (hM0 : 0 ≤ M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    P.real {ω | δ * M ≤ |Y ω - M|} ≤ 2 * Real.exp (-(δ ^ 2 * M / 3)) := by
  have htriv : P.real {ω | δ * M ≤ |Y ω - M|} ≤ 1 := measureReal_le_one
  rcases hM0.eq_or_lt with hz | hMpos
  · refine htriv.trans ?_
    rw [← hz]; simp
  rcases hδ0.eq_or_lt with hδz | hδpos
  · refine htriv.trans ?_
    rw [← hδz]; simp
  have hsub : {ω | δ * M ≤ |Y ω - M|} ⊆
      {ω | (1 + δ) * M ≤ Y ω} ∪ {ω | Y ω ≤ (1 - δ) * M} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; linarith
  have hup : P.real {ω | (1 + δ) * M ≤ Y ω} ≤ Real.exp (-(δ ^ 2 * M / 3)) := by
    refine (upper_gen P Y M hmgf hint ((1 + δ) * M) hMpos (by nlinarith)).trans ?_
    apply Real.exp_le_exp.mpr
    have hlog : Real.log ((1 + δ) * M / M) = Real.log (1 + δ) := by
      rw [show (1 + δ) * M / M = 1 + δ by field_simp]
    rw [hlog]
    have hl := log_one_add_ge δ hδ0
    have h2 : 0 < 2 + δ := by linarith
    rw [div_le_iff₀ h2] at hl
    have hl' := mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ (1 + δ) * M)
    have key0 : δ ^ 2 * M / (2 + δ) ≤ (1 + δ) * M * Real.log (1 + δ) - δ * M := by
      rw [div_le_iff₀ h2]; nlinarith
    have : δ ^ 2 * M / 3 ≤ δ ^ 2 * M / (2 + δ) :=
      div_le_div_of_nonneg_left (by positivity) h2 (by linarith)
    linarith
  have hlow : P.real {ω | Y ω ≤ (1 - δ) * M} ≤ Real.exp (-(δ ^ 2 * M / 3)) := by
    rcases hδ1.lt_or_eq with hlt | heq
    · have ht : 0 < (1 - δ) * M := by nlinarith
      refine (lower_gen P Y M hmgf hint ((1 - δ) * M) ht (by nlinarith)).trans ?_
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (M / ((1 - δ) * M)) = -Real.log (1 - δ) := by
        rw [show M / ((1 - δ) * M) = (1 - δ)⁻¹ by field_simp, Real.log_inv]
      rw [hlog]
      have := one_sub_log_ge δ hδ0 hlt
      have h3 : δ ^ 2 * M / 3 ≤ δ ^ 2 * M / 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
      nlinarith
    · rw [heq]
      have := lower_zero_gen P Y M hmgf hint
      simp only [sub_self, zero_mul]
      refine this.trans (le_of_eq ?_)
      congr 1; ring
  calc P.real {ω | δ * M ≤ |Y ω - M|}
      ≤ P.real ({ω | (1 + δ) * M ≤ Y ω} ∪ {ω | Y ω ≤ (1 - δ) * M}) := measureReal_mono hsub
    _ ≤ P.real {ω | (1 + δ) * M ≤ Y ω} + P.real {ω | Y ω ≤ (1 - δ) * M} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith

end Gen

lemma poisson_hasSum (lam : ℝ≥0) (c : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-(lam:ℝ)) * (lam:ℝ) ^ n / (n.factorial)) * Real.exp (c * n))
      (Real.exp ((Real.exp c - 1) * lam)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((lam:ℝ) * Real.exp c)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-(lam:ℝ)))
  have e1 : (fun n : ℕ => (Real.exp (-(lam:ℝ)) * (lam:ℝ) ^ n / (n.factorial)) * Real.exp (c * n)) =
      fun i : ℕ => Real.exp (-(lam:ℝ)) * (((lam:ℝ) * Real.exp c) ^ i / (i.factorial)) := by
    funext n
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm (n:ℝ) c]
    ring
  have e2 : Real.exp ((Real.exp c - 1) * lam) = Real.exp (-(lam:ℝ)) * Real.exp ((lam:ℝ) * Real.exp c) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2]; exact h2

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (X : Ω → ℕ) (hX : HasLaw X (poissonMeasure lam) P) (ε : ℝ) (hε : 0 < ε) :
    P {ω | ε * (lam : ℝ) < |(X ω : ℝ) - lam|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * lam) / (2 * (1 + ε)))) := by
  set M : ℝ := (lam : ℝ) with hM
  have hpush : P {ω | ε * M < |(X ω : ℝ) - M|} = poissonMeasure lam {k : ℕ | ε * M < |(k : ℝ) - M|} :=
    hX.measure_eq (p := fun k : ℕ => ε * M < |(k : ℝ) - M|) (MeasurableSet.of_discrete)
  rw [hpush]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (poissonMeasure lam) _)]
  apply ENNReal.ofReal_le_ofReal
  change (poissonMeasure lam).real _ ≤ _
  have hM0 : 0 ≤ M := lam.2
  have hint : ∀ c, Integrable (fun k : ℕ => Real.exp (c * (k : ℝ))) (poissonMeasure lam) := by
    intro c
    rw [integrable_poissonMeasure_iff]
    have := (poisson_hasSum lam c).summable
    refine this.congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmgf : ∀ c, mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) c ≤ Real.exp ((Real.exp c - 1) * M) := by
    intro c
    rw [mgf, integral_poissonMeasure' (hint c)]
    simp only [smul_eq_mul]
    rw [(poisson_hasSum lam c).tsum_eq]
  rcases hM0.eq_or_lt with hz | hMpos
  · refine measureReal_le_one.trans ?_
    rw [← hz]; simp
  have h2e : 0 < 2 * (1 + ε) := by linarith
  have hup : (poissonMeasure lam).real {k : ℕ | (1 + ε) * M ≤ (k : ℝ)} ≤
      Real.exp (-(ε ^ 2 * M) / (2 * (1 + ε))) := by
    refine (upper_gen (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) M hmgf hint ((1 + ε) * M) hMpos
      (by nlinarith)).trans ?_
    apply Real.exp_le_exp.mpr
    have hlog : Real.log ((1 + ε) * M / M) = Real.log (1 + ε) := by
      rw [show (1 + ε) * M / M = 1 + ε by field_simp]
    rw [hlog]
    have hl := log_one_add_ge ε hε.le
    have h2 : 0 < 2 + ε := by linarith
    rw [div_le_iff₀ h2] at hl
    have hl' := mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ (1 + ε) * M)
    have key0 : ε ^ 2 * M / (2 + ε) ≤ (1 + ε) * M * Real.log (1 + ε) - ε * M := by
      rw [div_le_iff₀ h2]; nlinarith
    have : ε ^ 2 * M / (2 * (1 + ε)) ≤ ε ^ 2 * M / (2 + ε) :=
      div_le_div_of_nonneg_left (by positivity) h2 (by linarith)
    rw [neg_div]
    linarith
  rcases lt_or_ge ε 1 with hlt | hge
  · have hsub : {k : ℕ | ε * M < |(k : ℝ) - M|} ⊆
        {k : ℕ | (1 + ε) * M ≤ (k : ℝ)} ∪ {k : ℕ | (k : ℝ) ≤ (1 - ε) * M} := by
      intro k hk
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hk ⊢
      rcases lt_abs.mp hk with h | h
      · left; linarith
      · right; linarith
    have hlow : (poissonMeasure lam).real {k : ℕ | (k : ℝ) ≤ (1 - ε) * M} ≤
        Real.exp (-(ε ^ 2 * M) / (2 * (1 + ε))) := by
      have ht : 0 < (1 - ε) * M := by nlinarith
      refine (lower_gen (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) M hmgf hint ((1 - ε) * M) ht
        (by nlinarith)).trans ?_
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (M / ((1 - ε) * M)) = -Real.log (1 - ε) := by
        rw [show M / ((1 - ε) * M) = (1 - ε)⁻¹ by field_simp, Real.log_inv]
      rw [hlog]
      have := one_sub_log_ge ε hε.le hlt
      have h3 : ε ^ 2 * M / (2 * (1 + ε)) ≤ ε ^ 2 * M / 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      rw [neg_div]
      nlinarith
    calc (poissonMeasure lam).real {k : ℕ | ε * M < |(k : ℝ) - M|}
        ≤ (poissonMeasure lam).real ({k : ℕ | (1 + ε) * M ≤ (k : ℝ)} ∪ {k : ℕ | (k : ℝ) ≤ (1 - ε) * M}) :=
          measureReal_mono hsub
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ _ := by linarith
  · have hsub : {k : ℕ | ε * M < |(k : ℝ) - M|} ⊆ {k : ℕ | (1 + ε) * M ≤ (k : ℝ)} := by
      intro k hk
      simp only [Set.mem_ofPred_eq] at hk ⊢
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      rcases lt_abs.mp hk with h | h
      · linarith
      · nlinarith
    calc (poissonMeasure lam).real {k : ℕ | ε * M < |(k : ℝ) - M|}
        ≤ (poissonMeasure lam).real {k : ℕ | (1 + ε) * M ≤ (k : ℝ)} := measureReal_mono hsub
      _ ≤ Real.exp (-(ε ^ 2 * M) / (2 * (1 + ε))) := hup
      _ ≤ _ := by have := Real.exp_pos (-(ε ^ 2 * M) / (2 * (1 + ε))); linarith
