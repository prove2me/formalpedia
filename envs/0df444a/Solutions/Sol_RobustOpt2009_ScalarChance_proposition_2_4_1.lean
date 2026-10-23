-- Prove2me | solution 1 for RobustOpt2009.ScalarChance.proposition_2_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:58:41.009913+00:00
-- url     : https://prove2.me/submissions/1d957cc6-8862-4102-aa59-fe3916f83d57

import Definitions.Def_RobustOpt2009_ScalarChance_Setting

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open RobustOpt2009.ScalarChance

theorem g78d_chernoff {L : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S)
    [IsProbabilityMeasure P] (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P) (μminus μplus σ : Fin L → ℝ)
    (hmgf : MGFMajorant P ζ μminus μplus σ) (z : Fin L → ℝ) (t : ℝ) (ht : 0 ≤ t) (a : ℝ) :
    P.real {ω | a ≤ ∑ i, z i * ζ i ω} ≤
      Real.exp (-t * a) * Real.exp (t * boxTerm μminus μplus z +
        t ^ 2 * (∑ i, (σ i) ^ 2 * (z i) ^ 2) / 2) := by
  set Y : Fin L → S → ℝ := fun i ω => z i * ζ i ω with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => measurable_const.mul (hmeas i)
  have hind : iIndepFun Y P :=
    hindep.comp (fun i x => z i * x) (fun i => measurable_const.mul measurable_id)
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin L)),
      Integrable (fun ω => Real.exp (t * Y i ω)) P := by
    intro i _
    have := (hmgf i (t * z i)).1
    convert this using 2 with ω
    simp only [hY]; ring_nf
  have hI := hind.integrable_exp_mul_sum hYm hint
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i, Y i) (μ := P) a ht hI
  have hset : {ω | a ≤ ∑ i, z i * ζ i ω} = {ω | a ≤ (∑ i, Y i) ω} := by
    ext ω; simp [hY, Finset.sum_apply]
  rw [hset]
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  rw [hind.mgf_sum hYm]
  have hb : ∀ i, mgf (Y i) P t ≤ Real.exp (t * max (μminus i * z i) (μplus i * z i) +
      t ^ 2 * ((σ i) ^ 2 * (z i) ^ 2) / 2) := by
    intro i
    have h2 := (hmgf i (t * z i)).2
    have e1 : mgf (Y i) P t = ∫ ω, Real.exp (t * z i * ζ i ω) ∂P := by
      simp only [mgf, hY]; congr 1; funext ω; ring_nf
    rw [e1]
    refine h2.trans (le_of_eq ?_)
    congr 1
    rw [show μminus i * (t * z i) = t * (μminus i * z i) by ring,
      show μplus i * (t * z i) = t * (μplus i * z i) by ring, mul_max_of_nonneg _ _ ht]
    ring
  calc ∏ i, mgf (Y i) P t ≤ ∏ i, Real.exp (t * max (μminus i * z i) (μplus i * z i) +
        t ^ 2 * ((σ i) ^ 2 * (z i) ^ 2) / 2) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hb i)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [boxTerm, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]

theorem g78d_242 {L : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P)
    (μminus μplus σ : Fin L → ℝ)
    (hμ : ∀ i, μminus i ≤ μplus i) (hσ : ∀ i, 0 ≤ σ i)
    (hmgf : MGFMajorant P ζ μminus μplus σ) (z : Fin L → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    P.real {ω | boxTerm μminus μplus z + r * deviation σ z < ∑ i, z i * ζ i ω} ≤
      Real.exp (-(r^2 / 2)) := by
  set V := ∑ i, (σ i) ^ 2 * (z i) ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => by positivity
  set D := deviation σ z with hD
  have hD2 : D ^ 2 = V := Real.sq_sqrt hV0
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  set B := boxTerm μminus μplus z
  rcases hD0.lt_or_eq with hDp | hDz
  · set t := r / D
    have ht : 0 ≤ t := div_nonneg hr hD0
    have h := g78d_chernoff P ζ hmeas hindep μminus μplus σ hmgf z t ht (B + r * D)
    rw [← hV] at h
    have hval : Real.exp (-t * (B + r * D)) * Real.exp (t * B + t ^ 2 * V / 2) =
        Real.exp (-(r ^ 2 / 2)) := by
      rw [← Real.exp_add, ← hD2]
      congr 1
      simp only [t]
      field_simp
      ring
    rw [hval] at h
    refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) h
    have hω' : B + r * D < ∑ i, z i * ζ i ω := hω
    exact hω'.le
  · -- zero deviation: the sum never exceeds the box term
    have hV' : V = 0 := by rw [← hD2, ← hDz]; ring
    have hnull : ∀ n : ℕ, P {ω | B + 1 / ((n : ℝ) + 1) ≤ ∑ i, z i * ζ i ω} = 0 := by
      intro n
      set δ : ℝ := 1 / ((n : ℝ) + 1)
      have hδ : 0 < δ := by positivity
      set q := P.real {ω | B + δ ≤ ∑ i, z i * ζ i ω}
      have hq : ∀ t : ℝ, 0 ≤ t → q ≤ Real.exp (-(t * δ)) := by
        intro t ht
        have h := g78d_chernoff P ζ hmeas hindep μminus μplus σ hmgf z t ht (B + δ)
        rw [← hV, hV', ← Real.exp_add] at h
        convert h using 2; ring
      have hq0 : q = 0 := by
        by_contra hne
        have hqp : 0 < q := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
        have hq1 : q ≤ 1 := measureReal_le_one
        have ht : 0 ≤ (-Real.log q + 1) / δ := by
          have : Real.log q ≤ 0 := Real.log_nonpos hqp.le hq1
          exact div_nonneg (by linarith) hδ.le
        have := hq _ ht
        rw [div_mul_cancel₀ _ hδ.ne', neg_add, neg_neg, Real.exp_add, Real.exp_log hqp] at this
        have he : Real.exp (-1) < 1 := by
          simpa using Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
        nlinarith
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hq0
    have hsub : {ω | B + r * D < ∑ i, z i * ζ i ω} ⊆
        ⋃ n : ℕ, {ω | B + 1 / ((n : ℝ) + 1) ≤ ∑ i, z i * ζ i ω} := by
      intro ω hω
      have hω' : B + r * D < ∑ i, z i * ζ i ω := hω
      rw [← hDz, mul_zero, add_zero] at hω'
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hω')
      exact Set.mem_iUnion.2 ⟨n, (by linarith : B + 1 / ((n : ℝ) + 1) ≤ ∑ i, z i * ζ i ω)⟩
    have h0 : P {ω | B + r * D < ∑ i, z i * ζ i ω} = 0 :=
      measure_mono_null hsub (measure_iUnion_null hnull)
    rw [measureReal_def, h0, ENNReal.toReal_zero]
    positivity

theorem g78d_dev {L : ℕ} (σ y : Fin L → ℝ) :
    deviation σ y = ‖(WithLp.toLp 2 (fun i => σ i * y i) : EuclideanSpace ℝ (Fin L))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [deviation, Real.norm_eq_abs, sq_abs, mul_pow]

theorem solution {L : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P)
    (μminus μplus σ : Fin L → ℝ)
    (hμ : ∀ i, μminus i ≤ μplus i) (hσ : ∀ i, 0 ≤ σ i)
    (hmgf : MGFMajorant P ζ μminus μplus σ) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    Convex ℝ {z : ℝ × (Fin L → ℝ) | safeValue μminus μplus σ ε z ≤ 0} ∧
    (∀ z, safeValue μminus μplus σ ε z ≤ 0 → violation P ζ z ≤ ε) := by
  have hr : 0 ≤ radius ε := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · intro z hz z' hz' a b ha hb hab
    simp only [Set.mem_setOf_eq, safeValue] at hz hz' ⊢
    have hbox : boxTerm μminus μplus (a • z + b • z').2 ≤
        a * boxTerm μminus μplus z.2 + b * boxTerm μminus μplus z'.2 := by
      simp only [boxTerm, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => max_le ?_ ?_
      · have h1 := le_max_left (μminus i * z.2 i) (μplus i * z.2 i)
        have h2 := le_max_left (μminus i * z'.2 i) (μplus i * z'.2 i)
        nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
      · have h1 := le_max_right (μminus i * z.2 i) (μplus i * z.2 i)
        have h2 := le_max_right (μminus i * z'.2 i) (μplus i * z'.2 i)
        nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    have hdev : deviation σ (a • z + b • z').2 ≤ a * deviation σ z.2 + b * deviation σ z'.2 := by
      rw [g78d_dev, g78d_dev, g78d_dev]
      have e : (WithLp.toLp 2 (fun i => σ i * (a • z + b • z').2 i) : EuclideanSpace ℝ (Fin L)) =
          a • (WithLp.toLp 2 (fun i => σ i * z.2 i) : EuclideanSpace ℝ (Fin L)) +
          b • (WithLp.toLp 2 (fun i => σ i * z'.2 i) : EuclideanSpace ℝ (Fin L)) := by
        ext i
        simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply]
        ring
      rw [e]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have h1 : (a • z + b • z').1 = a * z.1 + b * z'.1 := by simp
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left hdev hr, mul_nonneg ha (le_refl (0:ℝ))]
  · intro z hz
    have h := g78d_242 P ζ hmeas hindep μminus μplus σ hμ hσ hmgf z.2 (radius ε) hr
    have hexp : Real.exp (-(radius ε ^ 2 / 2)) = ε := by
      have hl : 0 ≤ 2 * Real.log (1 / ε) := by
        have : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε.1]; linarith)
        linarith
      rw [radius, Real.sq_sqrt hl, show -(2 * Real.log (1 / ε) / 2) = Real.log ε by
        rw [one_div, Real.log_inv]; ring, Real.exp_log hε.1]
    rw [hexp] at h
    refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) h
    have hω' : 0 < z.1 + ∑ i, ζ i ω * z.2 i := hω
    show boxTerm μminus μplus z.2 + radius ε * deviation σ z.2 < ∑ i, z.2 i * ζ i ω
    simp only [safeValue] at hz
    have : ∑ i, ζ i ω * z.2 i = ∑ i, z.2 i * ζ i ω := Finset.sum_congr rfl fun i _ => mul_comm _ _
    linarith
