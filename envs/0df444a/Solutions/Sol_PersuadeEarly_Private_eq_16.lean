-- Prove2me | solution 1 for PersuadeEarly.Private.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:22:06.834999+00:00
-- url     : https://prove2.me/submissions/948c8dc4-bc60-4f5f-b98b-7d57b3cea553

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism
import Definitions.Def_PersuadeEarly_Private_PrivateMech


open MeasureTheory Set

namespace PersuadeEarly.Private.PEAux

variable {M : Model}

lemma f_nonneg (hM : M.Standing) : ∀ v ∈ Icc 0 M.b, 0 ≤ M.f v := by
  intro v hv
  rcases eq_or_lt_of_le hv.2 with h | h
  · subst h
    have hc : ContinuousWithinAt M.f (Ico 0 M.b) M.b :=
      (hM.f_cont M.b hv).mono Ico_subset_Icc_self
    have hne : (nhdsWithin M.b (Ico 0 M.b)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hM.b_pos.ne]
      exact right_mem_Icc.2 hM.b_pos.le
    exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun x hx => (hM.f_pos x hx).le)
  · exact (hM.f_pos v ⟨hv.1, h⟩).le

lemma f_intOn (hM : M.Standing) : IntegrableOn M.f (Icc 0 M.b) volume :=
  hM.f_cont.integrableOn_compact isCompact_Icc

theorem mu_finite (hM : M.Standing) : IsFiniteMeasure M.mu := by
  unfold Model.mu
  exact isFiniteMeasure_withDensity_ofReal (f_intOn hM).2

lemma integral_mu (hM : M.Standing) (g : ℝ → ℝ) :
    ∫ v, g v ∂M.mu = ∫ v in Icc 0 M.b, M.f v * g v := by
  unfold Model.mu
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
    simp [ENNReal.toReal_ofReal (f_nonneg hM v hv)]
  · exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hM.f_cont.aemeasurable measurableSet_Icc)
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- integral of a "threshold" integrand. -/
lemma integral_mu_ite (hM : M.Standing) (a : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ M.b) (g : ℝ → ℝ) :
    ∫ v, (if a ≤ v then g v else 0) ∂M.mu = ∫ v in a..M.b, M.f v * g v := by
  rw [integral_mu hM]
  have : (fun v => M.f v * (if a ≤ v then g v else 0)) =
      (Ici a).indicator (fun v => M.f v * g v) := by
    ext v; by_cases h : a ≤ v <;> simp [h, indicator]
  have hs : Icc 0 M.b ∩ Ici a = Icc a M.b := by
    ext v; simp only [mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨ha0.trans h1, h2⟩, h1⟩
  rw [this, setIntegral_indicator measurableSet_Ici, hs,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

lemma Fbar_eq_integral (hM : M.Standing) (y : ℝ) (hy0 : 0 ≤ y) (hyb : y ≤ M.b) :
    M.Fbar y = ∫ v in y..M.b, M.f v := by
  unfold Model.Fbar
  have h1 : (M.mu (Ioi y)).toReal = ∫ v, (Ioi y).indicator 1 v ∂M.mu := by
    rw [integral_indicator_one measurableSet_Ioi]; rfl
  rw [h1, integral_mu hM]
  have : (fun v => M.f v * (Ioi y).indicator 1 v) = (Ioi y).indicator M.f := by
    ext v; by_cases h : y < v <;> simp [h, indicator]
  have hs : Icc 0 M.b ∩ Ioi y = Ioc y M.b := by
    ext v; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hy0.trans h1.le, h2⟩, h1⟩
  rw [this, setIntegral_indicator measurableSet_Ioi, hs,
    intervalIntegral.integral_of_le hyb]

lemma Fbar_zero (hM : M.Standing) : M.Fbar 0 = 1 := by
  rw [Fbar_eq_integral hM 0 le_rfl hM.b_pos.le, hM.f_int]

lemma Fbar_b (hM : M.Standing) : M.Fbar M.b = 0 := by
  rw [Fbar_eq_integral hM _ hM.b_pos.le le_rfl, intervalIntegral.integral_same]

lemma Fbar_contOn (hM : M.Standing) : ContinuousOn M.Fbar (Icc 0 M.b) := by
  have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
    (a := 0) (b := M.b) (f := M.f) (by rw [uIcc_of_le hM.b_pos.le]; exact f_intOn hM)
  rw [uIcc_of_le hM.b_pos.le] at h
  exact h.congr fun y hy => Fbar_eq_integral hM y hy.1 hy.2

lemma f_intervalIntegrable (hM : M.Standing) {x y : ℝ} (hx : x ∈ Icc 0 M.b) (hy : y ∈ Icc 0 M.b) :
    IntervalIntegrable M.f volume x y :=
  (hM.f_cont.mono (uIcc_subset_Icc hx hy)).intervalIntegrable

lemma Fbar_sub (hM : M.Standing) {x y : ℝ} (hx : x ∈ Icc 0 M.b) (hy : y ∈ Icc 0 M.b) :
    M.Fbar x - M.Fbar y = ∫ v in x..y, M.f v := by
  rw [Fbar_eq_integral hM x hx.1 hx.2, Fbar_eq_integral hM y hy.1 hy.2]
  rw [sub_eq_iff_eq_add, intervalIntegral.integral_add_adjacent_intervals]
  · exact f_intervalIntegrable hM hx hy
  · exact f_intervalIntegrable hM hy ⟨hM.b_pos.le, le_rfl⟩

lemma Fbar_strictAnti (hM : M.Standing) : StrictAntiOn M.Fbar (Icc 0 M.b) := by
  intro x hx y hy hxy
  have := Fbar_sub hM hx hy
  have hpos : 0 < ∫ v in x..y, M.f v :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (f_intervalIntegrable hM hx hy)
      (fun v hv => hM.f_pos v ⟨hx.1.trans hv.1.le, hv.2.trans_le hy.2⟩) hxy
  linarith

lemma Fbar_nonneg (y : ℝ) : 0 ≤ M.Fbar y := ENNReal.toReal_nonneg

lemma Fbar_le_one (hM : M.Standing) (y : ℝ) : M.Fbar y ≤ 1 := by
  have := mu_finite hM
  have h0 : M.Fbar 0 = 1 := Fbar_zero hM
  unfold Model.Fbar at h0 ⊢
  have hu : (M.mu (Ioi y)).toReal ≤ (M.mu univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have hu2 : M.mu univ = M.mu (Ioi 0) := by
    unfold Model.mu
    rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Measure.restrict_univ]
    apply setLIntegral_congr
    have hs : Icc 0 M.b ∩ Ioi 0 = Ioc 0 M.b := by
      ext v; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1⟩
    rw [Set.inter_comm, hs]
    exact Ioc_ae_eq_Icc.symm
  rw [hu2] at hu; linarith

lemma Fbar_anti (hM : M.Standing) : Antitone M.Fbar := by
  have := mu_finite hM
  intro x y hxy
  unfold Model.Fbar
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioi_subset_Ioi hxy))

/-- `F̄^{-1}(q)` for `q ∈ (0,1)`. -/
lemma FbarInv_spec (hM : M.Standing) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    M.FbarInv q ∈ Ioo 0 M.b ∧ M.Fbar (M.FbarInv q) = q := by
  have hb := hM.b_pos.le
  obtain ⟨c, hc, hcq⟩ : ∃ c ∈ Icc 0 M.b, M.Fbar c = q := by
    have := intermediate_value_Icc' hb (Fbar_contOn hM)
    rw [Fbar_zero hM, Fbar_b hM] at this
    exact this ⟨hq0.le, hq1.le⟩
  have hleast : IsLeast {v ∈ Icc 0 M.b | M.Fbar v ≤ q} c := by
    refine ⟨⟨hc, hcq.le⟩, fun v hv => ?_⟩
    by_contra h
    push Not at h
    have := Fbar_strictAnti hM hv.1 hc h
    linarith [hv.2]
  have : M.FbarInv q = c := hleast.csInf_eq
  rw [this]
  refine ⟨⟨?_, ?_⟩, hcq⟩
  · rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h, Fbar_zero hM] at hcq; linarith
    · exact h
  · rcases eq_or_lt_of_le hc.2 with h | h
    · rw [h, Fbar_b hM] at hcq; linarith
    · exact h

lemma qL_lt_one_of (hM : M.Standing) (h : 0 < M.FbarInv M.qL) : M.qL < 1 := by
  by_contra hq
  push Not at hq
  have hmem : (0 : ℝ) ∈ {v ∈ Icc 0 M.b | M.Fbar v ≤ M.qL} :=
    ⟨left_mem_Icc.2 hM.b_pos.le, by rw [Fbar_zero hM]; exact hq⟩
  have : M.FbarInv M.qL ≤ 0 := csInf_le ⟨0, fun v hv => hv.1.1⟩ hmem
  linarith

end PersuadeEarly.Private.PEAux


open MeasureTheory Set

namespace PersuadeEarly.Private.PEAux

variable {M : Model}

lemma integrable_bdd (hM : M.Standing) {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ)
    (h : ∀ v, |g v| ≤ C) : Integrable g M.mu := by
  have := mu_finite hM
  exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun v => by
    simpa [Real.norm_eq_abs] using h v)

lemma pL_pos (hM : M.Standing) : 0 < M.pL := by
  unfold Model.pL; linarith [hM.pH_lt_one]

lemma vbar_eq (hM : M.Standing) {p2 : ℝ} (hp : p2 < psP1 M) (hp1 : 0 ≤ psP1 M) :
    vbar M p2 = min M.b (psP1 M + M.pH / M.pL * (psP1 M - p2)) := by
  set p1 := psP1 M
  set c := p1 + M.pH / M.pL * (p1 - p2)
  have hpL := pL_pos hM
  have hpH := hM.pH_pos
  have hd : 0 < p1 - p2 := by linarith
  have hc : p1 < c := by
    have : 0 < M.pH / M.pL * (p1 - p2) := by positivity
    linarith
  have key : ∀ v, sigmaH M p2 v < 1 ↔ v < c := by
    intro v
    unfold sigmaH
    rw [min_lt_iff]
    simp only [lt_irrefl, or_false]
    have e1 : M.pL / M.pH * ((v - p1) / (p1 - p2)) = (M.pL * (v - p1)) / (M.pH * (p1 - p2)) := by
      field_simp
    have e2 : c = p1 + (M.pH * (p1 - p2)) / M.pL := by simp only [c]; ring
    rw [e1, div_lt_one (by positivity), e2]
    constructor
    · intro h
      have : (v - p1) < M.pH * (p1 - p2) / M.pL := by
        rw [lt_div_iff₀ hpL]; linarith
      linarith
    · intro h
      have : (v - p1) < M.pH * (p1 - p2) / M.pL := by linarith
      rw [lt_div_iff₀ hpL] at this; linarith
  unfold vbar
  have hS : {v ∈ Icc 0 M.b | sigmaH M p2 v < 1} = Icc 0 M.b ∩ Iio c := by
    ext v; simp only [mem_setOf_eq, mem_inter_iff, mem_Iio, key]
  rw [hS]
  rcases le_or_gt c M.b with h | h
  · have : Icc 0 M.b ∩ Iio c = Ico 0 c := by
      ext v; simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
    rw [this, csSup_Ico (by linarith), min_eq_right h]
  · have : Icc 0 M.b ∩ Iio c = Icc 0 M.b := by
      ext v; simp only [mem_inter_iff, mem_Icc, mem_Iio]
      constructor
      · rintro ⟨h1, _⟩; exact h1
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by linarith⟩
    rw [this, csSup_Icc hM.b_pos.le, min_eq_left h.le]

set_option maxHeartbeats 1000000 in
theorem eq16 (M : Model) (hM : M.Standing) :
    ∀ p2 : ℝ, 0 ≤ p2 → p2 < M.FbarInv M.qL → PS14 M p2 →
      (psMech M p2).Valid ∧ (psMech M p2).Obedient ∧ (psMech M p2).revenue = Rprivate M p2 := by
  intro p2 h0 hlt _
  have hP : psP1 M = M.FbarInv M.qL := rfl
  set p1 := M.FbarInv M.qL with hp1def
  have hp1pos : 0 < p1 := lt_of_le_of_lt h0 hlt
  have hq1 : M.qL < 1 := qL_lt_one_of hM hp1pos
  obtain ⟨⟨_, hp1b⟩, hFp1⟩ := FbarInv_spec hM hM.qL_pos hq1
  have hpL := pL_pos hM
  have hpH := hM.pH_pos
  have hd : 0 < p1 - p2 := by linarith
  set σ := sigmaH M p2 with hσdef
  have hσc : Continuous σ := by
    simp only [hσdef]; unfold sigmaH; fun_prop
  have hσm : Measurable σ := hσc.measurable
  have hσle1 : ∀ v, σ v ≤ 1 := fun v => min_le_right _ _
  have hσle : ∀ v, σ v ≤ M.pL / M.pH * ((v - p1) / (p1 - p2)) := fun v => min_le_left _ _
  have hσnn : ∀ v, p1 ≤ v → 0 ≤ σ v := by
    intro v hv
    simp only [hσdef, sigmaH, hP]
    apply le_min _ zero_le_one
    have : 0 ≤ (v - p1) / (p1 - p2) := div_nonneg (by linarith) hd.le
    positivity
  set N := psMech M p2 with hN
  -- the four masses
  have hfσ : ContinuousOn (fun v => M.f v * σ v) (Icc 0 M.b) :=
    hM.f_cont.mul hσc.continuousOn
  have hD1L : N.D1L 0 = M.qL := by
    simp only [Mech.D1L, hN, psMech, hP, ← hσdef]
    rw [integral_mu_ite hM p1 hp1pos.le hp1b.le (fun _ => 1)]
    simp only [mul_one]
    rw [← Fbar_eq_integral hM p1 hp1pos.le hp1b.le, hFp1]
  have hD2L : N.D2L 0 = 0 := by simp [Mech.D2L, hN, psMech]
  set I := ∫ v in p1..M.b, M.f v * σ v with hI
  have hD1H : N.D1H 0 = I := by
    simp only [Mech.D1H, hN, psMech, hP, ← hσdef]
    rw [integral_mu_ite hM p1 hp1pos.le hp1b.le σ]
  have hint1 : Integrable (fun v => if p2 ≤ v then (1 : ℝ) else 0) M.mu :=
    integrable_bdd hM (Measurable.ite measurableSet_Ici measurable_const measurable_const) 1
      (fun v => by split_ifs <;> simp)
  have hint2 : Integrable (fun v => if p1 ≤ v then σ v else 0) M.mu :=
    integrable_bdd hM (Measurable.ite measurableSet_Ici hσm measurable_const) 1
      (fun v => by
        split_ifs with h
        · rw [abs_of_nonneg (hσnn v h)]; exact hσle1 v
        · simp)
  have hD2H : N.D2H 0 = M.Fbar p2 - I := by
    simp only [Mech.D2H, hN, psMech, hP, ← hσdef]
    have : (fun v => if p1 ≤ v then 1 - σ v else if p2 ≤ v then (1 : ℝ) else 0) =
        fun v => (if p2 ≤ v then (1 : ℝ) else 0) - (if p1 ≤ v then σ v else 0) := by
      ext v
      by_cases h1 : p1 ≤ v
      · have : p2 ≤ v := by linarith
        simp [h1, this]
      · simp [h1]
    rw [this, integral_sub hint1 hint2, integral_mu_ite hM p2 h0 (by linarith) (fun _ => 1),
      integral_mu_ite hM p1 hp1pos.le hp1b.le σ, ← hI]
    simp only [mul_one]
    rw [← Fbar_eq_integral hM p2 h0 (by linarith)]
  have hIle : I ≤ M.qL := by
    rw [hI, ← hFp1, Fbar_eq_integral hM p1 hp1pos.le hp1b.le]
    apply intervalIntegral.integral_mono_on hp1b.le
    · exact (hfσ.mono (Icc_subset_Icc hp1pos.le le_rfl)).intervalIntegrable_of_Icc hp1b.le
    · exact (hM.f_cont.mono (Icc_subset_Icc hp1pos.le le_rfl)).intervalIntegrable_of_Icc
        hp1b.le
    · intro v hv
      have hf := f_nonneg hM v ⟨hp1pos.le.trans hv.1, hv.2⟩
      nlinarith [hσle1 v]
  have hInn : 0 ≤ I := by
    apply intervalIntegral.integral_nonneg hp1b.le
    intro v hv
    exact mul_nonneg (f_nonneg hM v ⟨hp1pos.le.trans hv.1, hv.2⟩) (hσnn v hv.1)
  have hF2 : M.Fbar p2 ≤ 1 := Fbar_le_one hM p2
  -- availabilities
  have ha1L : N.a1L 0 = 1 := by
    simp only [Mech.a1L, alpha1, avail, hD1L]
    simp [not_le.2 hM.qL_pos]
  have ha2L : N.a2L 0 = 0 := by
    simp only [Mech.a2L, alpha2, avail, hD1L, hD2L]
    simp
  have ha1H : N.a1H 0 = 1 := by
    simp only [Mech.a1H, alpha1, avail, hD1H]
    rw [if_neg (by norm_num), if_pos (by linarith)]
  have ha2H : N.a2H 0 = 1 := by
    simp only [Mech.a2H, alpha2, avail, hD1H, hD2H]
    rw [max_eq_left (by linarith), if_neg (by linarith), if_pos (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · -- validity
    refine ⟨?_, h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hp1pos.le
    all_goals intros
    all_goals simp only [hN, psMech, hP, ← hσdef]
    · norm_num
    · norm_num
    · simp
    · simp
    · exact Measurable.ite measurableSet_Ici hσm measurable_const
    · exact Measurable.ite measurableSet_Ici measurable_const measurable_const
    · exact Measurable.ite measurableSet_Ici (measurable_const.sub hσm)
        (Measurable.ite measurableSet_Ici measurable_const measurable_const)
    · exact measurable_const
    · split_ifs with h
      · exact hσnn _ h
      · exact le_rfl
    · split_ifs <;> norm_num
    · split_ifs with h h'
      · linarith [hσle1 ‹ℝ›]
      · norm_num
      · norm_num
    · exact le_rfl
    · split_ifs <;> linarith
    · split_ifs <;> norm_num
  · -- obedience
    unfold Mech.Obedient Mech.ObedientOn
    refine Filter.Eventually.of_forall fun v => ?_
    simp only [Mech.wsum, Fin.sum_univ_one, Finset.univ_unique, Finset.sum_singleton,
      Fin.default_eq_zero, ha1L, ha2L, ha1H, ha2H, Mech.noH, Mech.noL]
    simp only [hN, psMech, hP, ← hσdef, mul_one, mul_zero, sub_zero, zero_mul, add_zero]
    by_cases h1 : p1 ≤ v
    · simp only [h1, if_true]
      have hs := hσle v
      have hsn := hσnn v h1
      have hs1 := hσle1 v
      have key : M.pH * σ v * (p1 - p2) ≤ M.pL * (v - p1) := by
        have : M.pH * (M.pL / M.pH * ((v - p1) / (p1 - p2))) * (p1 - p2) = M.pL * (v - p1) := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_left hs hpH.le]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · nlinarith
      · have : 0 ≤ v - p1 := by linarith
        positivity
      · have : 0 ≤ 1 - σ v := by linarith
        have e : v - p2 - (v - p1) = p1 - p2 := by ring
        rw [e]; exact mul_nonneg (mul_nonneg hpH.le this) hd.le
      · have : 0 ≤ 1 - σ v := by linarith
        have : 0 ≤ v - p2 := by linarith
        positivity
      · simp
      · simp
    · simp only [h1, if_false]
      push Not at h1
      by_cases h2 : p2 ≤ v
      · simp only [h2, if_true]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
      · simp only [h2, if_false]
        push Not at h2
        have a2 : 0 ≤ M.pH * (p2 - v) := mul_nonneg hpH.le (by linarith)
        have a3 : 0 ≤ M.pL * (p1 - v) := mul_nonneg hpL.le (by linarith)
        have a4 : 0 ≤ M.pH * (p1 - v) := mul_nonneg hpH.le (by linarith)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf <;> ring_nf at a2 a3 a4 <;> linarith
  · -- revenue
    have hrev : N.revenue = M.pH * (p1 * I + p2 * (M.Fbar p2 - I)) + M.pL * (p1 * M.qL) := by
      simp only [Mech.revenue, Fin.sum_univ_one, hD1H, hD2H, hD1L, hD2L, sales]
      simp only [hN, psMech, hP, one_mul]
      rw [min_eq_left (by linarith), max_eq_left (by linarith), min_eq_left (by linarith),
        min_self, sub_self, max_self, min_self]
      ring
    rw [hrev]
    unfold Rprivate
    rw [vbar_eq hM (by rw [hP]; exact hlt) (by rw [hP]; exact hp1pos.le), hP]
    set c := p1 + M.pH / M.pL * (p1 - p2) with hc
    have hcp : p1 < c := by
      have : 0 < M.pH / M.pL * (p1 - p2) := by positivity
      linarith
    set vb := min M.b c with hvb
    have hp1vb : p1 ≤ vb := le_min hp1b.le hcp.le
    have hvbb : vb ≤ M.b := min_le_left _ _
    have hvb0 : 0 ≤ vb := hp1pos.le.trans hp1vb
    have hii : ∀ x y, x ∈ Icc p1 M.b → y ∈ Icc p1 M.b →
        IntervalIntegrable (fun v => M.f v * σ v) volume x y := by
      intro x y hx hy
      exact (hfσ.mono ((uIcc_subset_Icc hx hy).trans
        (Icc_subset_Icc hp1pos.le le_rfl))).intervalIntegrable
    have hsplit : I = (∫ v in p1..vb, M.f v * σ v) + ∫ v in vb..M.b, M.f v * σ v := by
      rw [hI, intervalIntegral.integral_add_adjacent_intervals]
      · exact hii _ _ ⟨le_rfl, hp1b.le⟩ ⟨hp1vb, hvbb⟩
      · exact hii _ _ ⟨hp1vb, hvbb⟩ ⟨hp1b.le, le_rfl⟩
    have hpart1 : (∫ v in p1..vb, M.f v * σ v) =
        (M.pL / M.pH / (p1 - p2)) * ∫ v in p1..vb, (v - p1) * M.f v := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hp1vb] at hv
      have hle : M.pL / M.pH * ((v - p1) / (p1 - p2)) ≤ 1 := by
        have h1 : v - p1 ≤ M.pH / M.pL * (p1 - p2) := by
          have := hv.2.trans (min_le_right _ _); linarith
        have h2 : (v - p1) / (p1 - p2) ≤ (M.pH / M.pL * (p1 - p2)) / (p1 - p2) :=
          div_le_div_of_nonneg_right h1 hd.le
        have h3 : M.pL / M.pH * ((M.pH / M.pL * (p1 - p2)) / (p1 - p2)) = 1 := by
          field_simp
        calc M.pL / M.pH * ((v - p1) / (p1 - p2))
            ≤ M.pL / M.pH * ((M.pH / M.pL * (p1 - p2)) / (p1 - p2)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 1 := h3
      simp only [hσdef, sigmaH, hP]
      rw [min_eq_left hle]
      field_simp
    have hpart2 : (∫ v in vb..M.b, M.f v * σ v) = M.Fbar vb := by
      rcases lt_or_ge c M.b with h | h
      · have hvbc : vb = c := min_eq_right h.le
        rw [Fbar_eq_integral hM vb hvb0 hvbb]
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hvbb] at hv
        have hge : 1 ≤ M.pL / M.pH * ((v - p1) / (p1 - p2)) := by
          have h1 : M.pH / M.pL * (p1 - p2) ≤ v - p1 := by
            have := hv.1; rw [hvbc] at this; linarith
          have h2 : (M.pH / M.pL * (p1 - p2)) / (p1 - p2) ≤ (v - p1) / (p1 - p2) :=
            div_le_div_of_nonneg_right h1 hd.le
          have h3 : M.pL / M.pH * ((M.pH / M.pL * (p1 - p2)) / (p1 - p2)) = 1 := by
            field_simp
          calc (1 : ℝ) = M.pL / M.pH * ((M.pH / M.pL * (p1 - p2)) / (p1 - p2)) := h3.symm
            _ ≤ M.pL / M.pH * ((v - p1) / (p1 - p2)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
        simp only [hσdef, sigmaH, hP]
        rw [min_eq_right hge, mul_one]
      · have hvbc : vb = M.b := min_eq_left h
        rw [hvbc, intervalIntegral.integral_same, Fbar_b hM]
    rw [hsplit, hpart1, hpart2]
    field_simp
    ring

end PersuadeEarly.Private.PEAux


open PersuadeEarly.Private in
theorem solution (M : Model) (hM : M.Standing) :
    ∀ p2 : ℝ, 0 ≤ p2 → p2 < M.FbarInv M.qL → PS14 M p2 →
      (psMech M p2).Valid ∧ (psMech M p2).Obedient ∧ (psMech M p2).revenue = Rprivate M p2 :=
  PersuadeEarly.Private.PEAux.eq16 M hM
