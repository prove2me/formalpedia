-- Prove2me | solution 1 for RiskFunctionals.Kusuoka.mad_kusuoka
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:52:47.609737+00:00
-- url     : https://prove2.me/submissions/22e01886-302d-409d-bdec-d7fa92c7c344

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory

noncomputable def g79q_F (μ : Measure ℝ) (u : ℝ) : ℝ := μ.real (Set.Iic u)

noncomputable def g79q_q (μ : Measure ℝ) (p : ℝ) : ℝ := sInf {u : ℝ | p ≤ g79q_F μ u}

theorem g79q_cdf_eq_real (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    ProbabilityTheory.cdf μ v = g79q_F μ v := ProbabilityTheory.cdf_eq_real μ v

theorem g79q_qle (μ : Measure ℝ) [IsProbabilityMeasure μ] (p u : ℝ)
    (hp : 0 < p) (hfin : ∃ v : ℝ, p ≤ g79q_F μ v) :
    g79q_q μ p ≤ u ↔ p ≤ g79q_F μ u := by
  have hF : ∀ v, g79q_F μ v = ProbabilityTheory.cdf μ v := fun v =>
    (g79q_cdf_eq_real μ v).symm
  set S := {u : ℝ | p ≤ g79q_F μ u} with hS
  have hne : S.Nonempty := hfin
  have hbdd : BddBelow S := by
    have h := (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (gt_mem_nhds hp)
    obtain ⟨L, hL⟩ := Filter.eventually_atBot.1 h
    refine ⟨L, fun v hv => ?_⟩
    by_contra hlt
    have := hL v (le_of_lt (lt_of_not_ge hlt))
    have hv' : p ≤ g79q_F μ v := hv
    rw [hF] at hv'
    linarith
  have hmono : Monotone (g79q_F μ) := fun a b hab => by
    rw [hF, hF]; exact (ProbabilityTheory.cdf μ).mono hab
  constructor
  · intro hq
    have hQ : p ≤ g79q_F μ (g79q_q μ p) := by
      have hev : ∀ᶠ v in nhdsWithin (g79q_q μ p) (Set.Ioi (g79q_q μ p)),
          p ≤ ProbabilityTheory.cdf μ v := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        obtain ⟨w, hwS, hwv⟩ := exists_lt_of_csInf_lt hne hv
        have : p ≤ g79q_F μ w := hwS
        rw [← hF]; exact this.trans (hmono hwv.le)
      have ht : Filter.Tendsto (ProbabilityTheory.cdf μ)
          (nhdsWithin (g79q_q μ p) (Set.Ioi (g79q_q μ p)))
          (nhds (ProbabilityTheory.cdf μ (g79q_q μ p))) :=
        ((ProbabilityTheory.cdf μ).right_continuous _).tendsto.mono_left
          (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [hF]
      exact ge_of_tendsto ht hev
    exact hQ.trans (hmono hq)
  · intro hu
    exact csInf_le hbdd hu

theorem g79q_q_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : p ≤ 0) :
    g79q_q μ p = 0 := by
  unfold g79q_q
  have : {u : ℝ | p ≤ g79q_F μ u} = Set.univ := by
    ext u
    simp only [Set.mem_univ, iff_true]
    refine le_trans hp ?_
    unfold g79q_F; exact measureReal_nonneg
  rw [this]
  exact Real.sInf_of_not_bddBelow not_bddBelow_univ

theorem g79q_q_nowit (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ)
    (h : ¬ ∃ v, p ≤ g79q_F μ v) : g79q_q μ p = 0 := by
  unfold g79q_q
  have : {u : ℝ | p ≤ g79q_F μ u} = ∅ := by
    ext u; simp only [Set.mem_empty_iff_false, iff_false]; exact fun hu => h ⟨u, hu⟩
  rw [this, Real.sInf_empty]

theorem g79q_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] : Monotone (g79q_F μ) := by
  intro a b hab
  unfold g79q_F
  exact measureReal_mono (Set.Iic_subset_Iic.2 hab)

theorem g79q_meas (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (g79q_q μ) := by
  set A : Set ℝ := Set.Ioi 0 ∩ ⋃ n : ℕ, Set.Iic (g79q_F μ n) with hA
  have hAm : MeasurableSet A :=
    measurableSet_Ioi.inter (MeasurableSet.iUnion (fun _ => measurableSet_Iic))
  have hAiff : ∀ p, p ∈ A ↔ 0 < p ∧ ∃ v, p ≤ g79q_F μ v := by
    intro p
    simp only [hA, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · rintro ⟨h0, n, hn⟩; exact ⟨h0, n, hn⟩
    · rintro ⟨h0, v, hv⟩
      obtain ⟨n, hn⟩ := exists_nat_ge v
      exact ⟨h0, n, hv.trans (g79q_mono μ hn)⟩
  refine measurable_of_Iic (fun x => ?_)
  have : g79q_q μ ⁻¹' Set.Iic x =
      (A ∩ Set.Iic (g79q_F μ x)) ∪ (Aᶜ ∩ {_p | 0 ≤ x}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    by_cases hp : p ∈ A
    · have := (hAiff p).1 hp
      rw [g79q_qle μ p x this.1 this.2]
      simp [hp]
    · have h0 : g79q_q μ p = 0 := by
        by_cases hp0 : p ≤ 0
        · exact g79q_q_nonpos μ p hp0
        · exact g79q_q_nowit μ p (fun hw => hp ((hAiff p).2 ⟨lt_of_not_ge hp0, hw⟩))
      simp [hp, h0]
  rw [this]
  exact (hAm.inter measurableSet_Iic).union (hAm.compl.inter (MeasurableSet.const _))

theorem g79q_transform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U) (hunif : P.map U = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    P.map (fun ω => g79q_q μ (U ω)) = μ := by
  have hf := g79q_meas μ
  have hcomp : P.map (fun ω => g79q_q μ (U ω)) =
      (P.map U).map (g79q_q μ) := by
    rw [Measure.map_map hf hU]; rfl
  rw [hcomp, hunif]
  have hrestr : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  rw [hrestr]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    constructor; rw [Measure.restrict_apply_univ]; simp
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply hf measurableSet_Iic,
    Measure.restrict_apply (hf measurableSet_Iic)]
  set g := g79q_F μ x with hg
  have hset : g79q_q μ ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = Set.Iic g ∩ Set.Ioo 0 1 := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h0, h1'⟩
      refine ⟨?_, h0, h1'⟩
      have hw : ∃ v, p ≤ g79q_F μ v := by
        have hlim : Filter.Tendsto (g79q_F μ) Filter.atTop (nhds 1) := by
          have := ProbabilityTheory.tendsto_cdf_atTop μ
          refine this.congr (fun v => ?_)
          exact g79q_cdf_eq_real μ v
        obtain ⟨v, hv⟩ := (hlim.eventually (lt_mem_nhds h1')).exists
        exact ⟨v, hv.le⟩
      exact (g79q_qle μ p x h0 hw).1 h1
    · rintro ⟨h1, h0, h1'⟩
      exact ⟨(g79q_qle μ p x h0 ⟨x, h1⟩).2 h1, h0, h1'⟩
  rw [hset]
  have hg0 : 0 ≤ g := measureReal_nonneg
  have hg1 : g ≤ 1 := by
    rw [hg]; unfold g79q_F; exact measureReal_le_one
  have hμx : μ (Set.Iic x) = ENNReal.ofReal g := by
    rw [hg]; unfold g79q_F
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hμx]
  apply le_antisymm
  · calc volume (Set.Iic g ∩ Set.Ioo 0 1) ≤ volume (Set.Ioc 0 g) := by
          apply measure_mono
          rintro p ⟨h1, h0, -⟩; exact ⟨h0, h1⟩
      _ = ENNReal.ofReal g := by simp
  · calc ENNReal.ofReal g = volume (Set.Ioo 0 g) := by simp
      _ ≤ volume (Set.Iic g ∩ Set.Ioo 0 1) := by
          apply measure_mono
          rintro p ⟨h0, h1⟩; exact ⟨h1.le, h0, lt_of_lt_of_le h1 hg1⟩

theorem g79q_wit (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : p < 1) :
    ∃ v, p ≤ g79q_F μ v := by
  have hlim : Filter.Tendsto (g79q_F μ) Filter.atTop (nhds 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).congr (fun v => g79q_cdf_eq_real μ v)
  obtain ⟨v, hv⟩ := (hlim.eventually (lt_mem_nhds hp)).exists
  exact ⟨v, hv.le⟩

theorem g79q_qle' (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (u : ℝ) :
    g79q_q μ p ≤ u ↔ p ≤ g79q_F μ u := g79q_qle μ p u hp0 (g79q_wit μ hp1)

/-- two functions with the same "quantile-type" sublevel description agree off a countable set -/
theorem g79q_ae_eq (f g G : ℝ → ℝ)
    (hf : ∀ u ∈ Set.Ioo (0:ℝ) 1, ∀ x, (u < G x → f u ≤ x) ∧ (f u ≤ x → u ≤ G x))
    (hg : ∀ u ∈ Set.Ioo (0:ℝ) 1, ∀ x, (u < G x → g u ≤ x) ∧ (g u ≤ x → u ≤ G x)) :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioo (0:ℝ) 1 → f u = g u := by
  have hc : (Set.range (fun q : ℚ => G q)).Countable := Set.countable_range _
  filter_upwards [hc.ae_notMem volume] with u hu hu01
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have h1 := (hf u hu01 q).2 hq1.le
    have h2 : ¬ (u < G q) := fun h => absurd ((hg u hu01 q).1 h) (not_le.mpr hq2)
    exact hu ⟨q, le_antisymm (not_lt.mp h2) h1⟩
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
    have h1 := (hg u hu01 q).2 hq1.le
    have h2 : ¬ (u < G q) := fun h => absurd ((hf u hu01 q).1 h) (not_le.mpr hq2)
    exact hu ⟨q, le_antisymm (not_lt.mp h2) h1⟩

theorem g79q_Iio_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (a t : ℝ)
    (h : ∀ y < a, g79q_F μ y ≤ t) : μ.real (Set.Iio a) ≤ t := by
  have hU : Set.Iio a = ⋃ n : ℕ, Set.Iic (a - 1 / ((n : ℝ) + 1)) := by
    ext v; simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hv
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hv)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone (fun n : ℕ => Set.Iic (a - 1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    apply Set.Iic_subset_Iic.mpr
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have ht : 0 ≤ t := le_trans measureReal_nonneg (h (a - 1) (by linarith))
  have hE : μ (Set.Iio a) ≤ ENNReal.ofReal t := by
    rw [hU, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have := h (a - 1 / ((n : ℝ) + 1)) (by linarith)
    unfold g79q_F at this
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal this
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal ht hE

/-- reflection: quantile of the negated law agrees a.e. with `u ↦ -q(1-u)` -/
theorem g79q_refl (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioo (0:ℝ) 1 →
      g79q_q (μ.map (fun x => -x)) u = - g79q_q μ (1 - u) := by
  set ν := μ.map (fun x => -x) with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hFν : ∀ x, g79q_F ν x = 1 - μ.real (Set.Iio (-x)) := by
    intro x
    unfold g79q_F
    rw [hν, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic]
    have : (fun x : ℝ => -x) ⁻¹' Set.Iic x = (Set.Iio (-x))ᶜ := by
      ext v; simp
    rw [this, ← measureReal_def, probReal_compl_eq_one_sub measurableSet_Iio]
  apply g79q_ae_eq _ _ (g79q_F ν)
  · intro u hu x
    exact ⟨fun h => ((g79q_qle' ν hu.1 hu.2 x).2 h.le), fun h => (g79q_qle' ν hu.1 hu.2 x).1 h⟩
  · intro u hu x
    have h0 : 0 < 1 - u := by linarith [hu.2]
    have h1 : 1 - u < 1 := by linarith [hu.1]
    constructor
    · intro h
      rw [hFν] at h
      by_contra hc
      push Not at hc
      have hq : g79q_q μ (1 - u) < -x := by linarith
      have h2 := (g79q_qle' μ h0 h1 _).1 le_rfl
      have h3 : g79q_F μ (g79q_q μ (1 - u)) ≤ μ.real (Set.Iio (-x)) :=
        measureReal_mono (Set.Iic_subset_Iio.mpr hq)
      linarith
    · intro h
      rw [hFν]
      have : μ.real (Set.Iio (-x)) ≤ 1 - u := by
        apply g79q_Iio_le
        intro y hy
        have hlt : y < g79q_q μ (1 - u) := by linarith
        have := mt (g79q_qle' μ h0 h1 y).2 (not_le.mpr hlt)
        exact (not_le.mp this).le
      linarith

theorem g79c_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hv : v < 1) : g79q_q μ u ≤ g79q_q μ v := by
  rw [g79q_qle' μ hu (lt_of_le_of_lt huv hv)]
  exact huv.trans ((g79q_qle' μ (lt_of_lt_of_le hu huv) hv _).1 le_rfl)

/-- integrals against the law as integrals of the quantile function -/
theorem g79n_E (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable g μ) :
    IntegrableOn (fun u => g (g79q_q μ u)) (Set.Icc 0 1) ∧
    ∫ y, g y ∂μ = ∫ u in (0:ℝ)..1, g (g79q_q μ u) := by
  have hP : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have htr' : (volume.restrict (Set.Icc (0 : ℝ) 1)).map (g79q_q μ) = μ :=
    g79q_transform μ (volume.restrict (Set.Icc (0 : ℝ) 1)) id measurable_id Measure.map_id
  have hmeas := g79q_meas μ
  constructor
  · have h := hgi
    rw [← htr'] at h
    exact (integrable_map_measure hg.aestronglyMeasurable hmeas.aemeasurable).1 h
  · conv_lhs => rw [← htr']
    rw [integral_map hmeas.aemeasurable hg.aestronglyMeasurable,
      intervalIntegral.integral_of_le zero_le_one]
    exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm

/-- Rockafellar–Uryasev in quantile form, 0 < α < 1 -/
theorem g79n_RU (μ : Measure ℝ) [IsProbabilityMeasure μ] (hI : Integrable (fun y : ℝ => y) μ)
    {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (∀ x : ℝ, α * x - ∫ y, max (x - y) 0 ∂μ ≤ ∫ u in (0:ℝ)..α, g79q_q μ u) ∧
    α * g79q_q μ α - ∫ y, max (g79q_q μ α - y) 0 ∂μ = ∫ u in (0:ℝ)..α, g79q_q μ u := by
  set q := g79q_q μ with hqdef
  have hqI : IntegrableOn q (Set.Icc 0 1) := by
    simpa using (g79n_E μ (fun y => y) measurable_id hI).1
  have hpI : ∀ x : ℝ, IntegrableOn (fun u => max (x - q u) 0) (Set.Icc 0 1) ∧
      ∫ y, max (x - y) 0 ∂μ = ∫ u in (0:ℝ)..1, max (x - q u) 0 := by
    intro x
    exact g79n_E μ (fun y => max (x - y) 0) (by fun_prop) ((integrable_const x).sub hI).pos_part
  have hII : ∀ (f : ℝ → ℝ), IntegrableOn f (Set.Icc 0 1) → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable f volume a b := by
    intro f hf a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hf.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc ha hb))
  have hsplit : ∀ x : ℝ, ∫ u in (0:ℝ)..1, max (x - q u) 0 =
      (∫ u in (0:ℝ)..α, max (x - q u) 0) + ∫ u in α..1, max (x - q u) 0 := fun x =>
    (intervalIntegral.integral_add_adjacent_intervals (hII _ (hpI x).1 0 α le_rfl h0.le h1.le)
      (hII _ (hpI x).1 α 1 h0.le h1.le le_rfl)).symm
  constructor
  · intro x
    rw [(hpI x).2, hsplit x]
    have hnn : 0 ≤ ∫ u in α..(1:ℝ), max (x - q u) 0 :=
      intervalIntegral.integral_nonneg h1.le (fun u _ => le_max_right _ _)
    -- ∫_0^α (q - x + (x - q)^+) ≥ 0
    have hA : ∫ u in (0:ℝ)..α, (q u - x + max (x - q u) 0) =
        (∫ u in (0:ℝ)..α, q u) - α * x + ∫ u in (0:ℝ)..α, max (x - q u) 0 := by
      rw [intervalIntegral.integral_add ((hII q hqI 0 α le_rfl h0.le h1.le).sub
          intervalIntegrable_const) (hII _ (hpI x).1 0 α le_rfl h0.le h1.le),
        intervalIntegral.integral_sub (hII q hqI 0 α le_rfl h0.le h1.le) intervalIntegrable_const]
      simp
      try ring
    have hB : 0 ≤ ∫ u in (0:ℝ)..α, (q u - x + max (x - q u) 0) :=
      intervalIntegral.integral_nonneg h0.le (fun u _ => by
        rcases le_total (x - q u) 0 with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith)
    linarith
  · rw [(hpI (q α)).2, hsplit (q α)]
    have hz : ∫ u in α..(1:ℝ), max (q α - q u) 0 = 0 := by
      rw [intervalIntegral.integral_of_le h1.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      exact max_eq_right (by linarith [g79c_mono μ h0 hu.1.le hu.2])
    have he : ∫ u in (0:ℝ)..α, max (q α - q u) 0 = ∫ u in (0:ℝ)..α, (q α - q u) := by
      rw [intervalIntegral.integral_of_le h0.le, intervalIntegral.integral_of_le h0.le]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      exact max_eq_left (by linarith [g79c_mono μ hu.1 hu.2 h1])
    rw [hz, he, intervalIntegral.integral_sub intervalIntegrable_const
      (hII q hqI 0 α le_rfl h0.le h1.le)]
    simp

open RiskFunctionals.Kusuoka
open MeasureTheory ProbabilityTheory

theorem g79t_slint_dirac (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ENNReal) (a : ℝ) :
    ∫⁻ x in s, f x ∂(Measure.dirac a) = s.indicator f a := by
  rw [← lintegral_indicator hs, lintegral_dirac]

theorem g79t_sint_dirac (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) (a : ℝ) :
    ∫ x in s, f x ∂(Measure.dirac a) = s.indicator f a := by
  rw [← integral_indicator hs, integral_dirac]

theorem g79t_int_sdirac (s : Set ℝ) (f : ℝ → ℝ) (a : ℝ) (c : ENNReal) (hc : c ≠ ⊤) :
    Integrable f ((c • Measure.dirac a).restrict s) := by
  rw [Measure.restrict_smul]
  refine Integrable.smul_measure ?_ hc
  exact (integrable_dirac (f := f) (a := a) (by simp)).mono_measure Measure.restrict_le_self

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsNonAtomic P) (Y : Ω → ℝ) (hY : MemLp Y 1 P) :
    IsGLB {x : ℝ | ∃ m : Measure ℝ, IsProbabilityMeasure m ∧ m (Set.Ioc 0 1)ᶜ = 0 ∧
        (∫⁻ v in Set.Ioo 0 1, ENNReal.ofReal (1 / v) ∂m) ≤ 1 ∧
        x = ∫ α in Set.Ioc 0 1, averageValueAtRisk P Y α ∂m}
      ((∫ ω, Y ω ∂P) - (1 / 2) * meanAbsoluteDeviation P Y) := by
  have hYm : AEMeasurable Y P := hY.1.aemeasurable
  set μ := P.map Y with hμ
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hYm
  have hI : Integrable (fun x : ℝ => x) μ :=
    (integrable_map_measure aestronglyMeasurable_id hYm).2 (hY.integrable le_rfl)
  set M := ∫ x, x ∂μ with hMdef
  have hM : ∫ ω, Y ω ∂P = M := (integral_map hYm aestronglyMeasurable_id).symm
  set c := ∫ x, max (M - x) 0 ∂μ with hcdef
  have hc0 : 0 ≤ c := integral_nonneg fun x => le_max_right _ _
  have hpi : Integrable (fun x => max (M - x) 0) μ := ((integrable_const M).sub hI).pos_part
  have hMAD : meanAbsoluteDeviation P Y = 2 * c := by
    unfold meanAbsoluteDeviation
    rw [hM]
    have h1 : ∫ ω, |Y ω - M| ∂P = ∫ x, |x - M| ∂μ :=
      (integral_map hYm (by fun_prop : Continuous fun x : ℝ => |x - M|).aestronglyMeasurable).symm
    rw [h1]
    have h2 : (fun x : ℝ => |x - M|) = fun x => (x - M) + 2 * max (M - x) 0 := by
      funext x
      rcases le_total x M with h | h
      · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
      · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
    rw [h2, integral_add (f := fun x : ℝ => x - M) (g := fun x => 2 * max (M - x) 0)
      (hI.sub (integrable_const M)) (hpi.const_mul 2),
      integral_sub (f := fun x : ℝ => x) (g := fun _ => M) hI (integrable_const M), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, zero_add]
    rw [← hMdef, ← hcdef]; ring
  have htarget : (∫ ω, Y ω ∂P) - (1 / 2) * meanAbsoluteDeviation P Y = M - c := by
    rw [hM, hMAD]; ring
  rw [htarget]
  set q := g79q_q μ with hqdef
  have hAV : ∀ α, averageValueAtRisk P Y α = 1 / α * ∫ u in Set.Ioc 0 α, q u := fun α => rfl
  have hE := g79n_E μ (fun y => y) measurable_id hI
  have hqI : IntegrableOn q (Set.Icc 0 1) := hE.1
  have hqI' : IntegrableOn q (Set.Ioc 0 1) := hqI.mono_set Set.Ioc_subset_Icc_self
  have hAV1 : averageValueAtRisk P Y 1 = M := by
    rw [hAV, hMdef, hE.2, intervalIntegral.integral_of_le zero_le_one]; simp; rfl
  have hRU : ∀ α ∈ Set.Ioo (0:ℝ) 1, M - c / α ≤ averageValueAtRisk P Y α := by
    intro α hα
    have h := (g79n_RU μ hI hα.1 hα.2).1 M
    rw [hAV, ← intervalIntegral.integral_of_le hα.1.le]
    have hα0 : 0 < α := hα.1
    have : M - c / α = 1 / α * (α * M - c) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  set K := ∫ u in Set.Ioc 0 1, |q u| with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioc fun u _ => abs_nonneg _
  have hbound : ∀ α ∈ Set.Ioc (0:ℝ) 1, |averageValueAtRisk P Y α| ≤ K * (1 / α) := by
    intro α hα
    rw [hAV, abs_mul, abs_of_pos (by have := hα.1; positivity), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by have := hα.1; positivity)
    refine (abs_integral_le_integral_abs).trans ?_
    refine setIntegral_mono_set hqI'.abs (Filter.Eventually.of_forall fun u => abs_nonneg _) ?_
    exact (Set.Ioc_subset_Ioc_right hα.2).eventuallyLE
  have hcont : ContinuousOn (fun α => averageValueAtRisk P Y α) (Set.Ioc 0 1) := by
    have hprim : ContinuousOn (fun x => ∫ t in (0:ℝ)..x, q t) (Set.uIcc 0 1) :=
      intervalIntegral.continuousOn_primitive_interval (by rwa [Set.uIcc_of_le zero_le_one])
    have h2 : ContinuousOn (fun α : ℝ => 1 / α * ∫ t in (0:ℝ)..α, q t) (Set.Ioc 0 1) :=
      (continuousOn_const.div continuousOn_id (fun x hx => hx.1.ne')).mul
        (hprim.mono (by rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self))
    refine h2.congr fun α hα => ?_
    simp only [hAV, intervalIntegral.integral_of_le hα.1.le]
  -- key identity
  set p := μ.real (Set.Iic M) with hpdef
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by rw [hpdef]; exact measureReal_le_one
  have hkey : ∫ u in Set.Ioc 0 p, q u = p * M - c := by
    set gM : ℝ → ℝ := (Set.Iic M).indicator (fun y => y) with hgM
    have hgMi : Integrable gM μ := hI.indicator measurableSet_Iic
    have hEg := g79n_E μ gM (measurable_id.indicator measurableSet_Iic) hgMi
    have hc' : c = p * M - ∫ y, gM y ∂μ := by
      have : (fun x => max (M - x) 0) = (Set.Iic M).indicator (fun y => M - y) := by
        funext x
        by_cases h : x ≤ M
        · rw [Set.indicator_of_mem (by exact h), max_eq_left (by linarith)]
        · rw [Set.indicator_of_notMem (by exact h), max_eq_right (by push_neg at h; linarith)]
      rw [hcdef, this, integral_indicator measurableSet_Iic, hgM, integral_indicator measurableSet_Iic,
        integral_sub (integrable_const M).integrableOn hI.integrableOn, setIntegral_const]
      simp [hpdef]
    rw [hc', hEg.2, intervalIntegral.integral_of_le zero_le_one]
    have hs : ∫ u in Set.Ioc 0 p, q u = ∫ u in Set.Ioc 0 1, (Set.Ioc 0 p).indicator q u := by
      rw [setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.2 (Set.Ioc_subset_Ioc_right hp1)]
    rw [hs]
    have hne1 : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by
      rw [ae_iff]; simp
    have : ∫ u in Set.Ioc 0 1, (Set.Ioc 0 p).indicator q u = ∫ u in Set.Ioc 0 1, gM (q u) := by
      refine setIntegral_congr_ae measurableSet_Ioc ?_
      filter_upwards [hne1] with u hu1 hu
      have hu' : u < 1 := lt_of_le_of_ne hu.2 hu1
      have hiff := g79q_qle' μ hu.1 hu' M
      by_cases h : u ≤ p
      · rw [Set.indicator_of_mem (show u ∈ Set.Ioc 0 p from ⟨hu.1, h⟩), hgM,
          Set.indicator_of_mem (show q u ∈ Set.Iic M from hiff.2 h)]
      · rw [Set.indicator_of_notMem (fun h' => h h'.2), hgM,
          Set.indicator_of_notMem (show q u ∉ Set.Iic M from fun h' => h (hiff.1 h'))]
    rw [this]; ring
  refine IsLeast.isGLB ⟨?_, ?_⟩
  · -- attainment
    rcases eq_or_lt_of_le hp0 with hp | hp
    · -- p = 0
      have hc00 : c = 0 := by
        have := hkey; rw [← hp] at this; simp at this; linarith
      refine ⟨Measure.dirac 1, inferInstance, ?_, ?_, ?_⟩
      · rw [Measure.dirac_apply' _ measurableSet_Ioc.compl]; simp
      · rw [g79t_slint_dirac _ measurableSet_Ioo]; simp
      · rw [g79t_sint_dirac _ measurableSet_Ioc, Set.indicator_of_mem (by simp), hAV1, hc00]; ring
    · refine ⟨ENNReal.ofReal (1 - p) • Measure.dirac 1 + ENNReal.ofReal p • Measure.dirac p,
        ⟨?_⟩, ?_, ?_, ?_⟩
      · simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
          smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_add (by linarith) hp0]; simp
      · simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Measure.dirac_apply' _ measurableSet_Ioc.compl,
          Measure.dirac_apply' _ measurableSet_Ioc.compl]
        simp [hp, hp1]
      · rw [Measure.restrict_add, lintegral_add_measure, Measure.restrict_smul, Measure.restrict_smul,
          lintegral_smul_measure, lintegral_smul_measure, g79t_slint_dirac _ measurableSet_Ioo,
          g79t_slint_dirac _ measurableSet_Ioo, Set.indicator_of_notMem (by simp)]
        simp only [smul_eq_mul, mul_zero, zero_add]
        by_cases hp1' : p < 1
        · rw [Set.indicator_of_mem (show p ∈ Set.Ioo (0:ℝ) 1 from ⟨hp, hp1'⟩), ← ENNReal.ofReal_mul hp0,
            mul_one_div_cancel hp.ne']
          simp
        · rw [Set.indicator_of_notMem (fun h => hp1' h.2)]; simp
      · rw [Measure.restrict_add, integral_add_measure (g79t_int_sdirac _ _ _ _ ENNReal.ofReal_ne_top)
          (g79t_int_sdirac _ _ _ _ ENNReal.ofReal_ne_top), Measure.restrict_smul, Measure.restrict_smul,
          integral_smul_measure, integral_smul_measure, g79t_sint_dirac _ measurableSet_Ioc,
          g79t_sint_dirac _ measurableSet_Ioc, Set.indicator_of_mem (show (1:ℝ) ∈ Set.Ioc 0 1 by simp),
          Set.indicator_of_mem (show p ∈ Set.Ioc (0:ℝ) 1 from ⟨hp, hp1⟩), hAV1,
          ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith), hAV p, hkey]
        simp only [smul_eq_mul]
        field_simp
        ring
  · rintro x ⟨m, hm1, hm2, hm3, rfl⟩
    haveI := hm1
    have hae : ∀ᵐ x ∂m, x ∈ Set.Ioc (0:ℝ) 1 := by rw [ae_iff]; exact hm2
    have hν : m.restrict (Set.Ioc 0 1) = m := Measure.restrict_eq_self_of_ae_mem hae
    rw [hν]
    set H : ℝ → ENNReal := (Set.Ioo (0:ℝ) 1).indicator (fun v => ENNReal.ofReal (1 / v)) with hH
    have hHm : Measurable H := (Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ioo
    have hHl : ∫⁻ v, H v ∂m ≤ 1 := by rw [hH, lintegral_indicator measurableSet_Ioo]; exact hm3
    set h : ℝ → ℝ := fun v => (H v).toReal with hhdef
    have hhi : Integrable h m := integrable_toReal_of_lintegral_ne_top hHm.aemeasurable
      (ne_top_of_le_ne_top ENNReal.one_ne_top hHl)
    have hhint : ∫ v, h v ∂m ≤ 1 := by
      rw [hhdef, integral_toReal hHm.aemeasurable (Filter.Eventually.of_forall fun v => by
        simp only [hH]; by_cases hv : v ∈ Set.Ioo (0:ℝ) 1 <;> simp [hv])]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hHl)
    have hhval : ∀ v ∈ Set.Ioc (0:ℝ) 1, h v = if v < 1 then 1 / v else 0 := by
      intro v hv
      by_cases hv1 : v < 1
      · simp only [hhdef, hH, Set.indicator_of_mem (show v ∈ Set.Ioo (0:ℝ) 1 from ⟨hv.1, hv1⟩),
          if_pos hv1]
        exact ENNReal.toReal_ofReal (by have := hv.1; positivity)
      · simp only [hhdef, hH, Set.indicator_of_notMem (show v ∉ Set.Ioo (0:ℝ) 1 from fun h => hv1 h.2),
          if_neg hv1]
        simp
    have hfm : AEStronglyMeasurable (fun α => averageValueAtRisk P Y α) m := by
      rw [← hν]; exact hcont.aestronglyMeasurable measurableSet_Ioc
    have hfi : Integrable (fun α => averageValueAtRisk P Y α) m := by
      refine Integrable.mono' ((hhi.add (integrable_const 1)).const_mul K) hfm ?_
      filter_upwards [hae] with v hv
      refine (Real.norm_eq_abs _ ▸ hbound v hv).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK0
      simp only [Pi.add_apply]
      rw [hhval v hv]
      split_ifs with hv1
      · linarith
      · have : v = 1 := le_antisymm hv.2 (not_lt.1 hv1)
        subst this; norm_num
    have hgi : Integrable (fun v => M - c * h v) m := (integrable_const M).sub (hhi.const_mul c)
    have hle : ∫ v, (M - c * h v) ∂m ≤ ∫ v, averageValueAtRisk P Y v ∂m := by
      refine integral_mono_ae hgi hfi ?_
      filter_upwards [hae] with v hv
      rw [hhval v hv]
      split_ifs with hv1
      · have := hRU v ⟨hv.1, hv1⟩
        rw [div_eq_mul_one_div] at this; linarith
      · have : v = 1 := le_antisymm hv.2 (not_lt.1 hv1)
        subst this; rw [hAV1]; simp
    rw [integral_sub (integrable_const M) (hhi.const_mul c), integral_const, integral_const_mul] at hle
    simp at hle
    have := mul_le_mul_of_nonneg_left hhint hc0
    linarith
