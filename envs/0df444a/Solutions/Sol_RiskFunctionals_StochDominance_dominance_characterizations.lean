-- Prove2me | solution 1 for RiskFunctionals.StochDominance.dominance_characterizations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:05:46.391615+00:00
-- url     : https://prove2.me/submissions/0ec4cd70-bb07-460a-a811-3838b442b48b

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction
import Definitions.Def_RiskFunctionals_StochDominance_IntegratedFunctions
import Definitions.Def_RiskFunctionals_StochDominance_Dominance
import Theorems.Thm_StochasticOrders_Convex_convex_order_martingale_coupling_iff_v2
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

open RiskFunctionals.StochDominance
open MeasureTheory

theorem g79t_idf (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    ∫ v in Set.Iic u, distributionFunction μ v = ∫ y, max (u - y) 0 ∂μ := by
  have hmono : Monotone (distributionFunction μ) := fun a b hab =>
    measureReal_mono (Set.Iic_subset_Iic.2 hab)
  have hF : ∀ v, ENNReal.ofReal (distributionFunction μ v) = μ (Set.Iic v) := by
    intro v; simp [distributionFunction, measureReal_def]
  rw [integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (Set.Iic u))
      (f := distributionFunction μ) (ae_of_all _ (fun v => measureReal_nonneg))
      hmono.measurable.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (μ := μ) (f := fun y => max (u - y) 0)
      (ae_of_all _ (fun y => le_max_right _ _)) (by fun_prop)]
  congr 1
  simp_rw [hF]
  set k : ℝ × ℝ → ENNReal := fun p => if p.2 ≤ p.1 then 1 else 0 with hk
  have hkm : Measurable k := Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    measurable_const measurable_const
  calc ∫⁻ v in Set.Iic u, μ (Set.Iic v)
      = ∫⁻ v in Set.Iic u, ∫⁻ y, k (v, y) ∂μ := by
        refine lintegral_congr fun v => ?_
        rw [← lintegral_indicator_one measurableSet_Iic]
        refine lintegral_congr fun y => ?_
        simp only [hk, Set.indicator, Set.mem_Iic, Pi.one_apply]
    _ = ∫⁻ y, (∫⁻ v in Set.Iic u, k (v, y)) ∂μ := lintegral_lintegral_swap hkm.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (max (u - y) 0) ∂μ := by
        refine lintegral_congr fun y => ?_
        have : (fun v => k (v, y)) = (Set.Ici y).indicator 1 := by
          funext v; simp only [hk, Set.indicator, Set.mem_Ici, Pi.one_apply]
        rw [this, lintegral_indicator_one measurableSet_Ici, Measure.restrict_apply measurableSet_Ici,
          Set.Ici_inter_Iic, Real.volume_Icc]
        rcases le_total y u with h | h
        · rw [max_eq_left (by linarith)]
        · rw [max_eq_right (by linarith), ENNReal.ofReal_of_nonpos (by linarith)]; simp

theorem g79t_key (μ : Measure ℝ) [IsProbabilityMeasure μ] (hI : Integrable (fun y : ℝ => y) μ)
    (u : ℝ) : ∫ t in Set.Ioc 0 (μ.real (Set.Iic u)), g79q_q μ t
      = μ.real (Set.Iic u) * u - ∫ y, max (u - y) 0 ∂μ := by
  set p := μ.real (Set.Iic u) with hpdef
  have hp1 : p ≤ 1 := by rw [hpdef]; exact measureReal_le_one
  set q := g79q_q μ with hqdef
  set gM : ℝ → ℝ := (Set.Iic u).indicator (fun y => y) with hgM
  have hgMi : Integrable gM μ := hI.indicator measurableSet_Iic
  have hEg := g79n_E μ gM (measurable_id.indicator measurableSet_Iic) hgMi
  have hc' : ∫ y, max (u - y) 0 ∂μ = p * u - ∫ y, gM y ∂μ := by
    have : (fun x => max (u - x) 0) = (Set.Iic u).indicator (fun y => u - y) := by
      funext x
      by_cases h : x ≤ u
      · rw [Set.indicator_of_mem (by exact h), max_eq_left (by linarith)]
      · rw [Set.indicator_of_notMem (by exact h), max_eq_right (by push_neg at h; linarith)]
    rw [this, integral_indicator measurableSet_Iic, hgM, integral_indicator measurableSet_Iic,
      integral_sub (integrable_const u).integrableOn hI.integrableOn, setIntegral_const]
    simp [hpdef]
  rw [hc', hEg.2, intervalIntegral.integral_of_le zero_le_one]
  have hs : ∫ t in Set.Ioc 0 p, q t = ∫ t in Set.Ioc 0 1, (Set.Ioc 0 p).indicator q t := by
    rw [setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 (Set.Ioc_subset_Ioc_right hp1)]
  rw [hs]
  have hne1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
    rw [ae_iff]; simp
  have : ∫ t in Set.Ioc 0 1, (Set.Ioc 0 p).indicator q t = ∫ t in Set.Ioc 0 1, gM (q t) := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [hne1] with t ht1 ht
    have ht' : t < 1 := lt_of_le_of_ne ht.2 ht1
    have hiff := g79q_qle' μ ht.1 ht' u
    by_cases h : t ≤ p
    · rw [Set.indicator_of_mem (show t ∈ Set.Ioc 0 p from ⟨ht.1, h⟩), hgM,
        Set.indicator_of_mem (show q t ∈ Set.Iic u from hiff.2 h)]
    · rw [Set.indicator_of_notMem (fun h' => h h'.2), hgM,
        Set.indicator_of_notMem (show q t ∉ Set.Iic u from fun h' => h (hiff.1 h'))]
  rw [this]; ring

theorem g97_conj (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun v : ℝ => v) μ) :
    (∀ u : ℝ, IsLUB {x : ℝ | ∃ q ∈ Set.Ioo (0 : ℝ) 1,
        x = u * q - integratedQuantileFunction μ q} (integratedDistributionFunction μ u)) ∧
    (∀ q ∈ Set.Ioo (0 : ℝ) 1, IsLUB {x : ℝ | ∃ u : ℝ,
        x = u * q - integratedDistributionFunction μ u} (integratedQuantileFunction μ q)) := by
  have hIDF : ∀ u, integratedDistributionFunction μ u = ∫ y, max (u - y) 0 ∂μ := g79t_idf μ
  have hIQF : ∀ t, integratedQuantileFunction μ t = ∫ s in Set.Ioc 0 t, g79q_q μ s := fun t => rfl
  have hE := g79n_E μ (fun y => y) measurable_id hμ
  have hqI : IntegrableOn (g79q_q μ) (Set.Icc 0 1) := hE.1
  constructor
  · intro u
    set g : ℝ → ℝ := fun t => u * t - ∫ s in Set.Ioc 0 t, g79q_q μ s with hg
    have hgle : ∀ t ∈ Set.Ioo (0:ℝ) 1, g t ≤ ∫ y, max (u - y) 0 ∂μ := by
      intro t ht
      have h := (g79n_RU μ hμ ht.1 ht.2).1 u
      rw [intervalIntegral.integral_of_le ht.1.le] at h
      simp only [hg]; linarith
    set p := μ.real (Set.Iic u) with hpdef
    have hp0 : 0 ≤ p := measureReal_nonneg
    have hp1 : p ≤ 1 := by rw [hpdef]; exact measureReal_le_one
    have hgp : g p = ∫ y, max (u - y) 0 ∂μ := by
      simp only [hg]; rw [hpdef, g79t_key μ hμ u]; ring
    have hcont : ContinuousOn g (Set.Icc 0 1) := by
      have hprim : ContinuousOn (fun x => ∫ t in (0:ℝ)..x, g79q_q μ t) (Set.uIcc 0 1) :=
        intervalIntegral.continuousOn_primitive_interval (by rwa [Set.uIcc_of_le zero_le_one])
      rw [Set.uIcc_of_le zero_le_one] at hprim
      refine (ContinuousOn.sub (f := fun t : ℝ => u * t) (by fun_prop) hprim).congr fun t ht => ?_
      simp only [Pi.sub_apply, hg, intervalIntegral.integral_of_le ht.1]
    rw [hIDF]
    constructor
    · rintro x ⟨t, ht, rfl⟩
      rw [hIQF]; exact hgle t ht
    · intro b hb
      by_contra hlt
      push_neg at hlt
      rw [← hgp] at hlt
      have hev : ∀ᶠ t in nhdsWithin p (Set.Icc 0 1), b < g t :=
        (hcont p ⟨hp0, hp1⟩).eventually (lt_mem_nhds hlt)
      have hev' : ∀ᶠ t in nhdsWithin p (Set.Ioo 0 1), b < g t ∧ t ∈ Set.Ioo (0:ℝ) 1 :=
        (hev.filter_mono (nhdsWithin_mono p Set.Ioo_subset_Icc_self)).and self_mem_nhdsWithin
      haveI : (nhdsWithin p (Set.Ioo (0:ℝ) 1)).NeBot := by
        apply mem_closure_iff_nhdsWithin_neBot.1
        rw [closure_Ioo zero_ne_one]; exact ⟨hp0, hp1⟩
      obtain ⟨t, hbt, ht⟩ := hev'.exists
      have := hb ⟨t, ht, by rw [hIQF]⟩
      simp only [hg] at hbt
      linarith
  · intro q hq
    constructor
    · rintro x ⟨u, rfl⟩
      have h := (g79n_RU μ hμ hq.1 hq.2).1 u
      rw [intervalIntegral.integral_of_le hq.1.le] at h
      rw [hIDF, hIQF]; linarith
    · intro b hb
      have h := (g79n_RU μ hμ hq.1 hq.2).2
      rw [intervalIntegral.integral_of_le hq.1.le] at h
      have := hb ⟨g79q_q μ q, rfl⟩
      rw [hIDF] at this
      rw [hIQF]; linarith

theorem g79q_fsd_cdf (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : FSD μ₁ μ₂) (u : ℝ) : g79q_F μ₂ u ≤ g79q_F μ₁ u := by
  have hU : Monotone ((Set.Ioi u).indicator (1 : ℝ → ℝ)) := by
    intro a b hab
    by_cases ha : a ∈ Set.Ioi u
    · have hb : b ∈ Set.Ioi u := lt_of_lt_of_le ha hab
      simp [Set.indicator_of_mem ha, Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) b
  have hi : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      Integrable ((Set.Ioi u).indicator (1 : ℝ → ℝ)) μ :=
    fun μ _ => (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have := h _ hU (hi μ₁) (hi μ₂)
  rw [integral_indicator_one measurableSet_Ioi, integral_indicator_one measurableSet_Ioi,
    ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic] at this
  unfold g79q_F; linarith


open MeasureTheory ProbabilityTheory

open MeasureTheory
namespace SD97

theorem abel_layer (w : ℝ → ℝ) (hw : Measurable w) (f₁ f₂ : ℝ → ENNReal)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (S : Set ℝ)
    (hlev : ∀ s : ℝ, 0 < s → ∫⁻ t in {t | s < w t} ∩ S, f₁ t ≤ ∫⁻ t in {t | s < w t} ∩ S, f₂ t) :
    ∫⁻ t in S, ENNReal.ofReal (w t) * f₁ t ≤ ∫⁻ t in S, ENNReal.ofReal (w t) * f₂ t := by
  have key : ∀ f : ℝ → ENNReal, Measurable f → ∀ t, ENNReal.ofReal (w t) * f t =
      ∫⁻ s, (if 0 < s ∧ s < w t then f t else 0) := by
    intro f _ t
    have : (fun s => if 0 < s ∧ s < w t then f t else 0) = (Set.Ioo 0 (w t)).indicator (fun _ => f t) := by
      ext s; simp [Set.indicator_apply, Set.mem_Ioo]
    rw [this, lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero, mul_comm]
  have hmeas : ∀ f : ℝ → ENNReal, Measurable f →
      Measurable (Function.uncurry fun t s => if 0 < s ∧ s < w t then f t else 0) := by
    intro f hf
    refine Measurable.ite ?_ (hf.comp measurable_fst) measurable_const
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (hw.comp measurable_fst))
  simp_rw [key f₁ hf₁, key f₂ hf₂]
  rw [lintegral_lintegral_swap (hmeas f₁ hf₁).aemeasurable,
    lintegral_lintegral_swap (hmeas f₂ hf₂).aemeasurable]
  refine lintegral_mono fun s => ?_
  by_cases hs : 0 < s
  · have e : ∀ f : ℝ → ENNReal, Measurable f →
        ∫⁻ t in S, (if 0 < s ∧ s < w t then f t else 0) = ∫⁻ t in {t | s < w t} ∩ S, f t := by
      intro f hf
      have hm : MeasurableSet {t | s < w t} := measurableSet_lt measurable_const hw
      rw [← Measure.restrict_restrict hm, ← lintegral_indicator hm]
      congr 1; ext t; simp [Set.indicator_apply, hs]
    rw [e f₁ hf₁, e f₂ hf₂]; exact hlev s hs
  · simp [hs]

theorem abel_seg (h : ℝ → ℝ) (E : Set ℝ) (hh : IntegrableOn h E) (h0 : 0 ≤ ∫ t in E, h t) :
    ∫⁻ t in E, ENNReal.ofReal (-h t) ≤ ∫⁻ t in E, ENNReal.ofReal (h t) := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh] at h0
  have h1 := hh.lintegral_lt_top
  have h2 := hh.neg.lintegral_lt_top
  simp only [Pi.neg_apply] at h2
  rw [← ENNReal.toReal_le_toReal h2.ne h1.ne]
  simpa using h0

theorem abel_init (h : ℝ → ℝ)
    (hD : ∀ a ∈ Set.Ioc (0:ℝ) 1, 0 ≤ ∫ t in Set.Ioc 0 a, h t)
    (P : Set ℝ) (hP : ∀ t u, 0 < t → t ≤ u → u ∈ Set.Ioo 0 1 ∩ P → t ∈ P) :
    0 ≤ ∫ t in Set.Ioc 0 1 ∩ P, h t := by
  set T := Set.Ioo (0:ℝ) 1 ∩ P with hT
  have hsub : (Set.Ioc (0:ℝ) 1 ∩ P) \ T ⊆ {1} := by
    intro t ⟨⟨⟨h0, h1⟩, hp⟩, hnt⟩
    by_contra hne
    exact hnt ⟨⟨h0, lt_of_le_of_ne h1 hne⟩, hp⟩
  rcases T.eq_empty_or_nonempty with he | hne
  · have : volume (Set.Ioc 0 1 ∩ P) = 0 := by
      refine measure_mono_null (fun t ht => hsub ⟨ht, by simp [he]⟩) (measure_singleton 1)
    rw [Measure.restrict_eq_zero.mpr this]; simp
  · have hbdd : BddAbove T := ⟨1, fun t ht => ht.1.2.le⟩
    set a := sSup T
    obtain ⟨u, hu⟩ := hne
    have ha0 : 0 < a := lt_of_lt_of_le hu.1.1 (le_csSup hbdd hu)
    have ha1 : a ≤ 1 := csSup_le ⟨u, hu⟩ fun t ht => ht.1.2.le
    have hae : (Set.Ioc (0:ℝ) 1 ∩ P : Set ℝ) =ᵐ[volume] (Set.Ioc 0 a : Set ℝ) := by
      rw [ae_eq_set]
      constructor
      · refine measure_mono_null ?_ (measure_singleton (1:ℝ))
        intro t ⟨ht, hta⟩
        by_contra hne
        have htT : t ∈ T := ⟨⟨ht.1.1, lt_of_le_of_ne ht.1.2 hne⟩, ht.2⟩
        exact hta ⟨ht.1.1, le_csSup hbdd htT⟩
      · refine measure_mono_null ?_ (measure_singleton a)
        intro t ⟨ht, htn⟩
        by_contra hne
        have hta : t < a := lt_of_le_of_ne ht.2 hne
        obtain ⟨v, hv, htv⟩ := exists_lt_of_lt_csSup ⟨u, hu⟩ hta
        exact htn ⟨⟨ht.1, (htv.le.trans hv.1.2.le)⟩, hP t v ht.1 htv.le hv⟩
    rw [setIntegral_congr_set hae]
    exact hD a ⟨ha0, ha1⟩

theorem abel_ofReal_mul (x y : ℝ) :
    ENNReal.ofReal (x * y) = ENNReal.ofReal x * ENNReal.ofReal y + ENNReal.ofReal (-x) * ENNReal.ofReal (-y) := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [ENNReal.ofReal_mul hx, ENNReal.ofReal_of_nonpos (by linarith : -x ≤ 0)]; simp
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hx hy),
      ENNReal.ofReal_of_nonpos hy, ENNReal.ofReal_of_nonpos (by linarith : -x ≤ 0)]; simp
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hx hy),
      ENNReal.ofReal_of_nonpos hx, ENNReal.ofReal_of_nonpos (by linarith : -y ≤ 0)]; simp
  · rw [← neg_mul_neg, ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_of_nonpos hx]; simp

theorem abel_main (g h : ℝ → ℝ) (hgm : Measurable g) (hhm : Measurable h)
    (hg : AntitoneOn g (Set.Ioo 0 1))
    (hh : IntegrableOn h (Set.Ioc 0 1))
    (hD : ∀ a ∈ Set.Ioo (0:ℝ) 1, 0 ≤ ∫ t in Set.Ioc 0 a, h t)
    (hcase : (∀ t ∈ Set.Ioo (0:ℝ) 1, 0 ≤ g t) ∨ ∫ t in Set.Ioc 0 1, h t = 0)
    (hpos : IntegrableOn (fun t => max (g t * h t) 0) (Set.Ioc 0 1)) :
    IntegrableOn (fun t => g t * h t) (Set.Ioc 0 1) ∧ 0 ≤ ∫ t in Set.Ioc 0 1, g t * h t := by
  set I := Set.Ioc (0:ℝ) 1 with hI
  -- nonnegativity at a = 1
  have hD1 : 0 ≤ ∫ t in I, h t := by
    rcases hcase with _ | h0
    · have hint : IntegrableOn h (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]; exact (integrableOn_Icc_iff_integrableOn_Ioc (f := h) (a := 0) (b := 1)).mpr hh
      have hc := intervalIntegral.continuousOn_primitive_interval hint
      rw [Set.uIcc_of_le zero_le_one] at hc
      have hc1 : ContinuousWithinAt (fun x => ∫ t in (0:ℝ)..x, h t) (Set.Ioo 0 1) 1 :=
        (hc 1 ⟨zero_le_one, le_rfl⟩).mono Set.Ioo_subset_Icc_self
      have ht : Filter.Tendsto (fun x => ∫ t in (0:ℝ)..x, h t) (nhdsWithin 1 (Set.Iio 1))
          (nhds (∫ t in (0:ℝ)..1, h t)) := by
        rw [← nhdsWithin_Ioo_eq_nhdsLT zero_lt_one]; exact hc1
      have := ge_of_tendsto ht (by
        rw [← nhdsWithin_Ioo_eq_nhdsLT zero_lt_one]
        refine eventually_nhdsWithin_of_forall fun a ha => ?_
        rw [intervalIntegral.integral_of_le ha.1.le]; exact hD a ha)
      rwa [intervalIntegral.integral_of_le zero_le_one] at this
    · rw [h0]
  have hD' : ∀ a ∈ Set.Ioc (0:ℝ) 1, 0 ≤ ∫ t in Set.Ioc 0 a, h t := by
    intro a ha
    rcases eq_or_lt_of_le ha.2 with e | e
    · rw [e]; exact hD1
    · exact hD a ⟨ha.1, e⟩
  have hIm : MeasurableSet I := measurableSet_Ioc
  have hP : ∫⁻ t in I, ENNReal.ofReal (g t * h t) =
      (∫⁻ t in I, ENNReal.ofReal (g t) * ENNReal.ofReal (h t)) +
      ∫⁻ t in I, ENNReal.ofReal (-g t) * ENNReal.ofReal (-h t) := by
    simp_rw [abel_ofReal_mul]
    exact lintegral_add_left ((ENNReal.measurable_ofReal.comp hgm).mul
      (ENNReal.measurable_ofReal.comp hhm)) _
  have hN : ∫⁻ t in I, ENNReal.ofReal (-(g t * h t)) =
      (∫⁻ t in I, ENNReal.ofReal (g t) * ENNReal.ofReal (-h t)) +
      ∫⁻ t in I, ENNReal.ofReal (-g t) * ENNReal.ofReal (h t) := by
    have : ∀ t, -(g t * h t) = g t * (-h t) := fun t => by ring
    simp_rw [this, abel_ofReal_mul, neg_neg]
    exact lintegral_add_left ((ENNReal.measurable_ofReal.comp hgm).mul
      (ENNReal.measurable_ofReal.comp hhm.neg)) _
  have hCA : (∫⁻ t in I, ENNReal.ofReal (g t) * ENNReal.ofReal (-h t)) ≤
      ∫⁻ t in I, ENNReal.ofReal (g t) * ENNReal.ofReal (h t) := by
    refine abel_layer g hgm _ _ (ENNReal.measurable_ofReal.comp hhm.neg)
      (ENNReal.measurable_ofReal.comp hhm) I fun s _ => ?_
    refine abel_seg h _ (hh.mono_set Set.inter_subset_right) ?_
    rw [Set.inter_comm]
    refine abel_init h hD' _ fun t u ht htu hu => ?_
    exact lt_of_lt_of_le hu.2 (hg ⟨ht, htu.trans_lt hu.1.2⟩ hu.1 htu)
  have hDB : (∫⁻ t in I, ENNReal.ofReal (-g t) * ENNReal.ofReal (h t)) ≤
      ∫⁻ t in I, ENNReal.ofReal (-g t) * ENNReal.ofReal (-h t) := by
    refine abel_layer (fun t => -g t) hgm.neg _ _ (ENNReal.measurable_ofReal.comp hhm)
      (ENNReal.measurable_ofReal.comp hhm.neg) I fun s hs => ?_
    have := abel_seg (fun t => -h t) ({t | s < -g t} ∩ I)
      (hh.neg.mono_set Set.inter_subset_right)
    simp only [neg_neg] at this
    refine this ?_
    rw [integral_neg, neg_nonneg]
    rcases hcase with hg0 | h0
    · have : volume ({t | s < -g t} ∩ I) = 0 := by
        refine measure_mono_null (fun t ht => ?_) (measure_singleton (1:ℝ))
        by_contra hne
        have := hg0 t ⟨ht.2.1, lt_of_le_of_ne ht.2.2 hne⟩
        have := ht.1; simp only [Set.mem_ofPred_eq] at this; linarith
      rw [Measure.restrict_eq_zero.mpr this]; simp
    · have hm : MeasurableSet {t | -g t ≤ s} := measurableSet_le hgm.neg measurable_const
      have hsplit := integral_inter_add_sdiff hm hh
      have hE : I \ {t | -g t ≤ s} = {t | s < -g t} ∩ I := by
        ext t; simp [and_comm]
      rw [hE, h0] at hsplit
      have := abel_init h hD' {t | -g t ≤ s} fun t u ht htu hu => by
        have := hg ⟨ht, htu.trans_lt hu.1.2⟩ hu.1 htu
        have := hu.2; simp only [Set.mem_ofPred_eq] at this ⊢; linarith
      linarith
  have hPfin : ∫⁻ t in I, ENNReal.ofReal (g t * h t) < ⊤ := by
    have := hpos.lintegral_lt_top
    convert this using 3 with t
    rcases le_total 0 (g t * h t) with e | e
    · rw [max_eq_left e]
    · rw [max_eq_right e, ENNReal.ofReal_of_nonpos e, ENNReal.ofReal_zero]
  have hNP : ∫⁻ t in I, ENNReal.ofReal (-(g t * h t)) ≤ ∫⁻ t in I, ENNReal.ofReal (g t * h t) := by
    rw [hN, hP]; exact add_le_add hCA hDB
  have hint : IntegrableOn (fun t => g t * h t) I := by
    refine ⟨(hgm.mul hhm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have : ∀ x : ℝ, ‖x‖ₑ = ENNReal.ofReal x + ENNReal.ofReal (-x) := fun x => by
      rw [Real.enorm_eq_ofReal_abs]
      rcases le_total 0 x with e | e
      · rw [abs_of_nonneg e, ENNReal.ofReal_of_nonpos (by linarith : -x ≤ 0), add_zero]
      · rw [abs_of_nonpos e, ENNReal.ofReal_of_nonpos e, zero_add]
    simp_rw [this]
    have hm : Measurable fun t => ENNReal.ofReal (g t * h t) := by fun_prop
    rw [lintegral_add_left hm]
    exact ENNReal.add_lt_top.mpr ⟨hPfin, lt_of_le_of_lt hNP hPfin⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint, sub_nonneg]
  exact ENNReal.toReal_mono hPfin.ne hNP

theorem abel (g h : ℝ → ℝ) (hgm : Measurable g) (hg : AntitoneOn g (Set.Ioo 0 1))
    (hh : IntegrableOn h (Set.Ioc 0 1))
    (hD : ∀ a ∈ Set.Ioo (0:ℝ) 1, 0 ≤ ∫ t in Set.Ioc 0 a, h t)
    (hcase : (∀ t ∈ Set.Ioo (0:ℝ) 1, 0 ≤ g t) ∨ ∫ t in Set.Ioc 0 1, h t = 0)
    (hpos : IntegrableOn (fun t => max (g t * h t) 0) (Set.Ioc 0 1)) :
    IntegrableOn (fun t => g t * h t) (Set.Ioc 0 1) ∧ 0 ≤ ∫ t in Set.Ioc 0 1, g t * h t := by
  set h' := hh.aestronglyMeasurable.mk h with hh'def
  have hhm : Measurable h' := hh.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : h =ᵐ[volume.restrict (Set.Ioc 0 1)] h' := hh.aestronglyMeasurable.ae_eq_mk
  have hae' : ∀ a ≤ (1:ℝ), ∫ t in Set.Ioc 0 a, h t = ∫ t in Set.Ioc 0 a, h' t := fun a ha =>
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Ioc_right ha) hae)
  have hgae : (fun t => g t * h t) =ᵐ[volume.restrict (Set.Ioc 0 1)] fun t => g t * h' t := by
    filter_upwards [hae] with t ht; rw [ht]
  have hgae' : (fun t => max (g t * h t) 0) =ᵐ[volume.restrict (Set.Ioc 0 1)]
      fun t => max (g t * h' t) 0 := by
    filter_upwards [hae] with t ht; rw [ht]
  have := abel_main g h' hgm hhm hg (hh.congr_fun_ae hae)
    (fun a ha => (hae' a ha.2.le) ▸ hD a ha)
    (hcase.imp id fun e => (hae' 1 le_rfl) ▸ e) (hpos.congr_fun_ae hgae')
  refine ⟨this.1.congr_fun_ae hgae.symm, ?_⟩
  rw [integral_congr_ae hgae]; exact this.2

end SD97


namespace SD97

theorem superg (U : ℝ → ℝ) (hU : ConcaveOn ℝ Set.univ U) :
    ∃ s : ℝ → ℝ, Antitone s ∧ (∀ x y, U y ≤ U x + s x * (y - x)) ∧
      (Monotone U → ∀ x, 0 ≤ s x) := by
  -- right slopes are bounded by left slopes
  have hadj : ∀ z x y : ℝ, z < x → x < y →
      (U y - U x) / (y - x) ≤ (U x - U z) / (x - z) := fun z x y h1 h2 =>
    hU.slope_anti_adjacent (Set.mem_univ _) (Set.mem_univ _) h1 h2
  let S : ℝ → Set ℝ := fun x => (fun y => (U y - U x) / (y - x)) '' Set.Ioi x
  have hne : ∀ x, (S x).Nonempty := fun x => ⟨_, x + 1, by simp, rfl⟩
  have hbdd : ∀ x, BddAbove (S x) := by
    intro x
    refine ⟨(U x - U (x - 1)) / (x - (x - 1)), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hadj (x - 1) x y (by linarith) hy
  refine ⟨fun x => sSup (S x), ?_, ?_, ?_⟩
  · intro x x' hxx'
    rcases eq_or_lt_of_le hxx' with rfl | hlt
    · exact le_rfl
    · have h1 : sSup (S x') ≤ (U x' - U x) / (x' - x) := by
        refine csSup_le (hne x') ?_
        rintro _ ⟨y, hy, rfl⟩
        exact hadj x x' y hlt hy
      have h2 : (U x' - U x) / (x' - x) ≤ sSup (S x) :=
        le_csSup (hbdd x) ⟨x', hlt, rfl⟩
      exact h1.trans h2
  · intro x y
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · have h : sSup (S x) ≤ (U x - U y) / (x - y) := by
        refine csSup_le (hne x) ?_
        rintro _ ⟨z, hz, rfl⟩
        exact hadj y x z hyx hz
      have hpos : 0 < x - y := by linarith
      rw [le_div_iff₀ hpos] at h
      nlinarith
    · simp
    · have h : (U y - U x) / (y - x) ≤ sSup (S x) := le_csSup (hbdd x) ⟨y, hxy, rfl⟩
      have hpos : 0 < y - x := by linarith
      rw [div_le_iff₀ hpos] at h
      linarith
  · intro hm x
    have h : (U (x + 1) - U x) / (x + 1 - x) ≤ sSup (S x) :=
      le_csSup (hbdd x) ⟨x + 1, by simp, rfl⟩
    have : 0 ≤ (U (x + 1) - U x) / (x + 1 - x) :=
      div_nonneg (by linarith [hm (show x ≤ x + 1 by linarith)]) (by linarith)
    linarith

end SD97

open MeasureTheory ProbabilityTheory
open RiskFunctionals.StochDominance
namespace SD97

theorem kc_eq_comp (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (hcdf : ∀ u : ℝ, distributionFunction μ₁ u = ∫ v, distributionFunction (K v) u ∂μ₂) :
    μ₁ = K ∘ₘ μ₂ := by
  have : IsProbabilityMeasure (K ∘ₘ μ₂) := by
    constructor; simp
  refine Measure.ext_of_Iic _ _ (fun u => ?_)
  rw [Measure.bind_apply measurableSet_Iic K.aemeasurable]
  have h := hcdf u
  unfold distributionFunction at h
  rw [← ofReal_measureReal (measure_ne_top _ _), h,
    ofReal_integral_eq_lintegral_ofReal]
  · apply lintegral_congr; intro v
    simp [ofReal_measureReal (measure_ne_top _ _)]
  · refine Integrable.of_bound (C := 1) ?_ ?_
    · exact ((K.measurable_coe measurableSet_Iic).ennreal_toReal).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun v => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  · exact Filter.Eventually.of_forall (fun v => measureReal_nonneg)

theorem kc_continuous (U : ℝ → ℝ) (hU : ConcaveOn ℝ Set.univ U) : Continuous U := by
  have := hU.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

theorem ccd_of_kernel (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h1 : Integrable (fun v : ℝ => v) μ₁) (h2 : Integrable (fun v : ℝ => v) μ₂)
    (hK : ∃ K : Kernel ℝ ℝ, IsMarkovKernel K ∧
        (∀ u : ℝ, distributionFunction μ₁ u = ∫ v, distributionFunction (K v) u ∂μ₂) ∧
        (∀ v : ℝ, Integrable (fun u : ℝ => u) (K v) ∧ ∫ u, u ∂(K v) = v)) :
    CCD μ₁ μ₂ := by
  have _ := h1; have _ := h2
  obtain ⟨K, hKm, hcdf, hmean⟩ := hK
  have hμ := kc_eq_comp μ₁ μ₂ K hcdf
  intro U hU hU1 hU2
  have hUc := kc_continuous U hU
  rw [hμ] at hU1 ⊢
  have hae : ∀ᵐ v ∂μ₂, Integrable U (K v) := Measure.ae_integrable_of_integrable_comp hU1
  have hint : ∫ v, U v ∂(K ∘ₘ μ₂) = ∫ v, ∫ y, U y ∂(K v) ∂μ₂ := by
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp]
    · simp
    · rw [← Measure.comp_eq_comp_const_apply]; exact hU1
  rw [hint]
  refine integral_mono_ae ?_ hU2 ?_
  · rw [Measure.comp_eq_comp_const_apply] at hU1
    simpa using hU1.integral_comp
  · filter_upwards [hae] with v hv
    have := hU.le_map_integral (μ := K v) (f := fun u => u) hUc.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) (hmean v).1 hv
    rw [(hmean v).2] at this
    exact this

theorem kc_convexOrder (μ₁ μ₂ : Measure ℝ) (hc : CCD μ₁ μ₂) :
    StochasticOrders.Convex.ConvexOrder μ₂ μ₁ id id := by
  intro φ hφ hi2 hi1
  have := hc (fun x => -φ x) hφ.neg hi1.neg hi2.neg
  simp only [integral_neg, id] at this ⊢
  linarith

theorem kernel_of_ccd (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h1 : Integrable (fun v : ℝ => v) μ₁) (h2 : Integrable (fun v : ℝ => v) μ₂)
    (hc : CCD μ₁ μ₂) :
    ∃ K : Kernel ℝ ℝ, IsMarkovKernel K ∧
        (∀ u : ℝ, distributionFunction μ₁ u = ∫ v, distributionFunction (K v) u ∂μ₂) ∧
        (∀ v : ℝ, Integrable (fun u : ℝ => u) (K v) ∧ ∫ u, u ∂(K v) = v) := by
  obtain ⟨Ω, _, ρ, _, X, Y, hXm, hYm, hXd, hYd, hce, κ, hκ, hjoint, -⟩ :=
    (StochasticOrders.Convex.convex_order_martingale_coupling_iff_v2 μ₂ μ₁ id id
      measurable_id measurable_id h2 h1).1 (kc_convexOrder μ₁ μ₂ hc)
  have hX : ρ.map X = μ₂ := by rw [hXd.map_eq, Measure.map_id]
  have hY : ρ.map Y = μ₁ := by rw [hYd.map_eq, Measure.map_id]
  rw [hX] at hjoint
  have hXi : Integrable X ρ := hXd.integrable_iff.2 h2
  have hYi : Integrable Y ρ := hYd.integrable_iff.2 h1
  have hXYm : Measurable (fun ω => (X ω, Y ω)) := hXm.prodMk hYm
  -- μ₁ = κ ∘ₘ μ₂
  have hμ₁ : μ₁ = κ ∘ₘ μ₂ := by
    rw [← hY, ← Measure.snd_compProd, ← hjoint, Measure.snd, Measure.map_map measurable_snd hXYm]
    rfl
  -- integrability of p.2 under joint law
  have hsnd : Integrable (fun p : ℝ × ℝ => p.2) (μ₂ ⊗ₘ κ) := by
    rw [← hjoint, integrable_map_measure measurable_snd.aestronglyMeasurable hXYm.aemeasurable]
    exact hYi
  have hae_int : ∀ᵐ x ∂μ₂, Integrable (fun y : ℝ => y) (κ x) :=
    ((Measure.integrable_compProd_iff hsnd.1).1 hsnd).1
  have hF : Integrable (fun x => ∫ y, y ∂(κ x)) μ₂ := hsnd.integral_compProd
  have hset : ∀ A : Set ℝ, MeasurableSet A →
      ∫ x in A, (∫ y, y ∂(κ x)) ∂μ₂ = ∫ x in A, x ∂μ₂ := by
    intro A hA
    have e1 : ∫ x in A, (∫ y, y ∂(κ x)) ∂μ₂ = ∫ p in A ×ˢ Set.univ, p.2 ∂(μ₂ ⊗ₘ κ) := by
      rw [Measure.setIntegral_compProd hA MeasurableSet.univ hsnd.integrableOn]
      simp
    have hm : MeasurableSpace.comap X inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
      hXm.comap_le
    have hpre : MeasurableSet[MeasurableSpace.comap X inferInstance] (X ⁻¹' A) :=
      ⟨A, hA, rfl⟩
    have e2 : ∫ p in A ×ˢ Set.univ, p.2 ∂(μ₂ ⊗ₘ κ) = ∫ ω in X ⁻¹' A, Y ω ∂ρ := by
      rw [← hjoint, setIntegral_map (hA.prod MeasurableSet.univ)
        measurable_snd.aestronglyMeasurable hXYm.aemeasurable]
      have hp : (fun ω => (X ω, Y ω)) ⁻¹' (A ×ˢ Set.univ) = X ⁻¹' A := by ext; simp
      rw [hp]
    have e3 : ∫ ω in X ⁻¹' A, Y ω ∂ρ = ∫ ω in X ⁻¹' A, X ω ∂ρ := by
      rw [← setIntegral_condExp hm hYi hpre]
      exact setIntegral_congr_ae (hm _ hpre) (by filter_upwards [hce] with ω h _ using h)
    have e4 : ∫ ω in X ⁻¹' A, X ω ∂ρ = ∫ x in A, x ∂μ₂ := by
      rw [← hX, setIntegral_map (f := fun x : ℝ => x) hA aestronglyMeasurable_id hXm.aemeasurable]
    rw [e1, e2, e3, e4]
  have hae_mean : (fun x => ∫ y, y ∂(κ x)) =ᵐ[μ₂] (fun x => x) :=
    ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => hF.integrableOn)
      (fun s _ _ => h2.integrableOn) (fun s hs _ => hset s hs)
  set G : Set ℝ := {x | Integrable (fun y : ℝ => y) (κ x) ∧ ∫ y, y ∂(κ x) = x} with hGdef
  have hGc : μ₂ Gᶜ = 0 := by
    have : ∀ᵐ x ∂μ₂, x ∈ G := by
      filter_upwards [hae_int, hae_mean] with x h1 h2 using ⟨h1, h2⟩
    exact this
  set N := toMeasurable μ₂ Gᶜ
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : μ₂ N = 0 := by rw [measure_toMeasurable]; exact hGc
  have hNG : Nᶜ ⊆ G := by
    intro x hx
    by_contra h
    exact hx (subset_toMeasurable _ _ h)
  classical
  let K : Kernel ℝ ℝ := Kernel.piecewise hN.compl κ (Kernel.deterministic id measurable_id)
  have hKae : ∀ᵐ x ∂μ₂, K x = κ x := by
    have : ∀ᵐ x ∂μ₂, x ∈ Nᶜ := by
      rw [ae_iff]; simpa using hN0
    filter_upwards [this] with x hx
    simp [K, Kernel.piecewise_apply, hx]
  refine ⟨K, inferInstance, ?_, ?_⟩
  · intro u
    unfold distributionFunction
    rw [integral_congr_ae (by filter_upwards [hKae] with x hx; rw [hx])]
    simp_rw [measureReal_def]
    rw [integral_toReal (κ.measurable_coe measurableSet_Iic).aemeasurable
      (Filter.Eventually.of_forall (fun _ => measure_lt_top _ _)), hμ₁,
      Measure.bind_apply measurableSet_Iic κ.aemeasurable]
  · intro v
    by_cases hv : v ∈ Nᶜ
    · have : K v = κ v := by simp [K, Kernel.piecewise_apply, hv]
      rw [this]; exact hNG hv
    · have : K v = Measure.dirac v := by
        simp [K, Kernel.piecewise_apply, hv, Kernel.deterministic_apply]
      rw [this]
      exact ⟨integrable_dirac (by simp), by simp⟩
end SD97


open MeasureTheory ProbabilityTheory
open RiskFunctionals.StochDominance

namespace SD97

theorem qeq (μ : Measure ℝ) : quantileFunction μ = g79q_q μ := rfl
theorem Feq (μ : Measure ℝ) : distributionFunction μ = g79q_F μ := rfl

theorem cont_of_concave {U : ℝ → ℝ} (hU : ConcaveOn ℝ Set.univ U) : Continuous U :=
  continuousOn_univ.1 (hU.continuousOn isOpen_univ)

/-- the endpoints of (0,1] are null -/
theorem ae_Ioo : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), t ∈ Set.Ioo (0:ℝ) 1 := by
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae h1] with t ht h
  exact ⟨ht.1, lt_of_le_of_ne ht.2 h⟩

/-- integral against the law as an integral of the quantile over (0,1] -/
theorem E_Ioc (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable g μ) :
    IntegrableOn (fun u => g (g79q_q μ u)) (Set.Ioc 0 1) ∧
    ∫ y, g y ∂μ = ∫ u in Set.Ioc 0 1, g (g79q_q μ u) := by
  obtain ⟨h1, h2⟩ := g79n_E μ g hg hgi
  exact ⟨h1.mono_set Set.Ioc_subset_Icc_self, by
    rw [h2, intervalIntegral.integral_of_le zero_le_one]⟩

/-- (ii) cdf order ↔ quantile order -/
theorem cdf_iff_q (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    (∀ u : ℝ, distributionFunction μ₂ u ≤ distributionFunction μ₁ u) ↔
    (∀ p ∈ Set.Ioo (0 : ℝ) 1, quantileFunction μ₁ p ≤ quantileFunction μ₂ p) := by
  rw [qeq, qeq, Feq, Feq]
  constructor
  · intro h p hp
    rw [g79q_qle' μ₁ hp.1 hp.2]
    exact ((g79q_qle' μ₂ hp.1 hp.2 _).1 le_rfl).trans (h _)
  · intro h u
    by_contra hlt
    push Not at hlt
    set p := (g79q_F μ₁ u + g79q_F μ₂ u) / 2 with hp
    have h0 : 0 ≤ g79q_F μ₁ u := measureReal_nonneg
    have h1 : g79q_F μ₂ u ≤ 1 := measureReal_le_one
    have hp0 : 0 < p := by rw [hp]; linarith
    have hp1 : p < 1 := by rw [hp]; linarith
    have hq2 : g79q_q μ₂ p ≤ u := (g79q_qle' μ₂ hp0 hp1 u).2 (by rw [hp]; linarith)
    have hq1 : g79q_q μ₁ p ≤ u := (h p ⟨hp0, hp1⟩).trans hq2
    have := (g79q_qle' μ₁ hp0 hp1 u).1 hq1
    rw [hp] at this; linarith

/-- (i) backward direction -/
theorem fsd_of_q (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : ∀ p ∈ Set.Ioo (0 : ℝ) 1, quantileFunction μ₁ p ≤ quantileFunction μ₂ p) :
    FSD μ₁ μ₂ := by
  intro U hU hU1 hU2
  obtain ⟨i1, e1⟩ := E_Ioc μ₁ U hU.measurable hU1
  obtain ⟨i2, e2⟩ := E_Ioc μ₂ U hU.measurable hU2
  rw [e1, e2]
  refine setIntegral_mono_ae_restrict i1 i2 ?_
  filter_upwards [ae_Ioo] with t ht
  exact hU (h t ht)

/-- `U_u(v) = -(u - v)⁺` -/
theorem hinge_props (u : ℝ) :
    Monotone (fun v : ℝ => -(max (u - v) 0)) ∧
    ConcaveOn ℝ Set.univ (fun v : ℝ => -(max (u - v) 0)) := by
  constructor
  · intro a b hab
    simp only [neg_le_neg_iff]
    exact max_le_max (by linarith) le_rfl
  · have hc : ConvexOn ℝ Set.univ (fun v : ℝ => max (u - v) 0) := by
      have h1 : ConvexOn ℝ Set.univ (fun v : ℝ => u - v) :=
        (convexOn_const u convex_univ).sub (concaveOn_id convex_univ)
      exact h1.sup (convexOn_const 0 convex_univ)
    exact hc.neg

theorem hinge_int (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Integrable (fun v : ℝ => v) μ)
    (u : ℝ) : Integrable (fun v : ℝ => -(max (u - v) 0)) μ := by
  have : Integrable (fun v : ℝ => max (u - v) 0) μ :=
    ((integrable_const u).sub h).sup (integrable_const 0)
  exact this.neg

/-- SSD ⇒ IDF order -/
theorem idf_of_ssd (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h1 : Integrable (fun v : ℝ => v) μ₁) (h2 : Integrable (fun v : ℝ => v) μ₂)
    (hs : SSD μ₁ μ₂) (u : ℝ) :
    integratedDistributionFunction μ₂ u ≤ integratedDistributionFunction μ₁ u := by
  have := hs _ (hinge_props u).1 (hinge_props u).2 (hinge_int μ₁ h1 u) (hinge_int μ₂ h2 u)
  rw [integral_neg, integral_neg] at this
  unfold integratedDistributionFunction
  rw [g79t_idf, g79t_idf]
  linarith

theorem iqf_of_idf (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h1 : Integrable (fun v : ℝ => v) μ₁) (h2 : Integrable (fun v : ℝ => v) μ₂)
    (h : ∀ u, integratedDistributionFunction μ₂ u ≤ integratedDistributionFunction μ₁ u) :
    ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      integratedQuantileFunction μ₁ p ≤ integratedQuantileFunction μ₂ p := by
  intro p hp
  have L1 := (g97_conj μ₁ h1).2 p hp
  have L2 := (g97_conj μ₂ h2).2 p hp
  refine L1.2 ?_
  rintro x ⟨u, rfl⟩
  have := L2.1 ⟨u, rfl⟩
  have := h u
  linarith

theorem idf_of_iqf (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h1 : Integrable (fun v : ℝ => v) μ₁) (h2 : Integrable (fun v : ℝ => v) μ₂)
    (h : ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      integratedQuantileFunction μ₁ p ≤ integratedQuantileFunction μ₂ p) :
    ∀ u, integratedDistributionFunction μ₂ u ≤ integratedDistributionFunction μ₁ u := by
  intro u
  have L1 := (g97_conj μ₁ h1).1 u
  have L2 := (g97_conj μ₂ h2).1 u
  refine L2.2 ?_
  rintro x ⟨p, hp, rfl⟩
  have := L1.1 ⟨p, hp, rfl⟩
  have := h p hp
  linarith

/-- the comparison lemma: IQF order + (monotone U or equal means) ⇒ ∫U dμ₁ ≤ ∫U dμ₂ -/
theorem cmp (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h1 : Integrable (fun v : ℝ => v) μ₁) (h2 : Integrable (fun v : ℝ => v) μ₂)
    (U : ℝ → ℝ) (hU : ConcaveOn ℝ Set.univ U) (hU1 : Integrable U μ₁) (hU2 : Integrable U μ₂)
    (hD : ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      integratedQuantileFunction μ₁ p ≤ integratedQuantileFunction μ₂ p)
    (hcase : Monotone U ∨ ∫ v, v ∂μ₁ = ∫ v, v ∂μ₂) :
    ∫ v, U v ∂μ₁ ≤ ∫ v, U v ∂μ₂ := by
  obtain ⟨s, hs_anti, hs_sg, hs_nn⟩ := superg U hU
  have hUm : Measurable U := (cont_of_concave hU).measurable
  set q₁ := g79q_q μ₁ with hq₁
  set q₂ := g79q_q μ₂ with hq₂
  obtain ⟨iU1, eU1⟩ := E_Ioc μ₁ U hUm hU1
  obtain ⟨iU2, eU2⟩ := E_Ioc μ₂ U hUm hU2
  obtain ⟨iq1, eq1⟩ := E_Ioc μ₁ (fun v => v) measurable_id h1
  obtain ⟨iq2, eq2⟩ := E_Ioc μ₂ (fun v => v) measurable_id h2
  set g : ℝ → ℝ := fun t => s (q₂ t) with hg
  set h : ℝ → ℝ := fun t => q₂ t - q₁ t with hh
  have hgm : Measurable g := hs_anti.measurable.comp (g79q_meas μ₂)
  have hhm : Measurable h := (g79q_meas μ₂).sub (g79q_meas μ₁)
  have hgA : AntitoneOn g (Set.Ioo 0 1) := by
    intro a ha b hb hab
    exact hs_anti (g79c_mono μ₂ ha.1 hab hb.2)
  have hhi : IntegrableOn h (Set.Ioc 0 1) := iq2.sub iq1
  have hDh : ∀ a ∈ Set.Ioo (0:ℝ) 1, 0 ≤ ∫ t in Set.Ioc 0 a, h t := by
    intro a ha
    have hsub : Set.Ioc 0 a ⊆ Set.Ioc (0:ℝ) 1 := Set.Ioc_subset_Ioc_right ha.2.le
    rw [integral_sub (iq2.mono_set hsub) (iq1.mono_set hsub)]
    have := hD a ha
    unfold integratedQuantileFunction at this
    rw [qeq, qeq] at this
    linarith
  have hcase' : (∀ t ∈ Set.Ioo (0:ℝ) 1, 0 ≤ g t) ∨ ∫ t in Set.Ioc 0 1, h t = 0 := by
    rcases hcase with hm | he
    · exact Or.inl fun t _ => hs_nn hm _
    · right
      rw [integral_sub iq2 iq1]
      have e1 : ∫ v, v ∂μ₁ = ∫ t in Set.Ioc 0 1, q₁ t := eq1
      have e2 : ∫ v, v ∂μ₂ = ∫ t in Set.Ioc 0 1, q₂ t := eq2
      linarith
  have hpt : ∀ t, g t * h t ≤ U (q₂ t) - U (q₁ t) := by
    intro t
    have := hs_sg (q₂ t) (q₁ t)
    simp only [hg, hh]
    nlinarith
  have hpos : IntegrableOn (fun t => max (g t * h t) 0) (Set.Ioc 0 1) := by
    refine Integrable.mono' ((iU2.norm).add (iU1.norm)) ((hgm.mul hhm).max measurable_const).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun t => ?_
    have := hpt t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    simp only [Pi.add_apply, Real.norm_eq_abs]
    refine max_le ?_ (by positivity)
    have := abs_le.1 (le_refl |U (q₂ t)|)
    have := neg_abs_le (U (q₁ t))
    linarith
  obtain ⟨igh, hge⟩ := abel g h hgm hgA hhi hDh hcase' hpos
  rw [eU1, eU2]
  have hle : ∫ t in Set.Ioc 0 1, g t * h t ≤ ∫ t in Set.Ioc 0 1, (U (q₂ t) - U (q₁ t)) :=
    setIntegral_mono_on igh (iU2.sub iU1) measurableSet_Ioc fun t _ => hpt t
  rw [integral_sub iU2 iU1] at hle
  linarith

theorem ssd_of_iqf (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h1 : Integrable (fun v : ℝ => v) μ₁) (h2 : Integrable (fun v : ℝ => v) μ₂)
    (hD : ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      integratedQuantileFunction μ₁ p ≤ integratedQuantileFunction μ₂ p) : SSD μ₁ μ₂ :=
  fun U hm hU hU1 hU2 => cmp μ₁ μ₂ h1 h2 U hU hU1 hU2 hD (Or.inl hm)

end SD97

open SD97 in
theorem solution (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    (FSD μ₁ μ₂ ↔ ∀ u : ℝ, distributionFunction μ₂ u ≤ distributionFunction μ₁ u) ∧
    (FSD μ₁ μ₂ ↔ ∀ p ∈ Set.Ioo (0 : ℝ) 1, quantileFunction μ₁ p ≤ quantileFunction μ₂ p) ∧
    (Integrable (fun v : ℝ => v) μ₁ → Integrable (fun v : ℝ => v) μ₂ →
      (CCD μ₁ μ₂ ↔ SSD μ₁ μ₂ ∧ ∫ v, v ∂μ₁ = ∫ v, v ∂μ₂)) ∧
    (Integrable (fun v : ℝ => v) μ₁ → Integrable (fun v : ℝ => v) μ₂ →
      (CCD μ₁ μ₂ ↔ ∃ K : Kernel ℝ ℝ, IsMarkovKernel K ∧
        (∀ u : ℝ, distributionFunction μ₁ u = ∫ v, distributionFunction (K v) u ∂μ₂) ∧
        (∀ v : ℝ, Integrable (fun u : ℝ => u) (K v) ∧ ∫ u, u ∂(K v) = v))) ∧
    (Integrable (fun v : ℝ => v) μ₁ → Integrable (fun v : ℝ => v) μ₂ →
      (SSD μ₁ μ₂ ↔ ∀ u : ℝ,
        integratedDistributionFunction μ₂ u ≤ integratedDistributionFunction μ₁ u)) ∧
    (Integrable (fun v : ℝ => v) μ₁ → Integrable (fun v : ℝ => v) μ₂ →
      (SSD μ₁ μ₂ ↔ ∀ p ∈ Set.Ioo (0 : ℝ) 1,
        integratedQuantileFunction μ₁ p ≤ integratedQuantileFunction μ₂ p)) := by
  have hFq := cdf_iff_q μ₁ μ₂
  have hFSD1 : FSD μ₁ μ₂ ↔ ∀ u : ℝ, distributionFunction μ₂ u ≤ distributionFunction μ₁ u :=
    ⟨fun h u => g79q_fsd_cdf μ₁ μ₂ h u, fun h => fsd_of_q μ₁ μ₂ (hFq.1 h)⟩
  refine ⟨hFSD1, hFSD1.trans hFq, ?_, ?_, ?_, ?_⟩
  · intro h1 h2
    constructor
    · intro hc
      refine ⟨fun U _ hU hU1 hU2 => hc U hU hU1 hU2, le_antisymm ?_ ?_⟩
      · exact hc _ (concaveOn_id convex_univ) h1 h2
      · have := hc (fun v => -v) (convexOn_id convex_univ).neg h1.neg h2.neg
        rw [integral_neg, integral_neg] at this
        linarith
    · rintro ⟨hs, he⟩ U hU hU1 hU2
      exact cmp μ₁ μ₂ h1 h2 U hU hU1 hU2
        (iqf_of_idf μ₁ μ₂ h1 h2 (idf_of_ssd μ₁ μ₂ h1 h2 hs)) (Or.inr he)
  · intro h1 h2
    exact ⟨kernel_of_ccd μ₁ μ₂ h1 h2, ccd_of_kernel μ₁ μ₂ h1 h2⟩
  · intro h1 h2
    exact ⟨idf_of_ssd μ₁ μ₂ h1 h2, fun h => ssd_of_iqf μ₁ μ₂ h1 h2 (iqf_of_idf μ₁ μ₂ h1 h2 h)⟩
  · intro h1 h2
    exact ⟨fun h => iqf_of_idf μ₁ μ₂ h1 h2 (idf_of_ssd μ₁ μ₂ h1 h2 h), ssd_of_iqf μ₁ μ₂ h1 h2⟩
