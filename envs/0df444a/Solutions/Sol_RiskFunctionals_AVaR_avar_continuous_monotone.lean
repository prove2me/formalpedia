-- Prove2me | solution 1 for RiskFunctionals.AVaR.avar_continuous_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:20:37.627637+00:00
-- url     : https://prove2.me/submissions/36dfde33-da80-423f-92d2-a106e8f7740e

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk
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

open Filter Topology

theorem g79c_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hv : v < 1) : g79q_q μ u ≤ g79q_q μ v := by
  rw [g79q_qle' μ hu (lt_of_le_of_lt huv hv)]
  exact huv.trans ((g79q_qle' μ (lt_of_lt_of_le hu huv) hv _).1 le_rfl)

open RiskFunctionals.AVaR in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P)
    (hnc : ¬ ∃ c : ℝ, Y =ᵐ[P] fun _ => c) :
    ContinuousOn (fun α : ℝ => averageValueAtRisk P Y α) (Set.Ioc 0 1) ∧
    MonotoneOn (fun α : ℝ => averageValueAtRisk P Y α) (Set.Ioc 0 1) ∧
    Tendsto (fun α : ℝ => ((averageValueAtRisk P Y α : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 (essInf (fun ω => ((Y ω : ℝ) : EReal)) P)) := by
  set μ := P.map Y with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hY.aemeasurable
  set q := g79q_q μ with hqdef
  have hA : ∀ α, 0 < α → averageValueAtRisk P Y α = 1 / α * ∫ u in (0:ℝ)..α, q u := by
    intro α h
    unfold averageValueAtRisk
    rw [intervalIntegral.integral_of_le h.le]; rfl
  have hP : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have htr' : (volume.restrict (Set.Icc (0 : ℝ) 1)).map q = μ :=
    g79q_transform μ (volume.restrict (Set.Icc (0 : ℝ) 1)) id measurable_id Measure.map_id
  have hmeas : Measurable q := g79q_meas μ
  have hint_id : Integrable (fun x : ℝ => x) μ :=
    (integrable_map_measure aestronglyMeasurable_id hY.aemeasurable).2 hYi
  have hqI : IntegrableOn q (Set.Icc 0 1) := by
    rw [← htr'] at hint_id
    exact (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).1 hint_id
  have hII : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable q volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hqI.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc ha hb))
  -- I α ≤ α q α  for α ∈ (0,1)
  have hIle : ∀ α, 0 < α → α < 1 → ∫ u in (0:ℝ)..α, q u ≤ α * q α := by
    intro α h0 h1
    rw [intervalIntegral.integral_of_le h0.le]
    have := setIntegral_mono_on (hqI.mono_set (Set.Ioc_subset_Icc_self.trans
      (Set.Icc_subset_Icc le_rfl h1.le))) (integrableOn_const (by simp)) measurableSet_Ioc
      (fun u hu => g79c_mono μ hu.1 hu.2 h1)
    simpa [setIntegral_const, h0.le] using this
  -- J ≥ (β - α) q α
  have hJge : ∀ α β, 0 < α → α < 1 → α ≤ β → β ≤ 1 →
      (β - α) * q α ≤ ∫ u in α..β, q u := by
    intro α β h0 h1 hab hb
    rw [intervalIntegral.integral_of_le hab, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
    have := setIntegral_mono_on (integrableOn_const (by simp))
      (hqI.mono_set (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc h0.le hb)))
      measurableSet_Ioo (fun u hu => g79c_mono μ h0 hu.1.le (lt_of_lt_of_le hu.2 hb))
    simpa [setIntegral_const, hab] using this
  refine ⟨?_, ?_, ?_⟩
  · -- continuity
    have hc : ContinuousOn (fun x => ∫ t in (0:ℝ)..x, q t) (Set.uIcc 0 1) :=
      intervalIntegral.continuousOn_primitive_interval (by
        rw [Set.uIcc_of_le zero_le_one]; exact hqI)
    rw [Set.uIcc_of_le zero_le_one] at hc
    have hc' := hc.mono Set.Ioc_subset_Icc_self
    have hinv : ContinuousOn (fun α : ℝ => 1 / α) (Set.Ioc 0 1) :=
      continuousOn_const.div continuousOn_id (fun x hx => hx.1.ne')
    exact (hinv.mul hc').congr (fun α hα => hA α hα.1)
  · -- monotone
    intro α hα β hβ hab
    simp only [hA α hα.1, hA β hβ.1]
    rcases eq_or_lt_of_le hα.2 with h1 | h1
    · have : β = 1 := le_antisymm hβ.2 (h1 ▸ hab)
      rw [h1, this]
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hII 0 α le_rfl hα.1.le h1.le) (hII α β hα.1.le hab hβ.2)
      rw [← hsplit]
      have e1 := hIle α hα.1 h1
      have e2 := hJge α β hα.1 h1 hab hβ.2
      set I := ∫ u in (0:ℝ)..α, q u
      set J := ∫ u in α..β, q u
      have ha := hα.1
      have hb : 0 < β := lt_of_lt_of_le ha hab
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul, div_le_div_iff₀ ha hb]
      nlinarith [mul_le_mul_of_nonneg_left e2 ha.le, mul_le_mul_of_nonneg_left e1 (sub_nonneg.mpr hab)]
  · -- limit
    set m : EReal := ⨅ u ∈ Set.Ioo (0:ℝ) 1, ((q u : ℝ) : EReal) with hm
    have hmq : ∀ u ∈ Set.Ioo (0:ℝ) 1, m ≤ (q u : EReal) := fun u hu => iInf₂_le u hu
    have hmtop : m ≠ ⊤ := by
      intro h; have := hmq (1/2) ⟨by norm_num, by norm_num⟩; rw [h] at this; simp at this
    have hmc : m = ⊥ ∨ ∃ c : ℝ, m = c ∧ ∀ u ∈ Set.Ioo (0:ℝ) 1, c ≤ q u := by
      by_cases hb : m = ⊥
      · exact Or.inl hb
      · refine Or.inr ⟨m.toReal, (EReal.coe_toReal hmtop hb).symm, fun u hu => ?_⟩
        have := hmq u hu
        rw [← EReal.coe_toReal hmtop hb] at this
        exact_mod_cast this
    have hS := essInf_eq_sSup P (fun ω => ((Y ω : ℝ) : EReal))
    have hme : m = essInf (fun ω => ((Y ω : ℝ) : EReal)) P := by
      apply le_antisymm
      · rw [hS]
        apply le_sSup
        show P {ω | ((Y ω : ℝ) : EReal) < m} = 0
        rcases hmc with hb | ⟨c, hmc, hc⟩
        · rw [hb]; simp
        · rw [hmc]
          have hF : μ.real (Set.Iio c) ≤ 0 := by
            apply g79q_Iio_le
            intro y hy
            by_contra hpos
            push Not at hpos
            set u := min (g79q_F μ y) (1/2)
            have hu0 : 0 < u := lt_min hpos (by norm_num)
            have hu1 : u < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
            have := (g79q_qle' μ hu0 hu1 y).2 (min_le_left _ _)
            have := hc u ⟨hu0, hu1⟩
            linarith
          have hz : μ (Set.Iio c) = 0 := by
            rw [← measureReal_eq_zero_iff]; exact le_antisymm hF measureReal_nonneg
          rw [hμ, Measure.map_apply hY measurableSet_Iio] at hz
          refine measure_mono_null (fun ω hω => ?_) hz
          have hω' : ((Y ω : ℝ) : EReal) < (c : EReal) := hω
          exact EReal.coe_lt_coe_iff.mp hω'
      · refine le_iInf₂ fun u hu => ?_
        rw [hS]
        refine sSup_le fun a ha => ?_
        have ha' : P {ω | ((Y ω : ℝ) : EReal) < a} = 0 := ha
        by_contra hlt
        push Not at hlt
        have hle := (g79q_qle' μ hu.1 hu.2 (q u)).1 le_rfl
        have hz : P (Y ⁻¹' Set.Iic (q u)) = 0 := by
          refine measure_mono_null (fun ω hω => ?_) ha'
          have hω' : Y ω ≤ q u := hω
          show ((Y ω : ℝ) : EReal) < a
          exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hω') hlt
        have : g79q_F μ (q u) = 0 := by
          unfold g79q_F; rw [hμ, measureReal_def, Measure.map_apply hY measurableSet_Iic, hz]; simp
        linarith [hu.1]
    rw [← hme]
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [Ioo_mem_nhdsGT (one_pos : (0:ℝ) < 1)] with α hα
      refine lt_of_lt_of_le ha ?_
      rcases hmc with hb | ⟨c, hmc, hc⟩
      · rw [hb] at ha; exact (not_lt_bot ha).elim
      · rw [hmc, EReal.coe_le_coe_iff, hA α hα.1, intervalIntegral.integral_of_le hα.1.le]
        have := setIntegral_mono_on (integrableOn_const (by simp)) (hqI.mono_set
          (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hα.2.le))) measurableSet_Ioc
          (fun u hu => hc u ⟨hu.1, lt_of_le_of_lt hu.2 hα.2⟩)
        simp only [setIntegral_const, Real.volume_real_Ioc, sub_zero, max_eq_left hα.1.le,
          smul_eq_mul] at this
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hα.1]; linarith
    · intro b hb
      obtain ⟨u, hu, hub⟩ : ∃ u ∈ Set.Ioo (0:ℝ) 1, ((q u : ℝ) : EReal) < b := by
        rw [hm] at hb
        simpa [iInf_lt_iff] using hb
      filter_upwards [Ioo_mem_nhdsGT hu.1] with α hα
      refine lt_of_le_of_lt ?_ hub
      rw [EReal.coe_le_coe_iff, hA α hα.1]
      have h1 : α < 1 := hα.2.trans hu.2
      have := hIle α hα.1 h1
      have hmq' := g79c_mono μ hα.1 hα.2.le hu.2
      have h3 := mul_le_mul_of_nonneg_left hmq' hα.1.le
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hα.1]; linarith
