-- Prove2me | solution 1 for RiskFunctionals.Deviation.minimal_loss_dual_representation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:36:34.906827+00:00
-- url     : https://prove2.me/submissions/ad74726a-44e6-4429-bf4f-0ce8be6f2272

import Mathlib
import Definitions.Def_RiskFunctionals_Deviation_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Deviation_MinimalLoss
import Theorems.Thm_RiskFunctionals_Deviation_integral_conjugate_duality

/-! Quantile machinery (distribution function, quantile function, quantile transform and the
Rockafellar–Uryasev identity), adapted from the accepted platform proof of
`RiskFunctionals.AVaR.avar_properties`. -/

namespace MLDualA

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


open RiskFunctionals.Deviation

theorem lawI {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (hYi : Integrable Y P) : Integrable (fun v : ℝ => v) (P.map Y) :=
  (integrable_map_measure aestronglyMeasurable_id hY.aemeasurable).2 hYi

theorem E_Ioc (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable g μ) :
    IntegrableOn (fun u => g (g79q_q μ u)) (Set.Ioc 0 1) ∧
    ∫ y, g y ∂μ = ∫ u in Set.Ioc 0 1, g (g79q_q μ u) := by
  obtain ⟨h1, h2⟩ := g79n_E μ g hg hgi
  exact ⟨h1.mono_set Set.Ioc_subset_Icc_self, by
    rw [h2, intervalIntegral.integral_of_le zero_le_one]⟩

theorem avar_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) (α : ℝ) :
    averageValueAtRisk P Y α = (1 / α) * ∫ u in Set.Ioc 0 α, g79q_q (P.map Y) u := rfl

theorem avar_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P) :
    averageValueAtRisk P Y 1 = ∫ ω, Y ω ∂P := by
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  rw [avar_eq, ← (E_Ioc (P.map Y) (fun v => v) measurable_id (lawI P Y hY hYi)).2,
    integral_map (f := fun y : ℝ => y) hY.aemeasurable aestronglyMeasurable_id]
  simp only [div_one, one_mul]

theorem F_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (u : ℝ) : g79q_F (P.map Y) u = P.real {ω | Y ω ≤ u} := by
  unfold g79q_F
  rw [map_measureReal_apply hY measurableSet_Iic]; rfl

/-- Rockafellar–Uryasev on `Ω`, `0 < α < 1`, with the maximiser `q = G⁻¹(α)` -/
theorem ru {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (∀ x : ℝ, α * x - ∫ ω, max (x - Y ω) 0 ∂P ≤ α * averageValueAtRisk P Y α) ∧
    α * g79q_q (P.map Y) α - ∫ ω, max (g79q_q (P.map Y) α - Y ω) 0 ∂P =
        α * averageValueAtRisk P Y α := by
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  obtain ⟨hA, hB⟩ := g79n_RU (P.map Y) (lawI P Y hY hYi) h0 h1
  have hE : ∀ x : ℝ, ∫ y, max (x - y) 0 ∂(P.map Y) = ∫ ω, max (x - Y ω) 0 ∂P := fun x =>
    integral_map hY.aemeasurable (by fun_prop)
  have hav : α * averageValueAtRisk P Y α = ∫ u in (0:ℝ)..α, g79q_q (P.map Y) u := by
    rw [avar_eq, intervalIntegral.integral_of_le h0.le]
    field_simp
  rw [hav]
  refine ⟨fun x => ?_, ?_⟩
  · rw [← hE]; exact hA x
  · rw [← hE]; exact hB


/-! ### Part (iv): `𝔸𝕍@ℝ_α(Y) = min {𝔼(YZ) : 𝔼Z = 1, 0 ≤ Z ≤ 1/α}` -/

theorem part_iv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)]
    [p.HolderConjugate q] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (Y : Ω → ℝ)
    (hYm : Measurable Y) (hYp : MemLp Y p P) :
    IsLeast {v : ℝ | ∃ Z : Ω → ℝ, Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
          (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ 1 / α) ∧ v = ∫ ω, Y ω * Z ω ∂P}
        (averageValueAtRisk P Y α) := by
  have hYint : Integrable Y P := hYp.integrable Fact.out
  have hZi : ∀ Z : Ω → ℝ, MemLp Z q P → Integrable Z P := by
    intro Z hZ
    have := (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1:ℝ)) p P).integrable_mul hZ
    exact this.congr (ae_of_all _ fun ω => by simp)
  rcases hα1.lt_or_eq with hlt | rfl
  · obtain ⟨hA, hB⟩ := ru P Y hYm hYint hα0 hlt
    set qq := g79q_q (P.map Y) α with hqq
    constructor
    · -- attainment
      have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
      set A := P.real {ω | Y ω < qq} with hAdef
      set B := P.real {ω | Y ω ≤ qq} with hBdef
      set E := P.real {ω | Y ω = qq} with hEdef
      have hmA : MeasurableSet {ω | Y ω < qq} := measurableSet_lt hYm measurable_const
      have hmE : MeasurableSet {ω | Y ω = qq} := measurableSet_eq_fun hYm measurable_const
      have hαB : α ≤ B := by
        have := (g79q_qle' (P.map Y) hα0 hlt qq).1 le_rfl
        rwa [F_map P Y hYm] at this
      have hAα : A ≤ α := by
        have := g79q_Iio_le (P.map Y) qq α (fun y hy => by
          by_contra hc
          have := (g79q_qle' (P.map Y) hα0 hlt y).2 (le_of_lt (lt_of_not_ge hc))
          linarith)
        rwa [map_measureReal_apply hYm measurableSet_Iio] at this
      have hBAE : B = A + E := by
        have hu : {ω | Y ω ≤ qq} = {ω | Y ω < qq} ∪ {ω | Y ω = qq} := by
          ext ω; simp [le_iff_lt_or_eq]
        have hd : Disjoint {ω | Y ω < qq} {ω | Y ω = qq} := by
          rw [Set.disjoint_left]; intro ω h1 h2
          simp only [Set.mem_setOf_eq] at h1 h2; linarith
        rw [hBdef, hu, measureReal_union hd hmE]
      have hE0 : 0 ≤ E := measureReal_nonneg
      set c := (α - A) / E with hcdef
      have hc0 : 0 ≤ c := div_nonneg (by linarith) hE0
      have hc1 : c ≤ 1 := by
        rcases hE0.lt_or_eq with hE | hE
        · rw [hcdef, div_le_one hE]; linarith
        · rw [hcdef, ← hE, div_zero]; norm_num
      have hcE : A + c * E = α := by
        rcases hE0.lt_or_eq with hE | hE
        · rw [hcdef, div_mul_cancel₀ _ hE.ne']; ring
        · rw [← hE, mul_zero, add_zero]; rw [← hE] at hBAE; linarith
      set Z : Ω → ℝ := fun ω => (1 / α) * Set.indicator {ω | Y ω < qq} (fun _ => (1:ℝ)) ω +
        (c / α) * Set.indicator {ω | Y ω = qq} (fun _ => (1:ℝ)) ω with hZdef
      have hZcase : ∀ ω, (Y ω < qq ∧ Z ω = 1 / α) ∨ (Y ω = qq ∧ Z ω = c / α) ∨
          (qq < Y ω ∧ Z ω = 0) := by
        intro ω
        rcases lt_trichotomy (Y ω) qq with h | h | h
        · left; refine ⟨h, ?_⟩
          simp [hZdef, Set.indicator, h, h.ne]
        · right; left; refine ⟨h, ?_⟩
          simp [hZdef, Set.indicator, h]
        · right; right; refine ⟨h, ?_⟩
          simp [hZdef, Set.indicator, not_lt.2 h.le, h.ne']
      have hZm : Measurable Z :=
        (measurable_const.mul (measurable_const.indicator hmA)).add
          (measurable_const.mul (measurable_const.indicator hmE))
      have hZb : ∀ ω, 0 ≤ Z ω ∧ Z ω ≤ 1 / α := by
        intro ω
        have h1α : 0 < 1 / α := by positivity
        rcases hZcase ω with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
        · exact ⟨h1α.le, le_rfl⟩
        · refine ⟨div_nonneg hc0 hα0.le, div_le_div_of_nonneg_right hc1 hα0.le⟩
        · exact ⟨le_rfl, h1α.le⟩
      have hZl : MemLp Z q P := by
        refine MemLp.of_bound hZm.aestronglyMeasurable (1 / α) (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hZb ω).1]; exact (hZb ω).2
      have hZint : ∫ ω, Z ω ∂P = 1 := by
        rw [hZdef, integral_add ((integrable_const (1:ℝ)).indicator hmA |>.const_mul _)
          ((integrable_const (1:ℝ)).indicator hmE |>.const_mul _),
          integral_const_mul, integral_const_mul, integral_indicator hmA, integral_indicator hmE,
          setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
        rw [← hAdef, ← hEdef]
        field_simp
        linarith
      refine ⟨Z, hZm, hZl, hZint, ae_of_all _ hZb, ?_⟩
      -- pointwise identity `α Y Z = α q Z - (q - Y)⁺`
      have hpt : ∀ ω, α * (Y ω * Z ω) = α * qq * Z ω - max (qq - Y ω) 0 := by
        intro ω
        rcases hZcase ω with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h']
        · rw [max_eq_left (by linarith)]; field_simp; ring
        · rw [h, sub_self, max_self]; ring
        · rw [max_eq_right (by linarith)]; ring
      have hhinge : Integrable (fun ω => max (qq - Y ω) 0) P :=
        ((integrable_const qq).sub hYint).pos_part
      have : α * ∫ ω, Y ω * Z ω ∂P = α * averageValueAtRisk P Y α := by
        rw [← integral_const_mul, ← hB]
        simp_rw [hpt]
        rw [integral_sub ((hZi Z hZl).const_mul _) hhinge, integral_const_mul, hZint, mul_one]
      exact (mul_left_cancel₀ hα0.ne' this).symm
    · -- lower bound
      rintro v ⟨Z, hZm, hZl, hZ1, hZb, rfl⟩
      have hhinge : Integrable (fun ω => max (qq - Y ω) 0) P :=
        ((integrable_const qq).sub hYint).pos_part
      have hpt : ∀ᵐ ω ∂P, α * qq * Z ω - max (qq - Y ω) 0 ≤ α * (Y ω * Z ω) := by
        filter_upwards [hZb] with ω ⟨h0, h1⟩
        have hαZ : α * Z ω ≤ 1 := by
          have := mul_le_mul_of_nonneg_left h1 hα0.le
          rwa [mul_one_div_cancel hα0.ne'] at this
        rcases le_total (Y ω) qq with h | h
        · rw [max_eq_left (by linarith)]
          nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hαZ)]
        · rw [max_eq_right (by linarith)]
          nlinarith [mul_nonneg (mul_nonneg hα0.le h0) (sub_nonneg.2 h)]
      have i1 : Integrable (fun ω => α * qq * Z ω - max (qq - Y ω) 0) P :=
        ((hZi Z hZl).const_mul (α * qq)).sub hhinge
      have hYZ : Integrable (fun ω => Y ω * Z ω) P := hYp.integrable_mul hZl
      have i2 : Integrable (fun ω => α * (Y ω * Z ω)) P := hYZ.const_mul α
      have hint := integral_mono_ae i1 i2 hpt
      rw [integral_sub ((hZi Z hZl).const_mul _) hhinge, integral_const_mul, hZ1, mul_one,
        integral_const_mul, hB] at hint
      exact le_of_mul_le_mul_left hint hα0
  · -- `α = 1`
    constructor
    · refine ⟨fun _ => 1, measurable_const, memLp_const 1, by simp,
        ae_of_all _ fun _ => by norm_num, ?_⟩
      rw [avar_one P Y hYm hYint]; simp
    · rintro v ⟨Z, hZm, hZl, hZ1, hZb, rfl⟩
      have hnn : 0 ≤ᵐ[P] fun ω => 1 - Z ω := by
        filter_upwards [hZb] with ω h; simp only [Pi.zero_apply]; linarith [h.2, (div_one (1:ℝ))]
      have hi : Integrable (fun ω => 1 - Z ω) P := (integrable_const 1).sub (hZi Z hZl)
      have h0 : ∫ ω, 1 - Z ω ∂P = 0 := by
        rw [integral_sub (integrable_const 1) (hZi Z hZl), hZ1]; simp
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h0
      rw [avar_one P Y hYm hYint]
      refine le_of_eq (integral_congr_ae ?_)
      filter_upwards [hae] with ω hω
      simp only [Pi.zero_apply] at hω
      have : Z ω = 1 := by linarith
      rw [this, mul_one]

/-! ### Part (ii): `𝔸𝕍@ℝ𝔻_α(Y) = sup {𝔼(YZ) : -(1-α)/α ≤ Z ≤ 1, 𝔼Z = 0}` -/

theorem part_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)]
    [p.HolderConjugate q] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (Y : Ω → ℝ)
    (hYm : Measurable Y) (hYp : MemLp Y p P) :
    ((avarDeviation P Y α : ℝ) : EReal) =
        ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧
            (∀ᵐ ω ∂P, -((1 - α) / α) ≤ Z ω ∧ Z ω ≤ 1) ∧ ∫ ω, Z ω ∂P = 0},
          ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal) := by
  have hYint : Integrable Y P := hYp.integrable Fact.out
  have hZi : ∀ Z : Ω → ℝ, MemLp Z q P → Integrable Z P := by
    intro Z hZ
    have := (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1:ℝ)) p P).integrable_mul hZ
    exact this.congr (ae_of_all _ fun ω => by simp)
  have hsub : ∀ Z : Ω → ℝ, MemLp Z q P →
      ∫ ω, Y ω * (1 - Z ω) ∂P = ∫ ω, Y ω ∂P - ∫ ω, Y ω * Z ω ∂P := by
    intro Z hZ
    have e : (fun ω => Y ω * (1 - Z ω)) = fun ω => Y ω - Y ω * Z ω := by funext ω; ring
    have hYZ : Integrable (fun ω => Y ω * Z ω) P := hYp.integrable_mul hZ
    rw [e, integral_sub hYint hYZ]
  have hkey : -((1 - α) / α) = 1 - 1 / α := by field_simp; ring
  obtain ⟨⟨Z, hZm, hZl, hZ1, hZb, hZv⟩, hlow⟩ :=
    part_iv P p q α hα0 hα1 Y hYm hYp
  have hdev : avarDeviation P Y α = ∫ ω, Y ω ∂P - averageValueAtRisk P Y α := rfl
  apply le_antisymm
  · refine le_iSup₂_of_le (f := fun W (_ : W ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧
            (∀ᵐ ω ∂P, -((1 - α) / α) ≤ Z ω ∧ Z ω ≤ 1) ∧ ∫ ω, Z ω ∂P = 0}) =>
          ((∫ ω, Y ω * W ω ∂P : ℝ) : EReal)) (fun ω => 1 - Z ω) ⟨measurable_const.sub hZm,
        (memLp_const 1).sub hZl, ?_, ?_⟩ ?_
    · filter_upwards [hZb] with ω h
      rw [hkey]; constructor <;> linarith [h.1, h.2]
    · rw [integral_sub (integrable_const 1) (hZi Z hZl), hZ1]; simp
    · rw [hsub Z hZl, hdev, hZv]
  · refine iSup₂_le fun W hW => ?_
    obtain ⟨hWm, hWl, hWb, hW0⟩ := hW
    have hmem : ∫ ω, Y ω * (1 - W ω) ∂P ∈ {v : ℝ | ∃ Z : Ω → ℝ, Measurable Z ∧ MemLp Z q P ∧
        ∫ ω, Z ω ∂P = 1 ∧ (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ 1 / α) ∧ v = ∫ ω, Y ω * Z ω ∂P} := by
      refine ⟨fun ω => 1 - W ω, measurable_const.sub hWm, (memLp_const 1).sub hWl, ?_, ?_, rfl⟩
      · rw [integral_sub (integrable_const 1) (hZi W hWl), hW0]; simp
      · filter_upwards [hWb] with ω h
        rw [hkey] at h; constructor <;> linarith [h.1, h.2]
    have := hlow hmem
    rw [hsub W hWl] at this
    rw [hdev]
    exact_mod_cast (by linarith : ∫ ω, Y ω * W ω ∂P ≤ ∫ ω, Y ω ∂P - averageValueAtRisk P Y α)

end MLDualA


open MeasureTheory Filter Topology RiskFunctionals.Deviation

namespace MLDualB

/-! ### Elementary facts on the Fenchel conjugate -/

lemma conj_nonneg (h : ℝ → ℝ) (h0 : h 0 = 0) (v : ℝ) : 0 ≤ fenchelConj h v := by
  refine le_trans ?_ (le_iSup (fun u : ℝ => ((u * v - h u : ℝ) : EReal)) 0)
  simp [h0]

lemma le_conj (h : ℝ → ℝ) (u v : ℝ) : ((u * v - h u : ℝ) : EReal) ≤ fenchelConj h v :=
  le_iSup (fun u : ℝ => ((u * v - h u : ℝ) : EReal)) u

lemma conj_zero (h : ℝ → ℝ) (hnn : ∀ u, 0 ≤ h u) (h0 : h 0 = 0) : fenchelConj h 0 = 0 := by
  apply le_antisymm
  · refine iSup_le fun u => ?_
    have : u * 0 - h u ≤ 0 := by linarith [hnn u]
    exact_mod_cast this
  · exact conj_nonneg h h0 0

lemma conj_measurable (h : ℝ → ℝ) (hc : Continuous h) : Measurable (fenchelConj h) := by
  have : LowerSemicontinuous (fenchelConj h) := by
    have := lowerSemicontinuous_iSup (f := fun (u : ℝ) (v : ℝ) => ((u * v - h u : ℝ) : EReal))
      (fun u => (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous)
    exact this
  exact this.measurable

lemma conj_coe (h : ℝ → ℝ) (h0 : h 0 = 0) {v : ℝ} (hv : fenchelConj h v ≠ ⊤) :
    (((fenchelConj h v).toReal : ℝ) : EReal) = fenchelConj h v :=
  EReal.coe_toReal hv (ne_bot_of_le_ne_bot (by simp) (conj_nonneg h h0 v))

lemma conj_toReal_nonneg (h : ℝ → ℝ) (h0 : h 0 = 0) (v : ℝ) : 0 ≤ (fenchelConj h v).toReal :=
  EReal.toReal_nonneg (conj_nonneg h h0 v)

lemma conj_comb (h : ℝ → ℝ) (h0 : h 0 = 0) {z1 z2 t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h1 : fenchelConj h z1 ≠ ⊤) (h2 : fenchelConj h z2 ≠ ⊤) :
    fenchelConj h (t * z1 + (1 - t) * z2) ≤
      ((t * (fenchelConj h z1).toReal + (1 - t) * (fenchelConj h z2).toReal : ℝ) : EReal) := by
  refine iSup_le fun u => ?_
  have a1 : u * z1 - h u ≤ (fenchelConj h z1).toReal := by
    have := le_conj h u z1
    rw [← conj_coe h h0 h1] at this
    exact_mod_cast this
  have a2 : u * z2 - h u ≤ (fenchelConj h z2).toReal := by
    have := le_conj h u z2
    rw [← conj_coe h h0 h2] at this
    exact_mod_cast this
  have e : u * (t * z1 + (1 - t) * z2) - h u = t * (u * z1 - h u) + (1 - t) * (u * z2 - h u) := by
    ring
  have : u * (t * z1 + (1 - t) * z2) - h u ≤
      t * (fenchelConj h z1).toReal + (1 - t) * (fenchelConj h z2).toReal := by
    rw [e]
    have := mul_le_mul_of_nonneg_left a1 ht0
    have := mul_le_mul_of_nonneg_left a2 (sub_nonneg.2 ht1)
    linarith
  exact_mod_cast this

/-- convexity along rays through `0` -/
lemma conv_scale (h : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ h) (h0 : h 0 = 0) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : ℝ) : h (t * y) ≤ t * h y := by
  have := hconv.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ y) (sub_nonneg.2 ht1) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, h0] at this
  linarith

/-- if `h > 0` somewhere on the negative axis, `h*` is finite at a negative point -/
lemma conj_fin_neg (h : ℝ → ℝ) (hnn : ∀ u, 0 ≤ h u) (hconv : ConvexOn ℝ Set.univ h)
    (h0 : h 0 = 0) {u1 : ℝ} (hu1 : u1 < 0) (hh : 0 < h u1) :
    ∃ v < 0, fenchelConj h v ≠ ⊤ := by
  set c := h u1 / (-u1) with hcdef
  have hpos : 0 < -u1 := by linarith
  have hc0 : 0 < c := div_pos hh hpos
  have hc : c * (-u1) = h u1 := by rw [hcdef, div_mul_cancel₀ _ hpos.ne']
  refine ⟨-c, by linarith, ne_top_of_le_ne_top (EReal.coe_ne_top (h u1)) ?_⟩
  refine iSup_le fun u => ?_
  have : u * (-c) - h u ≤ h u1 := by
    rcases le_or_gt 0 u with hu | hu
    · nlinarith [hnn u]
    · rcases le_or_gt u1 u with hu' | hu'
      · nlinarith [hnn u]
      · -- u < u1 < 0
        have ht0 : 0 ≤ u1 / u := le_of_lt (div_pos_of_neg_of_neg hu1 hu)
        have ht1 : u1 / u ≤ 1 := by rw [div_le_one_of_neg hu]; exact hu'.le
        have hs := conv_scale h hconv h0 ht0 ht1 u
        have e : u1 / u * u = u1 := div_mul_cancel₀ _ hu.ne
        rw [e] at hs
        -- hs : h u1 ≤ u1 / u * h u
        have hs' : h u1 * (-u) ≤ (-u1) * h u := by
          have := mul_le_mul_of_nonneg_right hs (by linarith : (0:ℝ) ≤ -u)
          have e2 : u1 / u * h u * -u = (-u1) * h u := by
            rw [show u1 / u * h u * -u = -(u1 / u * u) * h u by ring, div_mul_cancel₀ _ hu.ne]
          linarith
        -- c * (-u) ≤ h u
        have : c * (-u) ≤ h u := by
          have : c * (-u) * (-u1) ≤ h u * (-u1) := by
            have : c * (-u) * (-u1) = h u1 * (-u) := by rw [← hc]; ring
            linarith
          exact le_of_mul_le_mul_right this hpos
        nlinarith
  exact_mod_cast this

/-- if `h > 0` somewhere on the positive axis, `h*` is finite at a positive point -/
lemma conj_fin_pos (h : ℝ → ℝ) (hnn : ∀ u, 0 ≤ h u) (hconv : ConvexOn ℝ Set.univ h)
    (h0 : h 0 = 0) {u2 : ℝ} (hu2 : 0 < u2) (hh : 0 < h u2) :
    ∃ v > 0, fenchelConj h v ≠ ⊤ := by
  set c := h u2 / u2 with hcdef
  have hc0 : 0 < c := div_pos hh hu2
  have hc : c * u2 = h u2 := by rw [hcdef, div_mul_cancel₀ _ hu2.ne']
  refine ⟨c, hc0, ne_top_of_le_ne_top (EReal.coe_ne_top (h u2)) ?_⟩
  refine iSup_le fun u => ?_
  have : u * c - h u ≤ h u2 := by
    rcases le_or_gt u 0 with hu | hu
    · nlinarith [hnn u]
    · rcases le_or_gt u u2 with hu' | hu'
      · nlinarith [hnn u]
      · -- 0 < u2 < u
        have ht0 : 0 ≤ u2 / u := le_of_lt (div_pos hu2 hu)
        have ht1 : u2 / u ≤ 1 := by rw [div_le_one hu]; exact hu'.le
        have hs := conv_scale h hconv h0 ht0 ht1 u
        have e : u2 / u * u = u2 := div_mul_cancel₀ _ hu.ne'
        rw [e] at hs
        have hs' : h u2 * u ≤ u2 * h u := by
          have := mul_le_mul_of_nonneg_right hs hu.le
          have e2 : u2 / u * h u * u = u2 * h u := by
            rw [show u2 / u * h u * u = (u2 / u * u) * h u by ring, div_mul_cancel₀ _ hu.ne']
          linarith
        have : c * u ≤ h u := by
          have : c * u * u2 ≤ h u * u2 := by
            have : c * u * u2 = h u2 * u := by rw [← hc]; ring
            linarith
          exact le_of_mul_le_mul_right this hu2
        nlinarith
  exact_mod_cast this

/-! ### The abstract supergradient argument -/

lemma supergrad {α : Type*} (F : Set α) (m g : α → ℝ) (s0 : ℝ)
    (hcomb : ∀ z1 ∈ F, ∀ z2 ∈ F, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ w ∈ F, m w = t * m z1 + (1 - t) * m z2 ∧ t * g z1 + (1 - t) * g z2 ≤ g w)
    (hzero : ∀ z ∈ F, m z = 0 → g z ≤ s0)
    (hneg : ∃ z ∈ F, m z < 0) (hpos : ∃ z ∈ F, 0 < m z) :
    ∃ σ : ℝ, ∀ z ∈ F, g z ≤ s0 + σ * m z := by
  have key : ∀ z1 ∈ F, ∀ z2 ∈ F, m z1 < 0 → 0 < m z2 →
      (g z2 - s0) / m z2 ≤ (s0 - g z1) / (-m z1) := by
    intro z1 hz1 z2 hz2 h1 h2
    set m1 := m z1
    set m2 := m z2
    have hd : 0 < m2 - m1 := by linarith
    set t := m2 / (m2 - m1) with htdef
    have ht' : t * (m2 - m1) = m2 := by rw [htdef]; field_simp
    have ht'' : (1 - t) * (m2 - m1) = -m1 := by linarith
    have ht0 : 0 ≤ t := div_nonneg h2.le hd.le
    have ht1 : t ≤ 1 := by rw [htdef, div_le_one hd]; linarith
    obtain ⟨w, hw, hmw, hgw⟩ := hcomb z1 hz1 z2 hz2 t ht0 ht1
    have hmw0 : m w = 0 := by
      rw [hmw]
      have : (t * m1 + (1 - t) * m2) * (m2 - m1) = 0 := by
        linear_combination m1 * ht' + m2 * ht''
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hd.ne'
    have hle := (hgw.trans (hzero w hw hmw0))
    have e : (t * g z1 + (1 - t) * g z2) * (m2 - m1) = m2 * g z1 - m1 * g z2 := by
      linear_combination g z1 * ht' + g z2 * ht''
    have := mul_le_mul_of_nonneg_right hle hd.le
    rw [e] at this
    rw [div_le_div_iff₀ h2 (by linarith)]
    nlinarith
  obtain ⟨z1, hz1, hm1⟩ := hneg
  obtain ⟨z2, hz2, hm2⟩ := hpos
  set T := {r : ℝ | ∃ z ∈ F, 0 < m z ∧ r = (g z - s0) / m z} with hT
  have hbdd : BddAbove T := ⟨(s0 - g z1) / (-m z1), by
    rintro r ⟨z, hz, hm, rfl⟩; exact key z1 hz1 z hz hm1 hm⟩
  have hne : T.Nonempty := ⟨_, z2, hz2, hm2, rfl⟩
  refine ⟨sSup T, fun z hz => ?_⟩
  rcases lt_trichotomy (m z) 0 with hlt | heq | hgt
  · have hs : sSup T ≤ (s0 - g z) / (-m z) := csSup_le hne (by
      rintro r ⟨z', hz', hm', rfl⟩; exact key z hz z' hz' hlt hm')
    have := (le_div_iff₀ (neg_pos.2 hlt)).1 hs
    rw [mul_neg] at this
    linarith
  · rw [heq, mul_zero, add_zero]; exact hzero z hz heq
  · have hs : (g z - s0) / m z ≤ sSup T := le_csSup hbdd ⟨z, hz, hgt, rfl⟩
    have := (div_le_iff₀ hgt).1 hs
    linarith

/-- an extended-real lower bound for a coerced infimum of `ℝ≥0∞` values -/
lemma real_le_coe_iInf {ι : Sort*} (f : ι → ENNReal) (r : ℝ)
    (H : ∀ i, (r : EReal) ≤ ((f i : ENNReal) : EReal)) :
    (r : EReal) ≤ (((⨅ i, f i : ENNReal)) : EReal) := by
  rcases le_or_gt r 0 with hr | hr
  · exact le_trans (by exact_mod_cast hr) (EReal.coe_ennreal_nonneg _)
  · have e : (r : EReal) = ((ENNReal.ofReal r : ENNReal) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hr.le]
    rw [e, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf fun i => ?_
    have := H i
    rw [e, EReal.coe_ennreal_le_coe_ennreal_iff] at this
    exact this

/-- minimal loss vanishes along a dominated sequence of shifts killing `h` -/
lemma ml_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℝ)
    (hnn : ∀ u, 0 ≤ h u) (hc : Continuous h) (Y : Ω → ℝ) (hYm : Measurable Y)
    (hYi : Integrable (fun ω => h (Y ω)) P) (a : ℕ → ℝ)
    (hdom : ∀ n ω, h (Y ω - a n) ≤ h (Y ω))
    (hlim : ∀ ω, ∀ᶠ n in atTop, h (Y ω - a n) = 0) : minimalLoss P h Y = 0 := by
  have ht : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (h (Y ω - a n)) ∂P) atTop
      (𝓝 (∫⁻ _ω, (0 : ENNReal) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun ω => ENNReal.ofReal (h (Y ω)))
      (fun n => ?_) (fun n => ae_of_all _ fun ω => ENNReal.ofReal_le_ofReal (hdom n ω)) ?_
      (ae_of_all _ fun ω => ?_)
    · exact ENNReal.measurable_ofReal.comp (hc.measurable.comp (hYm.sub_const _))
    · exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => hnn (Y ω))).1 hYi.2).ne
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim ω] with n hn
      simp [hn]
  have : minimalLoss P h Y ≤ ∫⁻ _ω, (0 : ENNReal) ∂P :=
    ge_of_tendsto' ht fun n =>
      (iInf_le (fun b => ∫⁻ ω, ENNReal.ofReal (h (Y ω - b)) ∂P) (a n) : minimalLoss P h Y ≤ _)
  simpa using this

/-! ### Part (i) -/

theorem part_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] (h : ℝ → ℝ) (hnn : ∀ u, 0 ≤ h u) (hconv : ConvexOn ℝ Set.univ h)
    (h0 : h 0 = 0) (Y : Ω → ℝ) (hYm : Measurable Y) (hYp : MemLp Y p P)
    (hYi : Integrable (fun ω => h (Y ω)) P) :
    ((minimalLoss P h Y : ENNReal) : EReal) =
      ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 0 ∧
          HasFiniteExpectedConj P h Z},
        ((∫ ω, Y ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal) := by
  have hc : Continuous h := continuousOn_univ.1 (hconv.continuousOn isOpen_univ)
  set F := {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ HasFiniteExpectedConj P h Z} with hF
  set F0 := {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 0 ∧
          HasFiniteExpectedConj P h Z} with hF0
  -- integrability facts
  have hYZ : ∀ Z : Ω → ℝ, MemLp Z q P → Integrable (fun ω => Y ω * Z ω) P :=
    fun Z hZ => hYp.integrable_mul hZ
  have hZi : ∀ Z : Ω → ℝ, MemLp Z q P → Integrable Z P := by
    intro Z hZ
    have := (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1:ℝ)) p P).integrable_mul hZ
    exact this.congr (ae_of_all _ fun ω => by simp)
  have lin : ∀ Z : Ω → ℝ, MemLp Z q P → ∀ a : ℝ,
      ∫ ω, (Y ω - a) * Z ω ∂P = ∫ ω, Y ω * Z ω ∂P - a * ∫ ω, Z ω ∂P := by
    intro Z hZ a
    have e : (fun ω => (Y ω - a) * Z ω) = fun ω => Y ω * Z ω - a * Z ω := by
      funext ω; ring
    rw [e, integral_sub (hYZ Z hZ) ((hZi Z hZ).const_mul a), integral_const_mul]
  -- the conjugate duality (Proposition B.3) for `Y - a`
  have K2 : ∀ a : ℝ, ((∫⁻ ω, ENNReal.ofReal (h (Y ω - a)) ∂P : ENNReal) : EReal) =
      ⨆ Z ∈ F, ((∫ ω, (Y ω - a) * Z ω ∂P - expectedConj P h Z : ℝ) : EReal) := by
    intro a
    obtain ⟨H1, H2⟩ := integral_conjugate_duality P p q hp h hconv hc.lowerSemicontinuous
      (conj_nonneg h h0) (fun ω => Y ω - a) (hYm.sub_const a) (hYp.sub (memLp_const a))
    have hmeas : AEStronglyMeasurable (fun ω => h (Y ω - a)) P :=
      (hc.measurable.comp (hYm.sub_const a)).aestronglyMeasurable
    by_cases hi : Integrable (fun ω => h (Y ω - a)) P
    · rw [← H1 hi, ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => hnn _),
        EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg fun ω => hnn _)]
    · rw [H2 hi]
      have : ∫⁻ ω, ENNReal.ofReal (h (Y ω - a)) ∂P = ⊤ := by
        by_contra hne
        exact hi ⟨hmeas, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => hnn _)).2
          (lt_top_iff_ne_top.2 hne)⟩
      rw [this, EReal.coe_ennreal_top]
  -- `0 ∈ F0` and its value
  have h0F0 : (fun _ : Ω => (0:ℝ)) ∈ F0 := by
    refine ⟨measurable_const, MemLp.zero, by simp, ?_, ?_⟩
    · exact ae_of_all _ fun ω => by simp [conj_zero h hnn h0]
    · simp [conj_zero h hnn h0]
  have hg0 : (∫ ω, Y ω * (fun _ : Ω => (0:ℝ)) ω ∂P - expectedConj P h (fun _ => (0:ℝ))) = 0 := by
    simp [expectedConj, conj_zero h hnn h0]
  set S := ⨆ Z ∈ F0, ((∫ ω, Y ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal) with hS
  have hS0 : (0 : EReal) ≤ S := by
    have := le_iSup₂_of_le (f := fun Z (_ : Z ∈ F0) =>
      ((∫ ω, Y ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) _ h0F0 le_rfl
    rw [hg0] at this
    exact_mod_cast this
  -- weak duality
  have weak : S ≤ ((minimalLoss P h Y : ENNReal) : EReal) := by
    refine iSup₂_le fun Z hZ => ?_
    refine real_le_coe_iInf _ _ fun a => ?_
    rw [K2 a]
    refine le_iSup₂_of_le (f := fun Z (_ : Z ∈ F) =>
      ((∫ ω, (Y ω - a) * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) Z
      ⟨hZ.1, hZ.2.1, hZ.2.2.2⟩ ?_
    rw [lin Z hZ.2.1 a, hZ.2.2.1, mul_zero, sub_zero]
  refine le_antisymm ?_ weak
  -- strong duality
  have hYlt : minimalLoss P h Y < ⊤ := by
    refine lt_of_le_of_lt (iInf_le _ 0) ?_
    simp only [sub_zero]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => hnn (Y ω))).1 hYi.2
  by_cases hA1 : ∃ u1 < 0, 0 < h u1
  · by_cases hA2 : ∃ u2 > 0, 0 < h u2
    · -- the main case
      obtain ⟨u1, hu1, hh1⟩ := hA1
      obtain ⟨u2, hu2, hh2⟩ := hA2
      obtain ⟨v1, hv1, hfv1⟩ := conj_fin_neg h hnn hconv h0 hu1 hh1
      obtain ⟨v2, hv2, hfv2⟩ := conj_fin_pos h hnn hconv h0 hu2 hh2
      have hSne_top : S ≠ ⊤ := by
        refine ne_top_of_le_ne_top ?_ weak
        exact fun h' => hYlt.ne (EReal.coe_ennreal_eq_top_iff.1 h')
      have hSne_bot : S ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hS0
      set s0 := S.toReal with hs0
      have hSs0 : S = (s0 : EReal) := (EReal.coe_toReal hSne_top hSne_bot).symm
      have hconst : ∀ v : ℝ, fenchelConj h v ≠ ⊤ → (fun _ : Ω => v) ∈ F := by
        intro v hv
        exact ⟨measurable_const, memLp_const v, ae_of_all _ fun _ => hv, integrable_const _⟩
      have hcomb : ∀ z1 ∈ F, ∀ z2 ∈ F, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          ∃ w ∈ F, ∫ ω, w ω ∂P = t * ∫ ω, z1 ω ∂P + (1 - t) * ∫ ω, z2 ω ∂P ∧
            t * (∫ ω, Y ω * z1 ω ∂P - expectedConj P h z1) +
              (1 - t) * (∫ ω, Y ω * z2 ω ∂P - expectedConj P h z2) ≤
              ∫ ω, Y ω * w ω ∂P - expectedConj P h w := by
        intro z1 hz1 z2 hz2 t ht0 ht1
        obtain ⟨m1, l1, f1, i1⟩ := hz1
        obtain ⟨m2, l2, f2, i2⟩ := hz2
        set w : Ω → ℝ := fun ω => t * z1 ω + (1 - t) * z2 ω with hw
        have hwm : Measurable w := (m1.const_mul t).add (m2.const_mul _)
        have hwl : MemLp w q P := (l1.const_mul t).add (l2.const_mul _)
        have hb : ∀ᵐ ω ∂P, fenchelConj h (w ω) ≤
            ((t * (fenchelConj h (z1 ω)).toReal + (1 - t) * (fenchelConj h (z2 ω)).toReal : ℝ)
              : EReal) := by
          filter_upwards [f1, f2] with ω a b
          exact conj_comb h h0 ht0 ht1 a b
        have hne : ∀ᵐ ω ∂P, fenchelConj h (w ω) ≠ ⊤ :=
          hb.mono fun ω hω => ne_top_of_le_ne_top (EReal.coe_ne_top _) hω
        have hle : ∀ᵐ ω ∂P, (fenchelConj h (w ω)).toReal ≤
            t * (fenchelConj h (z1 ω)).toReal + (1 - t) * (fenchelConj h (z2 ω)).toReal := by
          filter_upwards [hb] with ω hω
          have := EReal.toReal_le_toReal hω (ne_bot_of_le_ne_bot (by simp)
            (conj_nonneg h h0 _)) (EReal.coe_ne_top _)
          rwa [EReal.toReal_coe] at this
        have hbi : Integrable (fun ω => t * (fenchelConj h (z1 ω)).toReal +
            (1 - t) * (fenchelConj h (z2 ω)).toReal) P := (i1.const_mul t).add (i2.const_mul _)
        have hwi : Integrable (fun ω => (fenchelConj h (w ω)).toReal) P := by
          refine Integrable.mono' hbi
            (((conj_measurable h hc).comp hwm).ereal_toReal.aestronglyMeasurable) ?_
          filter_upwards [hle] with ω hω
          rw [Real.norm_eq_abs, abs_of_nonneg (conj_toReal_nonneg h h0 _)]
          exact hω
        refine ⟨w, ⟨hwm, hwl, hne, hwi⟩, ?_, ?_⟩
        · rw [hw, integral_add ((hZi z1 l1).const_mul t) ((hZi z2 l2).const_mul _),
            integral_const_mul, integral_const_mul]
        · have hE : expectedConj P h w ≤ t * expectedConj P h z1 + (1 - t) * expectedConj P h z2 := by
            unfold expectedConj
            rw [← integral_const_mul, ← integral_const_mul,
              ← integral_add (i1.const_mul t) (i2.const_mul _)]
            exact integral_mono_ae hwi hbi hle
          have hI : ∫ ω, Y ω * w ω ∂P = t * ∫ ω, Y ω * z1 ω ∂P + (1 - t) * ∫ ω, Y ω * z2 ω ∂P := by
            have e : (fun ω => Y ω * w ω) = fun ω => t * (Y ω * z1 ω) + (1 - t) * (Y ω * z2 ω) := by
              funext ω; simp only [hw]; ring
            rw [e, integral_add ((hYZ z1 l1).const_mul t) ((hYZ z2 l2).const_mul _),
              integral_const_mul, integral_const_mul]
          linarith
      have hzero : ∀ z ∈ F, ∫ ω, z ω ∂P = 0 → ∫ ω, Y ω * z ω ∂P - expectedConj P h z ≤ s0 := by
        intro z hz hm
        have : ((∫ ω, Y ω * z ω ∂P - expectedConj P h z : ℝ) : EReal) ≤ S :=
          le_iSup₂_of_le (f := fun Z (_ : Z ∈ F0) =>
            ((∫ ω, Y ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) z
            ⟨hz.1, hz.2.1, hm, hz.2.2⟩ le_rfl
        rw [hSs0] at this
        exact_mod_cast this
      obtain ⟨σ, hσ⟩ := supergrad F (fun z => ∫ ω, z ω ∂P)
        (fun z => ∫ ω, Y ω * z ω ∂P - expectedConj P h z) s0 hcomb hzero
        ⟨_, hconst v1 hfv1, by simpa using hv1⟩ ⟨_, hconst v2 hfv2, by simpa using hv2⟩
      calc ((minimalLoss P h Y : ENNReal) : EReal)
          ≤ ((∫⁻ ω, ENNReal.ofReal (h (Y ω - σ)) ∂P : ENNReal) : EReal) :=
            EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf_le _ σ)
        _ = ⨆ Z ∈ F, ((∫ ω, (Y ω - σ) * Z ω ∂P - expectedConj P h Z : ℝ) : EReal) := K2 σ
        _ ≤ S := by
          rw [hSs0]
          refine iSup₂_le fun Z hZ => ?_
          rw [lin Z hZ.2.1 σ]
          have := hσ Z hZ
          exact_mod_cast (by linarith : ∫ ω, Y ω * Z ω ∂P - σ * ∫ ω, Z ω ∂P -
            expectedConj P h Z ≤ s0)
    · -- `h = 0` on `[0, ∞)`
      push Not at hA2
      have hB : ∀ u, 0 ≤ u → h u = 0 := by
        intro u hu
        rcases hu.lt_or_eq with hu | rfl
        · exact le_antisymm (hA2 u hu) (hnn u)
        · exact h0
      have hanti : ∀ x y, x ≤ y → h y ≤ h x := by
        intro x y hxy
        rcases le_or_gt 0 y with hy | hy
        · rw [hB y hy]; exact hnn x
        · have hx : x < 0 := lt_of_le_of_lt hxy hy
          have ht0 : 0 ≤ y / x := le_of_lt (div_pos_of_neg_of_neg hy hx)
          have ht1 : y / x ≤ 1 := by rw [div_le_one_of_neg hx]; exact hxy
          have hs := conv_scale h hconv h0 ht0 ht1 x
          have e : y / x * x = y := div_mul_cancel₀ _ hx.ne
          rw [e] at hs
          nlinarith [hnn x]
      have := ml_zero P h hnn hc Y hYm hYi (fun n => -(n:ℝ))
        (fun n ω => hanti _ _ (by have : (0:ℝ) ≤ n := n.cast_nonneg; linarith))
        (fun ω => by
          filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (-Y ω)]
            with n hn
          exact hB _ (by linarith))
      rw [this]; simpa using hS0
  · -- `h = 0` on `(-∞, 0]`
    push Not at hA1
    have hB : ∀ u, u ≤ 0 → h u = 0 := by
      intro u hu
      rcases hu.lt_or_eq with hu | rfl
      · exact le_antisymm (hA1 u hu) (hnn u)
      · exact h0
    have hmono : ∀ x y, x ≤ y → h x ≤ h y := by
      intro x y hxy
      rcases le_or_gt x 0 with hx | hx
      · rw [hB x hx]; exact hnn y
      · have hy : 0 < y := lt_of_lt_of_le hx hxy
        have ht0 : 0 ≤ x / y := le_of_lt (div_pos hx hy)
        have ht1 : x / y ≤ 1 := by rw [div_le_one hy]; exact hxy
        have hs := conv_scale h hconv h0 ht0 ht1 y
        have e : x / y * y = x := div_mul_cancel₀ _ hy.ne'
        rw [e] at hs
        nlinarith [hnn y]
    have := ml_zero P h hnn hc Y hYm hYi (fun n => (n:ℝ))
      (fun n ω => hmono _ _ (by have : (0:ℝ) ≤ n := n.cast_nonneg; linarith))
      (fun ω => by
        filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Y ω)]
          with n hn
        exact hB _ (by linarith))
    rw [this]; simpa using hS0


/-! ### Part (iii) -/

theorem part_iii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] (h : ℝ → ℝ) (hnn : ∀ u, 0 ≤ h u) (hconv : ConvexOn ℝ Set.univ h)
    (h0 : h 0 = 0) (Y : Ω → ℝ) (hYm : Measurable Y) (hYp : MemLp Y p P)
    (hYi : Integrable (fun ω => h (Y ω)) P) :
    ((∫ ω, Y ω ∂P : ℝ) : EReal) - ((minimalLoss P h Y : ENNReal) : EReal) =
      ⨅ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
          HasFiniteExpectedConj P h (fun ω => 1 - Z ω)},
        ((∫ ω, Y ω * Z ω ∂P + expectedConj P h (fun ω => 1 - Z ω) : ℝ) : EReal) := by
  have hi := part_i P p q hp h hnn hconv h0 Y hYm hYp hYi
  have hYZ : ∀ Z : Ω → ℝ, MemLp Z q P → Integrable (fun ω => Y ω * Z ω) P :=
    fun Z hZ => hYp.integrable_mul hZ
  have hZi : ∀ Z : Ω → ℝ, MemLp Z q P → Integrable Z P := by
    intro Z hZ
    have := (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1:ℝ)) p P).integrable_mul hZ
    exact this.congr (ae_of_all _ fun ω => by simp)
  have hYint : Integrable Y P := by
    have := hYZ (fun _ => (1:ℝ)) (memLp_const 1)
    exact this.congr (ae_of_all _ fun ω => by simp)
  set F0 := {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 0 ∧
          HasFiniteExpectedConj P h Z} with hF0
  set F1 := {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
          HasFiniteExpectedConj P h (fun ω => 1 - Z ω)} with hF1
  set g : (Ω → ℝ) → ℝ := fun Z => ∫ ω, Y ω * Z ω ∂P - expectedConj P h Z with hg
  have hYlt : minimalLoss P h Y ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (iInf_le _ 0)
    simp only [sub_zero]
    exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => hnn (Y ω))).1 hYi.2).ne
  set D := (minimalLoss P h Y).toReal with hD
  have hDe : ((minimalLoss P h Y : ENNReal) : EReal) = (D : EReal) :=
    (EReal.coe_ennreal_toReal hYlt).symm
  have hgD : ∀ W ∈ F0, g W ≤ D := by
    intro W hW
    have : ((g W : ℝ) : EReal) ≤ ((minimalLoss P h Y : ENNReal) : EReal) := by
      rw [hi]
      exact le_iSup₂_of_le (f := fun Z (_ : Z ∈ F0) =>
        ((∫ ω, Y ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) W hW le_rfl
    rw [hDe] at this
    exact_mod_cast this
  -- `Z ↦ 1 - Z` maps `F1` to `F0`
  have hmap : ∀ Z ∈ F1, (fun ω => 1 - Z ω) ∈ F0 ∧
      ∫ ω, Y ω * Z ω ∂P + expectedConj P h (fun ω => 1 - Z ω) =
        ∫ ω, Y ω ∂P - g (fun ω => 1 - Z ω) := by
    intro Z hZ
    obtain ⟨hm, hl, h1, hf⟩ := hZ
    refine ⟨⟨measurable_const.sub hm, (memLp_const 1).sub hl, ?_, hf⟩, ?_⟩
    · rw [integral_sub (integrable_const _) (hZi Z hl), h1]; simp
    · have : ∫ ω, Y ω * (1 - Z ω) ∂P = ∫ ω, Y ω ∂P - ∫ ω, Y ω * Z ω ∂P := by
        have e : (fun ω => Y ω * (1 - Z ω)) = fun ω => Y ω - Y ω * Z ω := by
          funext ω; ring
        rw [e, integral_sub hYint (hYZ Z hl)]
      simp only [hg, this]
      ring
  have hback : ∀ W ∈ F0, (fun ω => 1 - W ω) ∈ F1 := by
    intro W hW
    obtain ⟨hm, hl, h1, hf⟩ := hW
    refine ⟨measurable_const.sub hm, (memLp_const 1).sub hl, ?_, ?_⟩
    · rw [integral_sub (integrable_const _) (hZi W hl), h1]; simp
    · have e : (fun ω => 1 - (1 - W ω)) = W := by funext ω; ring
      simpa only [e] using hf
  have hval : ∀ W : Ω → ℝ, (fun ω => 1 - (fun ω => 1 - W ω) ω) = W := by
    intro W; funext ω; ring
  set I := ⨅ Z ∈ F1, ((∫ ω, Y ω * Z ω ∂P + expectedConj P h (fun ω => 1 - Z ω) : ℝ) : EReal)
    with hI
  rw [hDe, ← EReal.coe_sub]
  have hlow : ((∫ ω, Y ω ∂P - D : ℝ) : EReal) ≤ I := by
    refine le_iInf₂ fun Z hZ => ?_
    obtain ⟨hW, he⟩ := hmap Z hZ
    rw [he]
    have := hgD _ hW
    exact_mod_cast (by linarith : ∫ ω, Y ω ∂P - D ≤ ∫ ω, Y ω ∂P - g (fun ω => 1 - Z ω))
  refine le_antisymm hlow ?_
  have h0F0 : (fun _ : Ω => (0:ℝ)) ∈ F0 := by
    refine ⟨measurable_const, MemLp.zero, by simp, ?_, ?_⟩
    · exact ae_of_all _ fun ω => by simp [conj_zero h hnn h0]
    · simp [conj_zero h hnn h0]
  have hItop : I ≠ ⊤ := by
    have h1F1 := hback _ h0F0
    have : I ≤ ((∫ ω, Y ω * (fun ω => 1 - (fun _ : Ω => (0:ℝ)) ω) ω ∂P +
        expectedConj P h (fun ω => 1 - (fun ω => 1 - (fun _ : Ω => (0:ℝ)) ω) ω) : ℝ) : EReal) :=
      iInf₂_le (f := fun Z (_ : Z ∈ F1) =>
        ((∫ ω, Y ω * Z ω ∂P + expectedConj P h (fun ω => 1 - Z ω) : ℝ) : EReal)) _ h1F1
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) this
  have hIbot : I ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
  set r := I.toReal with hr
  have hIr : I = (r : EReal) := (EReal.coe_toReal hItop hIbot).symm
  have hrW : ∀ W ∈ F0, g W ≤ ∫ ω, Y ω ∂P - r := by
    intro W hW
    have hZ := hback W hW
    have : I ≤ ((∫ ω, Y ω * (fun ω => 1 - W ω) ω ∂P +
        expectedConj P h (fun ω => 1 - (fun ω => 1 - W ω) ω) : ℝ) : EReal) :=
      iInf₂_le (f := fun Z (_ : Z ∈ F1) =>
        ((∫ ω, Y ω * Z ω ∂P + expectedConj P h (fun ω => 1 - Z ω) : ℝ) : EReal)) _ hZ
    rw [(hmap _ hZ).2, hval, hIr] at this
    have := EReal.coe_le_coe_iff.1 this
    linarith
  have hDr : D ≤ ∫ ω, Y ω ∂P - r := by
    have : ((minimalLoss P h Y : ENNReal) : EReal) ≤ ((∫ ω, Y ω ∂P - r : ℝ) : EReal) := by
      rw [hi]
      exact iSup₂_le fun W hW => EReal.coe_le_coe_iff.2 (hrW W hW)
    rw [hDe] at this
    exact_mod_cast this
  rw [hIr]
  exact_mod_cast (by linarith : r ≤ ∫ ω, Y ω ∂P - D)

end MLDualB


open MeasureTheory RiskFunctionals.Deviation in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] :
    -- (i), (2.113)
    (∀ h : ℝ → ℝ, (∀ u, 0 ≤ h u) → ConvexOn ℝ Set.univ h → h 0 = 0 →
      ∀ Y : Ω → ℝ, Measurable Y → MemLp Y p P → Integrable (fun ω => h (Y ω)) P →
        ((minimalLoss P h Y : ENNReal) : EReal) =
          ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 0 ∧
              HasFiniteExpectedConj P h Z},
            ((∫ ω, Y ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) ∧
    -- (i), (2.114)
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ Y : Ω → ℝ, Measurable Y → MemLp Y p P →
      ((avarDeviation P Y α : ℝ) : EReal) =
        ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧
            (∀ᵐ ω ∂P, -((1 - α) / α) ≤ Z ω ∧ Z ω ≤ 1) ∧ ∫ ω, Z ω ∂P = 0},
          ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal)) ∧
    -- (ii), the dual representation of `𝔼 − 𝒟`
    (∀ h : ℝ → ℝ, (∀ u, 0 ≤ h u) → ConvexOn ℝ Set.univ h → h 0 = 0 →
      ∀ Y : Ω → ℝ, Measurable Y → MemLp Y p P → Integrable (fun ω => h (Y ω)) P →
        ((∫ ω, Y ω ∂P : ℝ) : EReal) - ((minimalLoss P h Y : ENNReal) : EReal) =
          ⨅ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
              HasFiniteExpectedConj P h (fun ω => 1 - Z ω)},
            ((∫ ω, Y ω * Z ω ∂P + expectedConj P h (fun ω => 1 - Z ω) : ℝ) : EReal)) ∧
    -- (ii), the representation of `𝔸𝕍@ℝ_α`, with attainment
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ Y : Ω → ℝ, Measurable Y → MemLp Y p P →
      IsLeast {v : ℝ | ∃ Z : Ω → ℝ, Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
          (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ 1 / α) ∧ v = ∫ ω, Y ω * Z ω ∂P}
        (averageValueAtRisk P Y α)) :=
  ⟨fun h hnn hconv h0 Y hYm hYp hYi => MLDualB.part_i P p q hp h hnn hconv h0 Y hYm hYp hYi,
   fun α hα0 hα1 Y hYm hYp => MLDualA.part_ii P p q α hα0 hα1 Y hYm hYp,
   fun h hnn hconv h0 Y hYm hYp hYi => MLDualB.part_iii P p q hp h hnn hconv h0 Y hYm hYp hYi,
   fun α hα0 hα1 Y hYm hYp => MLDualA.part_iv P p q α hα0 hα1 Y hYm hYp⟩
