-- Prove2me | solution 1 for RiskFunctionals.Distortion.choquet_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:13:14.276139+00:00
-- url     : https://prove2.me/submissions/67d0199f-78e1-44aa-b54d-6d33a0d2d3f9

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional
import Definitions.Def_RiskFunctionals_Distortion_Orders
set_option linter.unusedSimpArgs false
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


open MeasureTheory ProbabilityTheory Set Filter Topology


theorem cr_qint (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ) :
    IntegrableOn (g79q_q μ) (Ioc 0 1) := by
  have hP : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have htr' : (volume.restrict (Set.Icc (0 : ℝ) 1)).map (g79q_q μ) = μ :=
    g79q_transform μ (volume.restrict (Set.Icc (0 : ℝ) 1)) id measurable_id Measure.map_id
  have hmeas := g79q_meas μ
  rw [← htr'] at hμ
  have := (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).1 hμ
  exact (show IntegrableOn (g79q_q μ) (Icc 0 1) volume from this).mono_set Ioc_subset_Icc_self

theorem cr_qmono (μ : Measure ℝ) [IsProbabilityMeasure μ] : MonotoneOn (g79q_q μ) (Ioo 0 1) := by
  intro p hp p' hp' hpp
  rw [g79q_qle' μ hp.1 hp.2]
  have := (g79q_qle' μ hp'.1 hp'.2 (g79q_q μ p')).1 le_rfl
  linarith

open MeasureTheory Set

noncomputable def cr_F (q : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := (Ioc 0 p.1).indicator (fun u => q u / p.1) p.2

noncomputable def cr_W (ν : Measure ℝ) (u : ℝ) : ℝ := ∫ a, (Ici u).indicator (fun a => 1 / a) a ∂ν

theorem cr_F_meas (q : ℝ → ℝ) (hq : Measurable q) : Measurable (cr_F q) := by
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)
  have : cr_F q = {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator (fun p => q p.2 / p.1) := by
    funext p; simp [cr_F, indicator, mem_Ioc]
  rw [this]
  exact ((hq.comp measurable_snd).div measurable_fst).indicator hs

theorem cr_F_int_u (q : ℝ → ℝ) (a : ℝ) :
    ∫ u, cr_F q (a, u) = (1 / a) * ∫ u in Ioc 0 a, q u := by
  simp only [cr_F]
  rw [integral_indicator measurableSet_Ioc, integral_div]
  ring

theorem cr_F_int_a (ν : Measure ℝ) (q : ℝ → ℝ) (hsupp : ∀ᵐ a ∂ν, a ≤ 1) (u : ℝ) :
    ∫ a, cr_F q (a, u) ∂ν = (Ioc 0 1).indicator (fun u => q u * cr_W ν u) u := by
  by_cases hu : u ∈ Ioc (0:ℝ) 1
  · rw [indicator_of_mem hu, cr_W, ← integral_const_mul]
    congr 1; funext a
    by_cases ha : u ≤ a
    · simp [cr_F, indicator, hu.1, ha, div_eq_mul_inv]
    · simp [cr_F, indicator, ha]
  · rw [indicator_of_notMem hu]
    rcases not_and_or.1 hu with h | h
    · simp [cr_F, indicator, h]
    · apply integral_eq_zero_of_ae
      filter_upwards [hsupp] with a ha
      have : u ∉ Ioc 0 a := fun h' => h (h'.2.trans ha)
      simp [cr_F, indicator_of_notMem this]

theorem cr_core (ν : Measure ℝ) [SFinite ν] (q : ℝ → ℝ) (hsupp : ∀ᵐ a ∂ν, a ≤ 1)
    (hF : Integrable (cr_F q) (ν.prod volume)) :
    Integrable (fun a => (1 / a) * ∫ u in Ioc 0 a, q u) ν ∧
      ∫ a, (1 / a) * (∫ u in Ioc 0 a, q u) ∂ν = ∫ u in Ioc 0 1, q u * cr_W ν u := by
  constructor
  · have := hF.integral_prod_left
    simpa [cr_F_int_u] using this
  · calc ∫ a, (1 / a) * (∫ u in Ioc 0 a, q u) ∂ν = ∫ a, (∫ u, cr_F q (a, u)) ∂ν := by
          simp only [cr_F_int_u]
      _ = ∫ u, (∫ a, cr_F q (a, u) ∂ν) := integral_integral_swap (f := fun a u => cr_F q (a, u)) hF
      _ = ∫ u in Ioc 0 1, q u * cr_W ν u := by
          simp only [cr_F_int_a ν q hsupp]
          rw [integral_indicator measurableSet_Ioc]


open MeasureTheory ProbabilityTheory Set Filter Topology RiskFunctionals.Distortion
open scoped ENNReal NNReal

theorem g82_meas (H : StieltjesFunction ℝ) (h : ℝ → ℝ)
    (hhi : IntegrableOn h (Icc (0:ℝ) 1))
    (hnn : ∀ p ∈ Icc (0:ℝ) 1, 0 ≤ h p)
    (hH : ∀ p ∈ Icc (0:ℝ) 1, H p = ∫ q in (0:ℝ)..p, h q) :
    H.measure.restrict (Ioc 0 1) =
      (volume.restrict (Ioc (0:ℝ) 1)).withDensity (fun p => ((h p).toNNReal : ℝ≥0∞)) := by
  have key : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
      H.measure (Ioc a b) = ∫⁻ p in Ioc a b, ((h p).toNNReal : ℝ≥0∞) := by
    intro a b ha hab hb
    have hII : ∀ c, 0 ≤ c → c ≤ 1 → IntervalIntegrable h volume 0 c := by
      intro c hc0 hc1
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc0]
      exact hhi.mono_set (Icc_subset_Icc le_rfl hc1)
    rw [StieltjesFunction.measure_Ioc, hH b ⟨by linarith, hb⟩, hH a ⟨ha, by linarith⟩,
      intervalIntegral.integral_interval_sub_left (hII b (by linarith) hb) (hII a ha (by linarith)),
      intervalIntegral.integral_of_le hab]
    have hint : IntegrableOn h (Ioc a b) := hhi.mono_set (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    · rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hnn x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  haveI : IsFiniteMeasure (H.measure.restrict (Ioc 0 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top
  refine Measure.ext_of_Ioc_finite _ _ ?_ ?_
  · rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact key 0 1 le_rfl zero_le_one le_rfl
  · intro a b _
    rw [Measure.restrict_apply measurableSet_Ioc, withDensity_apply _ measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc]
    rcases le_or_gt (a ⊔ 0) (b ⊓ 1) with hle | hlt
    · exact key _ _ le_sup_right hle inf_le_right
    · rw [Ioc_eq_empty (not_lt.2 hlt.le)]
      simp


open MeasureTheory ProbabilityTheory Set Filter Topology RiskFunctionals.Distortion
open scoped ENNReal NNReal

theorem cr_bound (q : ℝ → ℝ) (hqi : IntegrableOn q (Ioc 0 1)) (hqm : MonotoneOn q (Ioo 0 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Ioc (0:ℝ) 1,
      (1 / a) * (∫ u in Ioc 0 a, |q u|) ≤ |(1 / a) * ∫ u in Ioc 0 a, q u| + C := by
  set n : ℝ → ℝ := fun u => max (-q u) 0 with hn
  have hni : IntegrableOn n (Ioc 0 1) := hqi.neg.pos_part
  have habs : ∀ u, |q u| = q u + 2 * n u := by
    intro u
    rcases le_total 0 (q u) with h | h
    · simp [hn, abs_of_nonneg h, h]
    · simp [hn, abs_of_nonpos h, h]; ring
  by_cases hex : ∃ p1 ∈ Ioo (0:ℝ) 1, q p1 < 0
  · obtain ⟨p1, hp1, hq1⟩ := hex
    have hK : 0 ≤ ∫ u in Ioc 0 1, n u :=
      setIntegral_nonneg measurableSet_Ioc (fun u _ => le_max_right _ _)
    refine ⟨2 * (∫ u in Ioc 0 1, n u) / p1, by have := hp1.1; positivity, fun a ha => ?_⟩
    have hia : IntegrableOn q (Ioc 0 a) := hqi.mono_set (Ioc_subset_Ioc_right ha.2)
    rcases le_or_gt a p1 with hap | hap
    · have : ∫ u in Ioc 0 a, |q u| = - ∫ u in Ioc 0 a, q u := by
        rw [← integral_neg]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        have : q u ≤ q p1 := hqm ⟨hu.1, by linarith [hu.2, hp1.2]⟩ hp1 (hu.2.trans hap)
        show |q u| = -q u
        rw [abs_of_neg (by linarith)]
      rw [this, mul_neg]
      have := neg_le_abs ((1 / a) * ∫ u in Ioc 0 a, q u)
      have : 0 ≤ 2 * (∫ u in Ioc 0 1, n u) / p1 := by have := hp1.1; positivity
      linarith
    · have hnia : IntegrableOn n (Ioc 0 a) := hni.mono_set (Ioc_subset_Ioc_right ha.2)
      have hsplit : ∫ u in Ioc 0 a, |q u| = (∫ u in Ioc 0 a, q u) + 2 * ∫ u in Ioc 0 a, n u := by
        have e1 := integral_add hia (hnia.const_mul 2)
        have e2 : ∫ u in Ioc 0 a, 2 * n u = 2 * ∫ u in Ioc 0 a, n u := integral_const_mul _ _
        have e3 : ∫ u in Ioc 0 a, |q u| = ∫ u in Ioc 0 a, (q u + 2 * n u) :=
          setIntegral_congr_fun measurableSet_Ioc (fun u _ => habs u)
        rw [e3, e1, e2]
      have hn_le : ∫ u in Ioc 0 a, n u ≤ ∫ u in Ioc 0 1, n u :=
        setIntegral_mono_set hni (Eventually.of_forall fun u => le_max_right _ _)
          (Eventually.of_forall (Ioc_subset_Ioc_right ha.2))
      have hn0 : 0 ≤ ∫ u in Ioc 0 a, n u :=
        setIntegral_nonneg measurableSet_Ioc (fun u _ => le_max_right _ _)
      rw [hsplit, mul_add]
      have h1 := le_abs_self ((1 / a) * ∫ u in Ioc 0 a, q u)
      have h2 : (1 / a) * (2 * ∫ u in Ioc 0 a, n u) ≤ 2 * (∫ u in Ioc 0 1, n u) / p1 := by
        calc (1 / a) * (2 * ∫ u in Ioc 0 a, n u) ≤ (1 / p1) * (2 * ∫ u in Ioc 0 1, n u) :=
              mul_le_mul (one_div_le_one_div_of_le hp1.1 hap.le) (by linarith)
                (by positivity) (by have := hp1.1; positivity)
          _ = 2 * (∫ u in Ioc 0 1, n u) / p1 := by ring
      linarith
  · push_neg at hex
    refine ⟨0, le_rfl, fun a ha => ?_⟩
    have : ∫ u in Ioc 0 a, |q u| = ∫ u in Ioc 0 a, q u := by
      apply setIntegral_congr_ae measurableSet_Ioc
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (1:ℝ))] with u hu1 hu
      have hu1' : u ≠ 1 := hu1
      exact abs_of_nonneg (hex u ⟨hu.1, lt_of_le_of_ne (hu.2.trans ha.2) hu1'⟩)
    rw [this, add_zero]
    exact le_abs_self _

theorem cr_F1 (ν : Measure ℝ) [IsFiniteMeasure ν] : Integrable (cr_F (fun _ => 1)) (ν.prod volume) := by
  rw [integrable_prod_iff (cr_F_meas _ measurable_const).aestronglyMeasurable]
  constructor
  · filter_upwards with a
    simp only [cr_F]
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (by simp)
  · refine Integrable.mono' (integrable_const (1:ℝ))
      ((cr_F_meas _ measurable_const).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable ?_
    filter_upwards with a
    simp only [cr_F, norm_indicator_eq_indicator_norm]
    rw [integral_indicator measurableSet_Ioc, setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
    rcases le_or_gt a 0 with ha | ha
    · rw [max_eq_right (by linarith)]; simp
    · rw [max_eq_left (by linarith), sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
        abs_one, abs_of_pos ha, mul_one_div_cancel ha.ne', abs_one]

theorem cr_W_nonneg (ν : Measure ℝ) (u : ℝ) (hu : 0 < u) : 0 ≤ cr_W ν u := by
  apply integral_nonneg
  intro a
  by_cases ha : a ∈ Ici u
  · rw [indicator_of_mem ha]; exact one_div_nonneg.2 (hu.le.trans ha)
  · rw [indicator_of_notMem ha]; simp

theorem cr_part2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    (∀ (A : (Ω → ℝ) → ℝ) (M : StieltjesFunction ℝ), (∀ x ≤ 0, M x = 0) →
      (∀ Y₁ Y₂ : Ω → ℝ,
        Measurable Y₁ → Integrable Y₁ P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y₁) α) (Set.Icc 0 1) M.measure →
        Measurable Y₂ → Integrable Y₂ P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y₂) α) (Set.Icc 0 1) M.measure →
        Comonotone P Y₁ Y₂ → A (fun ω => Y₁ ω + Y₂ ω) = A Y₁ + A Y₂) →
      (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y) α) (Set.Icc 0 1) M.measure →
        A Y = ∫ α in Set.Icc (0 : ℝ) 1, averageValueAtRisk (P.map Y) α ∂M.measure) →
      ∃ H : StieltjesFunction ℝ, ∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y) α) (Set.Icc 0 1) M.measure →
          InDistortionDomain H (P.map Y) ∧ A Y = distortionFunctional H (P.map Y)) := by
  intro A M _hM0 _hcom hrep
  set ν := M.measure.restrict (Icc 0 1) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (isCompact_Icc.measure_lt_top.ne)
  have hsupp : ∀ᵐ a ∂ν, a ≤ 1 := (ae_restrict_mem measurableSet_Icc).mono fun a ha => ha.2
  set w := cr_W ν with hw
  set wI := (Ioc (0:ℝ) 1).indicator w with hwI
  have hwI_eq : wI = fun u => ∫ a, cr_F (fun _ => 1) (a, u) ∂ν := by
    funext u; rw [cr_F_int_a ν _ hsupp u]; simp only [hwI, one_mul]; rfl
  have hwIint : Integrable wI := by rw [hwI_eq]; exact (cr_F1 ν).integral_prod_right
  have hwInn : ∀ u, 0 ≤ wI u := by
    intro u
    by_cases hu : u ∈ Ioc (0:ℝ) 1
    · rw [hwI, indicator_of_mem hu]; exact cr_W_nonneg ν u hu.1
    · rw [hwI, indicator_of_notMem hu]
  have hcont : Continuous fun p => ∫ u in (0:ℝ)..p, wI u :=
    intervalIntegral.continuous_primitive (fun a b => hwIint.intervalIntegrable) 0
  let H : StieltjesFunction ℝ :=
    { toFun := fun p => ∫ u in (0:ℝ)..p, wI u
      mono' := by
        intro a b hab
        have := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hwIint.intervalIntegrable (a := 0) (b := a)) (hwIint.intervalIntegrable (a := a) (b := b))
        have h2 : 0 ≤ ∫ u in a..b, wI u := intervalIntegral.integral_nonneg hab (fun u _ => hwInn u)
        simp only
        linarith
      right_continuous' := fun x => hcont.continuousWithinAt }
  have hHv : ∀ p, H p = ∫ u in (0:ℝ)..p, wI u := fun p => rfl
  have hmeas := g82_meas H wI hwIint.integrableOn (fun p _ => hwInn p) (fun p _ => hHv p)
  have hfm : Measurable fun p => (wI p).toNNReal := by
    rw [hwI_eq]
    exact ((cr_F_meas _ measurable_const).stronglyMeasurable.integral_prod_left').measurable.real_toNNReal
  refine ⟨H, fun Y hYm hYi hAV => ?_⟩
  set μ := P.map Y with hμ
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hYm.aemeasurable
  set q := g79q_q μ with hq
  have hqi : IntegrableOn q (Ioc 0 1) :=
    cr_qint μ ((integrable_map_measure aestronglyMeasurable_id hYm.aemeasurable).2 hYi)
  obtain ⟨C, hC0, hC⟩ := cr_bound q hqi (cr_qmono μ)
  have hF : Integrable (cr_F q) (ν.prod volume) := by
    rw [integrable_prod_iff (cr_F_meas q (g79q_meas μ)).aestronglyMeasurable]
    constructor
    · filter_upwards [hsupp] with a ha
      simp only [cr_F]
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact (show IntegrableOn (fun x => q x / a) (Ioc 0 1) volume from hqi.div_const a).mono_set
        (Ioc_subset_Ioc_right ha)
    · refine Integrable.mono' (hAV.norm.add (integrable_const C))
        ((cr_F_meas q (g79q_meas μ)).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      simp only [cr_F, norm_indicator_eq_indicator_norm]
      rw [integral_indicator measurableSet_Ioc]
      rcases eq_or_lt_of_le ha.1 with h0 | h0
      · subst h0; simp; positivity
      · have e : ∫ u in Ioc 0 a, ‖q u / a‖ = (1 / a) * ∫ u in Ioc 0 a, |q u| := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
          simp only [Real.norm_eq_abs, abs_div, abs_of_pos h0]; ring
        rw [e, Real.norm_eq_abs, abs_of_nonneg (by have := h0; positivity)]
        have := hC a ⟨h0, ha.2⟩
        have e2 : averageValueAtRisk μ a = (1 / a) * ∫ u in Ioc 0 a, q u := rfl
        show _ ≤ ‖averageValueAtRisk μ a‖ + C
        rw [e2, Real.norm_eq_abs]; exact this
  obtain ⟨_, hEq⟩ := cr_core ν q hsupp hF
  have hqw : IntegrableOn (fun u => q u * w u) (Ioc 0 1) := by
    have := hF.integral_prod_right
    simp only [cr_F_int_a ν q hsupp] at this
    exact (integrable_indicator_iff measurableSet_Ioc).1 this
  have hsm : ∀ p ∈ Ioc (0:ℝ) 1, (wI p).toNNReal • q p = q p * w p := by
    intro p hp
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hwInn p), smul_eq_mul, mul_comm, hwI, indicator_of_mem hp]
  have hD : distortionFunctional H μ = ∫ p in Ioc (0:ℝ) 1, q p * w p := by
    rw [distortionFunctional, hmeas, integral_withDensity_eq_integral_smul hfm]
    exact setIntegral_congr_fun measurableSet_Ioc hsm
  refine ⟨⟨by simp [hHv], ?_, ?_⟩, ?_⟩
  · rw [IntegrableOn, hmeas, integrable_withDensity_iff_integrable_smul hfm]
    exact hqw.congr ((ae_restrict_mem measurableSet_Ioc).mono fun p hp => (hsm p hp).symm)
  · intro h1; exfalso; apply h1
    have : H.measure {1} = H.measure.restrict (Ioc 0 1) {1} := by
      rw [Measure.restrict_apply (measurableSet_singleton 1),
        inter_eq_left.2 (singleton_subset_iff.2 (show (1:ℝ) ∈ Ioc 0 1 from ⟨zero_lt_one, le_rfl⟩))]
    rw [this, hmeas]
    exact withDensity_absolutelyContinuous _ _ (by simp)
  · rw [hrep Y hYm hYi hAV, hD, ← hEq]
    rfl


open MeasureTheory ProbabilityTheory Set Filter Topology RiskFunctionals.Distortion
open scoped ENNReal NNReal

theorem cr_stieltjes (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∃ M : StieltjesFunction ℝ, M.measure = ν ∧ ∀ x, M x = ν.real (Iic x) := by
  by_cases h0 : ν = 0
  · refine ⟨0, by simp [h0], fun x => by simp [h0]⟩
  · set c := ν univ with hc
    have hc0 : c ≠ 0 := by rwa [hc, Ne, Measure.measure_univ_eq_zero]
    have hct : c ≠ ∞ := measure_ne_top ν univ
    set π := c⁻¹ • ν with hπ
    haveI : IsProbabilityMeasure π := ⟨by
      rw [hπ, Measure.smul_apply, smul_eq_mul, ← hc, ENNReal.inv_mul_cancel hc0 hct]⟩
    have hνπ : ν = (c.toNNReal : ℝ≥0∞) • π := by
      rw [hπ, smul_smul, ENNReal.coe_toNNReal hct, ENNReal.mul_inv_cancel hc0 hct, one_smul]
    refine ⟨c.toNNReal • cdf π, ?_, fun x => ?_⟩
    · rw [StieltjesFunction.measure_smul, measure_cdf, hνπ]; rfl
    · change (c.toNNReal : ℝ) * cdf π x = _
      rw [cdf_eq_real, hπ, measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ← mul_assoc, ← measureReal_def, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_inv,
        mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hc0, hct⟩), one_mul]

section
variable (h : ℝ → ℝ)

/-- level-set inverse of `h` -/
noncomputable def cr_S (s : ℝ) : Set ℝ := {x | x ∈ Ioo (0:ℝ) 1 ∧ s ≤ h x}
noncomputable def cr_al (s : ℝ) : ℝ := sSup (cr_S h s)

theorem cr_bdd (s : ℝ) : BddAbove (cr_S h s) := ⟨1, fun x hx => hx.1.2.le⟩

theorem cr_al_nonneg (s : ℝ) : 0 ≤ cr_al h s := Real.sSup_nonneg (fun x hx => hx.1.1.le)

theorem cr_al_le_one (s : ℝ) : cr_al h s ≤ 1 := Real.sSup_le (fun x hx => hx.1.2.le) zero_le_one

theorem cr_al_anti : Antitone (cr_al h) := by
  intro s1 s2 hs
  by_cases hne : (cr_S h s2).Nonempty
  · exact csSup_le_csSup (cr_bdd h s1) hne (fun x hx => ⟨hx.1, hs.trans hx.2⟩)
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [cr_al, hne, Real.sSup_empty]; exact cr_al_nonneg h s1

theorem cr_al_meas : Measurable (cr_al h) := (cr_al_anti h).measurable

theorem cr_al_i {u s : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (hs : s ≤ h u) : u ≤ cr_al h s :=
  le_csSup (cr_bdd h s) ⟨hu, hs⟩

theorem cr_al_ii (hanti : AntitoneOn h (Ioc 0 1)) {u s : ℝ} (hu : u ∈ Ioo (0:ℝ) 1)
    (hlt : u < cr_al h s) : s ≤ h u := by
  have hne : (cr_S h s).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [cr_al, hne, Real.sSup_empty] at hlt; linarith [hu.1]
  obtain ⟨x, hx, hux⟩ := exists_lt_of_lt_csSup hne hlt
  exact hx.2.trans (hanti ⟨hu.1, hu.2.le⟩ ⟨hx.1.1, hx.1.2.le⟩ hux.le)

theorem cr_null : ∀ᵐ u ∂(volume : Measure ℝ), volume {s | cr_al h s = u} = 0 := by
  set D : Set (ℝ × ℝ) := {p | cr_al h p.2 = p.1} with hD
  have hDm : MeasurableSet D := measurableSet_eq_fun ((cr_al_meas h).comp measurable_snd) measurable_fst
  have h0 : (volume.prod volume) D = 0 := by
    rw [Measure.prod_apply_symm hDm]
    have : ∀ y, volume ((fun x => (x, y)) ⁻¹' D) = 0 := by
      intro y
      have : (fun x => (x, y)) ⁻¹' D = {cr_al h y} := by
        ext x; simp [hD, eq_comm]
      rw [this, measure_singleton]
    simp [this]
  exact (Measure.measure_prod_null hDm).1 h0
end


open MeasureTheory ProbabilityTheory Set Filter Topology RiskFunctionals.Distortion
open scoped ENNReal NNReal

section
variable (h : ℝ → ℝ)

theorem cr_Emeas (u : ℝ) : MeasurableSet {s | u ∈ Ioc 0 (cr_al h s)} := by
  have : {s | u ∈ Ioc 0 (cr_al h s)} = {_s : ℝ | 0 < u} ∩ {s | u ≤ cr_al h s} := rfl
  rw [this]
  exact (MeasurableSet.const _).inter (measurableSet_le measurable_const (cr_al_meas h))

theorem cr_L (hanti : AntitoneOn h (Ioc 0 1)) :
    ∀ᵐ u ∂(volume : Measure ℝ), (volume.restrict (Ioi 0)) {s | u ∈ Ioc 0 (cr_al h s)} =
      ENNReal.ofReal ((Ioo (0:ℝ) 1).indicator h u) := by
  filter_upwards [cr_null h, compl_mem_ae_iff.2 (measure_singleton (1:ℝ))] with u hnull hu1
  have hu1' : u ≠ 1 := hu1
  rw [Measure.restrict_apply (cr_Emeas h u)]
  rcases le_or_gt u 0 with h0 | h0
  · have : {s | u ∈ Ioc 0 (cr_al h s)} = ∅ := by
      ext s; simp only [mem_setOf_eq, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro hu; linarith
    rw [this, empty_inter, measure_empty, indicator_of_notMem (fun hu => by linarith [hu.1]),
      ENNReal.ofReal_zero]
  rcases lt_or_gt_of_ne hu1' with h1 | h1
  · have hu : u ∈ Ioo (0:ℝ) 1 := ⟨h0, h1⟩
    rw [indicator_of_mem hu]
    apply le_antisymm
    · calc volume ({s | u ∈ Ioc 0 (cr_al h s)} ∩ Ioi 0)
          ≤ volume (Ioc 0 (h u) ∪ {s | cr_al h s = u}) := by
            apply measure_mono
            intro s ⟨hs, hs0⟩
            rcases eq_or_lt_of_le hs.2 with he | hlt
            · exact Or.inr he.symm
            · exact Or.inl ⟨hs0, cr_al_ii h hanti hu hlt⟩
        _ ≤ volume (Ioc 0 (h u)) + volume {s | cr_al h s = u} := measure_union_le _ _
        _ = ENNReal.ofReal (h u) := by rw [hnull, add_zero, Real.volume_Ioc, sub_zero]
    · rw [← sub_zero (h u), ← Real.volume_Ioc]
      apply measure_mono
      intro s hs
      exact ⟨⟨h0, cr_al_i h hu hs.2⟩, hs.1⟩
  · have : {s | u ∈ Ioc 0 (cr_al h s)} = ∅ := by
      ext s; simp only [mem_setOf_eq, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro _ hu; linarith [cr_al_le_one h s]
    rw [this, empty_inter, measure_empty, indicator_of_notMem (fun hu => by linarith [hu.2]),
      ENNReal.ofReal_zero]

theorem cr_tot (hanti : AntitoneOn h (Ioc 0 1)) (hint : IntegrableOn h (Ioc 0 1))
    (hpos : ∀ p ∈ Ioo (0:ℝ) 1, 0 ≤ h p) :
    ∫⁻ s in Ioi 0, ENNReal.ofReal (cr_al h s) = ENNReal.ofReal (∫ u in Ioc 0 1, h u) := by
  have hIint : Integrable ((Ioo (0:ℝ) 1).indicator h) :=
    (integrable_indicator_iff measurableSet_Ioo).2 (hint.mono_set Ioo_subset_Ioc_self)
  have hInn : 0 ≤ᵐ[volume] (Ioo (0:ℝ) 1).indicator h := Eventually.of_forall fun u => by
    by_cases hu : u ∈ Ioo (0:ℝ) 1
    · rw [indicator_of_mem hu]; exact hpos u hu
    · rw [indicator_of_notMem hu]; rfl
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ cr_al h p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd ((cr_al_meas h).comp measurable_fst))
  calc ∫⁻ s in Ioi 0, ENNReal.ofReal (cr_al h s)
      = ∫⁻ s in Ioi 0, ∫⁻ u, (Ioc 0 (cr_al h s)).indicator 1 u := by
        congr 1; funext s
        rw [lintegral_indicator_one measurableSet_Ioc, Real.volume_Ioc, sub_zero]
    _ = ∫⁻ u, ∫⁻ s in Ioi 0, (Ioc 0 (cr_al h s)).indicator 1 u := by
        apply lintegral_lintegral_swap
        have : Function.uncurry (fun s u => (Ioc 0 (cr_al h s)).indicator (1 : ℝ → ℝ≥0∞) u) =
            {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ cr_al h p.1}.indicator 1 := by
          funext p; rcases p with ⟨s, u⟩; simp [indicator, mem_Ioc]
        rw [this]
        exact (measurable_const.indicator hset).aemeasurable
    _ = ∫⁻ u, ENNReal.ofReal ((Ioo (0:ℝ) 1).indicator h u) := by
        apply lintegral_congr_ae
        filter_upwards [cr_L h hanti] with u hu
        rw [← hu, ← lintegral_indicator_one (cr_Emeas h u)]
        congr 1
    _ = ENNReal.ofReal (∫ u, (Ioo (0:ℝ) 1).indicator h u) :=
        (ofReal_integral_eq_lintegral_ofReal hIint hInn).symm
    _ = ENNReal.ofReal (∫ u in Ioc 0 1, h u) := by
        rw [integral_indicator measurableSet_Ioo, setIntegral_congr_set Ioo_ae_eq_Ioc]

/-- the measure `dM` -/
noncomputable def cr_nu : Measure ℝ :=
  ((volume.restrict (Ioi 0)).withDensity (fun s => ENNReal.ofReal (cr_al h s))).map (cr_al h)

theorem cr_nu_apply {B : Set ℝ} (hB : MeasurableSet B) :
    cr_nu h B = ∫⁻ s in cr_al h ⁻¹' B, ENNReal.ofReal (cr_al h s) ∂(volume.restrict (Ioi 0)) := by
  rw [cr_nu, Measure.map_apply (cr_al_meas h) hB,
    withDensity_apply _ ((cr_al_meas h) hB)]

theorem cr_nu_univ (hanti : AntitoneOn h (Ioc 0 1)) (hint : IntegrableOn h (Ioc 0 1))
    (hpos : ∀ p ∈ Ioo (0:ℝ) 1, 0 ≤ h p) :
    cr_nu h univ = ENNReal.ofReal (∫ u in Ioc 0 1, h u) := by
  rw [cr_nu_apply h MeasurableSet.univ, preimage_univ, Measure.restrict_univ, cr_tot h hanti hint hpos]

theorem cr_nu_Iic0 : cr_nu h (Iic 0) = 0 := by
  rw [cr_nu_apply h measurableSet_Iic]
  apply setLIntegral_eq_zero ((cr_al_meas h) measurableSet_Iic)
  intro s hs
  simp only [mem_preimage, mem_Iic] at hs
  simp [ENNReal.ofReal_eq_zero.2 hs]

theorem cr_nu_compl : cr_nu h (Icc 0 1)ᶜ = 0 := by
  rw [cr_nu_apply h measurableSet_Icc.compl]
  have : cr_al h ⁻¹' (Icc 0 1)ᶜ = ∅ := by
    ext s; simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact ⟨cr_al_nonneg h s, cr_al_le_one h s⟩
  rw [this, Measure.restrict_empty, lintegral_zero_measure]

theorem cr_W_eq (hanti : AntitoneOn h (Ioc 0 1)) (hpos : ∀ p ∈ Ioo (0:ℝ) 1, 0 ≤ h p) :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioc (0:ℝ) 1 → cr_W (cr_nu h) u = (Ioo (0:ℝ) 1).indicator h u := by
  filter_upwards [cr_L h hanti] with u hu hmem
  have hg : Measurable ((Ici u).indicator (fun a : ℝ => 1 / a)) :=
    (measurable_const.div measurable_id).indicator measurableSet_Ici
  rw [cr_W, cr_nu, integral_map (cr_al_meas h).aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (cr_al_meas h).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ s, (ENNReal.ofReal (cr_al h s)).toReal • (Ici u).indicator (fun a : ℝ => 1 / a) (cr_al h s)
      = {s | u ∈ Ioc 0 (cr_al h s)}.indicator 1 s := by
    intro s
    rw [ENNReal.toReal_ofReal (cr_al_nonneg h s), smul_eq_mul]
    by_cases hs : u ≤ cr_al h s
    · have hpos : 0 < cr_al h s := hmem.1.trans_le hs
      rw [indicator_of_mem (show cr_al h s ∈ Ici u from hs),
        indicator_of_mem (show s ∈ {s | u ∈ Ioc 0 (cr_al h s)} from ⟨hmem.1, hs⟩),
        mul_one_div_cancel hpos.ne']
      rfl
    · rw [indicator_of_notMem (show cr_al h s ∉ Ici u from hs),
        indicator_of_notMem (show s ∉ {s | u ∈ Ioc 0 (cr_al h s)} from fun h' => hs h'.2), mul_zero]
  simp only [hpt]
  rw [integral_indicator_one (cr_Emeas h u), measureReal_def, hu, ENNReal.toReal_ofReal]
  by_cases hu' : u ∈ Ioo (0:ℝ) 1
  · rw [indicator_of_mem hu']; exact hpos u hu'
  · rw [indicator_of_notMem hu']
end


open MeasureTheory ProbabilityTheory Set Filter Topology RiskFunctionals.Distortion
open scoped ENNReal NNReal

theorem cr_II (h : ℝ → ℝ) (hint : IntegrableOn h (Ioc 0 1)) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntervalIntegrable h volume 0 c := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc0]
  exact hint.mono_set (Ioc_subset_Ioc_right hc1)

theorem cr_hpos (H : StieltjesFunction ℝ) (h : ℝ → ℝ) (hanti : AntitoneOn h (Ioc 0 1))
    (hint : IntegrableOn h (Ioc 0 1)) (hH : ∀ p ∈ Icc (0:ℝ) 1, H p = ∫ α in (0:ℝ)..p, h α) :
    ∀ p ∈ Ioo (0:ℝ) 1, 0 ≤ h p := by
  intro p hp
  by_contra hneg
  push_neg at hneg
  have hle : ∀ x ∈ Ioc p 1, h x ≤ h p := fun x hx =>
    hanti ⟨hp.1, hp.2.le⟩ ⟨by linarith [hx.1, hp.1], hx.2⟩ hx.1.le
  have hdiff : H 1 - H p = ∫ x in Ioc p 1, h x := by
    rw [hH 1 ⟨zero_le_one, le_rfl⟩, hH p ⟨hp.1.le, hp.2.le⟩,
      intervalIntegral.integral_interval_sub_left (cr_II h hint 1 zero_le_one le_rfl)
        (cr_II h hint p hp.1.le hp.2.le), intervalIntegral.integral_of_le hp.2.le]
  have hm : ∫ x in Ioc p 1, h x ≤ ∫ x in Ioc p 1, h p :=
    setIntegral_mono_on (hint.mono_set (Ioc_subset_Ioc_left hp.1.le))
      (integrableOn_const (by simp)) measurableSet_Ioc hle
  rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, max_eq_left (by linarith [hp.2])] at hm
  have hmono : H p ≤ H 1 := H.mono hp.2.le
  have : (1 - p) * h p < 0 := mul_neg_of_pos_of_neg (by linarith [hp.2]) hneg
  linarith

theorem cr_part1 :
    ∀ (H : StieltjesFunction ℝ) (h : ℝ → ℝ), AntitoneOn h (Set.Ioc 0 1) →
      IntegrableOn h (Set.Ioc 0 1) →
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = ∫ α in (0 : ℝ)..p, h α) →
      ∃ M : StieltjesFunction ℝ, (∀ x ≤ 0, M x = 0) ∧ M 1 = H 1 ∧
        ∀ μ : Measure ℝ, IsProbabilityMeasure μ → InDistortionDomain H μ →
          IntegrableOn (fun α => averageValueAtRisk μ α) (Set.Icc 0 1) M.measure ∧
          distortionFunctional H μ =
            ∫ α in Set.Icc (0 : ℝ) 1, averageValueAtRisk μ α ∂M.measure := by
  intro H h hanti hint hH
  have hpos := cr_hpos H h hanti hint hH
  set ν := cr_nu h with hν
  have hH1 : H 1 = ∫ u in Ioc 0 1, h u := by
    rw [hH 1 ⟨zero_le_one, le_rfl⟩, intervalIntegral.integral_of_le zero_le_one]
  have hH0 : H 0 = 0 := by rw [hH 0 ⟨le_rfl, zero_le_one⟩, intervalIntegral.integral_same]
  have hH1nn : 0 ≤ H 1 := hH0 ▸ H.mono zero_le_one
  have huniv : ν univ = ENNReal.ofReal (H 1) := by rw [hH1]; exact cr_nu_univ h hanti hint hpos
  haveI : IsFiniteMeasure ν := ⟨by rw [huniv]; exact ENNReal.ofReal_lt_top⟩
  obtain ⟨M, hMν, hMx⟩ := cr_stieltjes ν
  have hrest : M.measure.restrict (Icc 0 1) = ν := by
    rw [hMν]
    exact Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 (cr_nu_compl h) |>.mono
      fun x hx => by simpa using hx)
  have hsupp : ∀ᵐ a ∂ν, a ≤ 1 := by
    rw [← hrest]; exact (ae_restrict_mem measurableSet_Icc).mono fun a ha => ha.2
  refine ⟨M, fun x hx => ?_, ?_, fun μ hμ hG => ?_⟩
  · rw [hMx, measureReal_def, measure_mono_null (Iic_subset_Iic.2 hx) (cr_nu_Iic0 h),
      ENNReal.toReal_zero]
  · rw [hMx, measureReal_def]
    have : ν (Iic 1) = ν univ := by
      apply le_antisymm (measure_mono (subset_univ _))
      have hc : ν (Iic 1)ᶜ = 0 := measure_mono_null
        (fun x hx => fun hx' => hx hx'.2) (cr_nu_compl h)
      rw [measure_compl measurableSet_Iic (measure_ne_top _ _)] at hc
      exact tsub_eq_zero_iff_le.1 hc
    rw [this, huniv, ENNReal.toReal_ofReal hH1nn]
  · set q := g79q_q μ with hq
    set hI := (Ioo (0:ℝ) 1).indicator h with hhI
    have hInn : ∀ p, 0 ≤ hI p := by
      intro p
      by_cases hp : p ∈ Ioo (0:ℝ) 1
      · rw [hhI, indicator_of_mem hp]; exact hpos p hp
      · rw [hhI, indicator_of_notMem hp]
    have hIint : IntegrableOn hI (Icc 0 1) :=
      ((integrable_indicator_iff measurableSet_Ioo).2 (hint.mono_set Ioo_subset_Ioc_self)).integrableOn
    have hH' : ∀ p ∈ Icc (0:ℝ) 1, H p = ∫ u in (0:ℝ)..p, hI u := by
      intro p hp
      rw [hH p hp]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (1:ℝ))] with u hu1 hu
      rw [uIoc_of_le hp.1] at hu
      have hu1' : u ≠ 1 := hu1
      rw [hhI, indicator_of_mem (show u ∈ Ioo (0:ℝ) 1 from ⟨hu.1, lt_of_le_of_ne (hu.2.trans hp.2) hu1'⟩)]
    have hmeas := g82_meas H hI hIint (fun p _ => hInn p) hH'
    have hfm : AEMeasurable (fun p => (hI p).toNNReal) (volume.restrict (Ioc 0 1)) :=
      (hIint.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)).aemeasurable.real_toNNReal
    have hsm : ∀ p ∈ Ioc (0:ℝ) 1, (hI p).toNNReal • q p = q p * hI p := by
      intro p hp
      rw [NNReal.smul_def, Real.coe_toNNReal _ (hInn p), smul_eq_mul, mul_comm]
    have hqh : IntegrableOn (fun p => q p * hI p) (Ioc 0 1) := by
      have := hG.2.1
      rw [IntegrableOn, hmeas, integrable_withDensity_iff_integrable_smul₀ hfm] at this
      exact this.congr ((ae_restrict_mem measurableSet_Ioc).mono fun p hp => hsm p hp)
    have hD : distortionFunctional H μ = ∫ p in Ioc (0:ℝ) 1, q p * hI p := by
      rw [distortionFunctional, hmeas, integral_withDensity_eq_integral_smul₀ hfm]
      exact setIntegral_congr_fun measurableSet_Ioc hsm
    have hWe := cr_W_eq h hanti hpos
    have hF : Integrable (cr_F q) (ν.prod volume) := by
      rw [integrable_prod_iff' (cr_F_meas q (g79q_meas μ)).aestronglyMeasurable]
      constructor
      · filter_upwards [(cr_F1 ν).prod_left_ae] with u hu
        have : (fun a => cr_F q (a, u)) = fun a => q u * cr_F (fun _ => 1) (a, u) := by
          funext a; simp only [cr_F, indicator]; split_ifs <;> ring
        rw [this]; exact hu.const_mul _
      · have hn : ∀ p, ‖cr_F q p‖ = cr_F (fun u => |q u|) p := by
          intro p; simp only [cr_F, indicator]
          split_ifs with hp
          · rw [Real.norm_eq_abs, abs_div, abs_of_pos (hp.1.trans_le hp.2)]
          · simp
        simp only [hn, cr_F_int_a ν _ hsupp]
        rw [integrable_indicator_iff measurableSet_Ioc]
        refine hqh.norm.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hWe] with u hu hW
        rw [hW hu, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hInn u)]
    obtain ⟨hInt, hEq⟩ := cr_core ν q hsupp hF
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn, hrest]; exact hInt
    · rw [hrest, hD]
      change _ = ∫ a, (1 / a) * (∫ u in Ioc 0 a, q u) ∂ν
      rw [hEq]
      apply setIntegral_congr_ae measurableSet_Ioc
      filter_upwards [hWe] with u hW hu
      rw [hW hu]


open MeasureTheory ProbabilityTheory Set Filter Topology RiskFunctionals.Distortion
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    -- (1) H concave ⇒ Choquet representation (2.66)
    (∀ (H : StieltjesFunction ℝ) (h : ℝ → ℝ), AntitoneOn h (Set.Ioc 0 1) →
      IntegrableOn h (Set.Ioc 0 1) →
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = ∫ α in (0 : ℝ)..p, h α) →
      ∃ M : StieltjesFunction ℝ, (∀ x ≤ 0, M x = 0) ∧ M 1 = H 1 ∧
        ∀ μ : Measure ℝ, IsProbabilityMeasure μ → InDistortionDomain H μ →
          IntegrableOn (fun α => averageValueAtRisk μ α) (Set.Icc 0 1) M.measure ∧
          distortionFunctional H μ =
            ∫ α in Set.Icc (0 : ℝ) 1, averageValueAtRisk μ α ∂M.measure) ∧
    -- (2) comonotone additive + Choquet representation ⇒ distortion functional
    (∀ (A : (Ω → ℝ) → ℝ) (M : StieltjesFunction ℝ), (∀ x ≤ 0, M x = 0) →
      (∀ Y₁ Y₂ : Ω → ℝ,
        Measurable Y₁ → Integrable Y₁ P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y₁) α) (Set.Icc 0 1) M.measure →
        Measurable Y₂ → Integrable Y₂ P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y₂) α) (Set.Icc 0 1) M.measure →
        Comonotone P Y₁ Y₂ → A (fun ω => Y₁ ω + Y₂ ω) = A Y₁ + A Y₂) →
      (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y) α) (Set.Icc 0 1) M.measure →
        A Y = ∫ α in Set.Icc (0 : ℝ) 1, averageValueAtRisk (P.map Y) α ∂M.measure) →
      ∃ H : StieltjesFunction ℝ, ∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
        IntegrableOn (fun α => averageValueAtRisk (P.map Y) α) (Set.Icc 0 1) M.measure →
          InDistortionDomain H (P.map Y) ∧ A Y = distortionFunctional H (P.map Y)) :=
  ⟨cr_part1, cr_part2 P⟩

