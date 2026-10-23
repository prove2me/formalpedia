-- Prove2me | solution 1 for RiskFunctionals.Distortion.distortion_examples
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:01:44.624238+00:00
-- url     : https://prove2.me/submissions/274771f8-5d12-4ec3-9418-c57234850179

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional
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


open RiskFunctionals.Distortion

theorem g79s_restrict_eq (H G : StieltjesFunction ℝ) (l r : ℝ)
    (hHG : ∀ x ∈ Set.Icc l r, H x = G x) :
    H.measure.restrict (Set.Ioc l r) = G.measure.restrict (Set.Ioc l r) := by
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Set.Ioc_inter_Ioc]
  rcases le_or_gt (a ⊔ l) (b ⊓ r) with h | h
  · rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
      hHG _ ⟨le_sup_right, h.trans inf_le_right⟩, hHG _ ⟨le_sup_right.trans h, inf_le_right⟩]
  · rw [Set.Ioc_eq_empty (not_lt.mpr h.le)]
    simp

theorem g79s_part1 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (Integrable (fun x : ℝ => x) μ → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = p) →
        distortionFunctional H μ = ∫ x, x ∂μ ∧
        ∫ x, x ∂μ = ∫ p in Set.Ioc (0 : ℝ) 1, quantileFunction μ p ∧
        ∫ x, x ∂μ = -(∫ u in Set.Iic (0 : ℝ), distributionFunction μ u) +
          ∫ u in Set.Ioi (0 : ℝ), (1 - distributionFunction μ u)) := by
  intro hint H hH
  have hm : H.measure.restrict (Set.Ioc 0 1) = volume.restrict (Set.Ioc 0 1) := by
    rw [g79s_restrict_eq H StieltjesFunction.id 0 1 (fun x hx => by rw [hH x hx]; rfl),
      ← Real.volume_eq_stieltjes_id]
  have hE : ∫ x, x ∂μ = ∫ p in Set.Ioc (0 : ℝ) 1, quantileFunction μ p := by
    have := (g79n_E μ (fun x => x) measurable_id hint).2
    rw [this, intervalIntegral.integral_of_le zero_le_one]
    rfl
  refine ⟨?_, hE, ?_⟩
  · unfold distortionFunctional
    rw [hm, hE]
  · -- layer cake
    have hpos : Integrable (fun x : ℝ => max x 0) μ := hint.pos_part
    have hneg : Integrable (fun x : ℝ => max (-x) 0) μ := hint.neg.pos_part
    have hsplit : ∫ x, x ∂μ = ∫ x, max x 0 ∂μ - ∫ x, max (-x) 0 ∂μ := by
      rw [← integral_sub hpos hneg]
      congr 1; funext x; rw [max_zero_sub_max_neg_zero_eq_self]
    have h1 : ∫ x, max x 0 ∂μ = ∫ u in Set.Ioi (0 : ℝ), (1 - distributionFunction μ u) := by
      rw [hpos.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun x => le_max_right _ _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : (0:ℝ) < t := ht
      have e : {a : ℝ | t < max a 0} = Set.Ioi t := by
        ext a; simp only [Set.mem_setOf_eq, Set.mem_Ioi, lt_max_iff]
        constructor
        · rintro (h | h)
          · exact h
          · linarith
        · exact Or.inl
      show μ.real {a : ℝ | t < max a 0} = 1 - μ.real (Set.Iic t)
      rw [e, ← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
    have h2 : ∫ x, max (-x) 0 ∂μ = ∫ u in Set.Iic (0 : ℝ), distributionFunction μ u := by
      rw [hneg.integral_eq_integral_meas_le (Filter.Eventually.of_forall fun x => le_max_right _ _)]
      rw [show Set.Iic (0:ℝ) = Set.Iic (-0) by rw [neg_zero], ← integral_comp_neg_Ioi]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : (0:ℝ) < t := ht
      have e : {a : ℝ | t ≤ max (-a) 0} = Set.Iic (-t) := by
        ext a; simp only [Set.mem_setOf_eq, Set.mem_Iic, le_max_iff]
        constructor
        · rintro (h | h)
          · linarith
          · linarith
        · intro h; exact Or.inl (by linarith)
      show μ.real {a : ℝ | t ≤ max (-a) 0} = μ.real (Set.Iic (-t))
      rw [e]
    rw [hsplit, h1, h2]; ring

theorem g79s_part2 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = if α ≤ p then 1 else 0) →
        distortionFunctional H μ = quantileFunction μ α) := by
  intro α ha0 ha1 H hH
  have hm : H.measure.restrict (Set.Ioc 0 1) = Measure.dirac α := by
    apply Measure.ext_of_Ioc
    intro a b hab
    rw [Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc,
      Measure.dirac_apply' _ measurableSet_Ioc]
    rcases le_or_gt (a ⊔ 0) (b ⊓ 1) with h | h
    · rw [StieltjesFunction.measure_Ioc, hH _ ⟨le_sup_right.trans h, inf_le_right⟩,
        hH _ ⟨le_sup_right, h.trans inf_le_right⟩]
      by_cases h1 : α ≤ b ⊓ 1 <;> by_cases h2 : α ≤ a ⊔ 0
      · rw [if_pos h1, if_pos h2, Set.indicator_of_notMem]; · simp
        intro hm; exact absurd h2 (not_le.mpr (sup_lt_iff.mpr ⟨hm.1, ha0⟩))
      · rw [if_pos h1, if_neg h2, Set.indicator_of_mem]; · simp
        exact ⟨lt_of_le_of_lt le_sup_left (lt_of_not_ge h2), h1.trans inf_le_left⟩
      · exfalso; exact h1 (h2.trans h)
      · rw [if_neg h1, if_neg h2, Set.indicator_of_notMem]; · simp
        intro hm; exact h1 (le_inf hm.2 ha1)
    · rw [Set.Ioc_eq_empty (not_lt.mpr h.le), measure_empty, Set.indicator_of_notMem]
      intro hm
      have : a ⊔ 0 < α := sup_lt_iff.mpr ⟨hm.1, ha0⟩
      have : α ≤ b ⊓ 1 := le_inf hm.2 ha1
      linarith
  unfold distortionFunctional
  rw [hm, integral_dirac]

noncomputable def g79s_lin (α : ℝ) (ha : 0 < α) : StieltjesFunction ℝ where
  toFun := fun x => x / α
  mono' := fun x y hxy => div_le_div_of_nonneg_right hxy ha.le
  right_continuous' := fun x => (continuous_id.div_const α).continuousWithinAt

theorem g79s_lin_measure (α : ℝ) (ha : 0 < α) :
    (g79s_lin α ha).measure = ENNReal.ofReal (1 / α) • volume := by
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [StieltjesFunction.measure_Ioc, Measure.smul_apply, Real.volume_Ioc, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  show b / α - a / α = 1 / α * (b - a)
  field_simp

theorem g79s_part3 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = min (p / α) 1) →
        distortionFunctional H μ = averageValueAtRisk μ α) := by
  intro α ha0 ha1 H hH
  have hsplit : Set.Ioc (0:ℝ) 1 = Set.Ioc 0 α ∪ Set.Ioc α 1 :=
    (Set.Ioc_union_Ioc_eq_Ioc ha0.le ha1).symm
  have hz : H.measure (Set.Ioc α 1) = 0 := by
    rw [StieltjesFunction.measure_Ioc, hH 1 ⟨zero_le_one, le_rfl⟩, hH α ⟨ha0.le, ha1⟩,
      div_self ha0.ne', min_self, min_eq_right ((one_le_div ha0).mpr ha1)]
    simp
  have hr : H.measure.restrict (Set.Ioc 0 1) = H.measure.restrict (Set.Ioc 0 α) := by
    rw [hsplit, Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.restrict_eq_zero.mpr hz, add_zero]
  have hG : H.measure.restrict (Set.Ioc 0 α) = (g79s_lin α ha0).measure.restrict (Set.Ioc 0 α) := by
    apply g79s_restrict_eq
    intro x hx
    rw [hH x ⟨hx.1, hx.2.trans ha1⟩, min_eq_left ((div_le_one ha0).mpr hx.2)]
    rfl
  unfold distortionFunctional averageValueAtRisk
  rw [hr, hG, g79s_lin_measure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

open MeasureTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    -- (i) H(p) = p: the expectation
    (Integrable (fun x : ℝ => x) μ → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = p) →
        distortionFunctional H μ = ∫ x, x ∂μ ∧
        ∫ x, x ∂μ = ∫ p in Set.Ioc (0 : ℝ) 1, quantileFunction μ p ∧
        ∫ x, x ∂μ = -(∫ u in Set.Iic (0 : ℝ), distributionFunction μ u) +
          ∫ u in Set.Ioi (0 : ℝ), (1 - distributionFunction μ u)) ∧
    -- (ii) H(p) = 𝟙_{[α,1]}(p): the value-at-risk
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = if α ≤ p then 1 else 0) →
        distortionFunctional H μ = quantileFunction μ α) ∧
    -- (iii) H(p) = min(p/α, 1): the average value-at-risk
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = min (p / α) 1) →
        distortionFunctional H μ = averageValueAtRisk μ α) := ⟨g79s_part1 μ, g79s_part2 μ, g79s_part3 μ⟩
