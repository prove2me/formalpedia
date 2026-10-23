-- Prove2me | solution 1 for RiskFunctionals.Distortion.choquet_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:15:07.903982+00:00
-- url     : https://prove2.me/submissions/a1bdb81a-63d2-49d5-9d80-d155bfe49e3b

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional
import Definitions.Def_RiskFunctionals_Distortion_Orders
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

/-- The quantile point `y*` for a level `w ∈ (0,1)`. -/
theorem g81q_star (μ : Measure ℝ) [IsProbabilityMeasure μ] {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    ∃ y0 : ℝ, w ≤ μ.real (Iic y0) ∧ μ.real (Iio y0) ≤ w ∧ ∀ y < y0, μ.real (Iic y) < w := by
  set S := {y : ℝ | w ≤ cdf μ y}
  have hne : S.Nonempty := by
    have := (tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hw1)
    obtain ⟨a, ha⟩ := this.exists_forall_of_atTop
    exact ⟨a, (ha a le_rfl).le⟩
  have hbdd : BddBelow S := by
    have := (tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hw0)
    obtain ⟨b, hb⟩ := Filter.eventually_atBot.1 this
    refine ⟨b, fun y hy => ?_⟩
    by_contra h; push Not at h
    have := hb y h.le; simp only [S, mem_ofPred_eq] at hy; linarith
  set y0 := sInf S
  have hlt : ∀ y < y0, μ.real (Iic y) < w := by
    intro y hy
    rw [← cdf_eq_real]
    by_contra h; push Not at h
    exact absurd (csInf_le hbdd h) (not_le.2 hy)
  refine ⟨y0, ?_, ?_, hlt⟩
  · rw [← cdf_eq_real]
    have hc : Tendsto (cdf μ) (𝓝[>] y0) (𝓝 (cdf μ y0)) :=
      ((cdf μ).right_continuous y0).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine ge_of_tendsto hc ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt hne hy
    exact le_trans hs ((monotone_cdf μ) hsy.le)
  · -- `μ (Iio y0) = lim μ (Iic (y0 - 1/(n+1)))`
    have hU : Iio y0 = ⋃ n : ℕ, Iic (y0 - 1 / ((n : ℝ) + 1)) := by
      ext y; simp only [mem_Iio, mem_iUnion, mem_Iic]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hmono : Monotone (fun n : ℕ => Iic (y0 - 1 / ((n : ℝ) + 1))) := by
      intro m n hmn
      apply Iic_subset_Iic.2
      have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      linarith
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [← hU] at ht
    have hle : μ (Iio y0) ≤ ENNReal.ofReal w := by
      refine le_of_tendsto' ht fun n => ?_
      have := hlt (y0 - 1 / ((n : ℝ) + 1)) (by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
      simp only [Function.comp_apply]
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal this.le
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hle

/-- The randomized distributional transform on the joint space. -/
noncomputable def g81q_phi (μ : Measure ℝ) (p : ℝ × ℝ) : ℝ :=
  μ.real (Iio p.1) + p.2 * (μ.real (Iic p.1) - μ.real (Iio p.1))

theorem g81q_split (μ : Measure ℝ) [IsFiniteMeasure μ] (y : ℝ) :
    μ.real (Iic y) = μ.real (Iio y) + μ.real {y} := by
  have := measureReal_union (μ := μ) (s₁ := Iio y) (s₂ := {y})
    (Set.disjoint_singleton_right.2 (lt_irrefl y)) (measurableSet_singleton y)
  rw [Iio_union_right] at this
  exact this

theorem g81q_vol_Icc (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    volume.restrict (Icc (0:ℝ) 1) (Icc 0 a) = ENNReal.ofReal a := by
  rw [Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc, max_self, min_eq_left ha1,
    Real.volume_Icc, sub_zero]

theorem g81q_vol_Ico (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    volume.restrict (Icc (0:ℝ) 1) (Ico 0 a) = ENNReal.ofReal a := by
  rw [Measure.restrict_apply measurableSet_Ico]
  have : Ico 0 a ∩ Icc (0:ℝ) 1 = Ico 0 a := by
    ext u; simp only [mem_inter_iff, mem_Ico, mem_Icc]; constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, h.1, by linarith [h.2]⟩
  rw [this, Real.volume_Ico, sub_zero]

/-- slice where the whole unit interval is below `w`. -/
theorem g81q_s1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (y w : ℝ) (h : μ.real (Iic y) < w) :
    volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) ≤ w} = 1 ∧
    volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) < w} = 1 := by
  have hd : 0 ≤ μ.real (Iic y) - μ.real (Iio y) := by
    rw [g81q_split]; simp [measureReal_nonneg]
  have key : ∀ u ∈ Icc (0:ℝ) 1, g81q_phi μ (y, u) < w := by
    intro u hu
    simp only [g81q_phi]
    nlinarith [hu.1, hu.2]
  have h1 : volume.restrict (Icc (0:ℝ) 1) univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]; simp
  have e1 : {u | g81q_phi μ (y, u) ≤ w} ∩ Icc (0:ℝ) 1 = Icc 0 1 :=
    inter_eq_right.2 (fun u hu => (key u hu).le)
  have e2 : {u | g81q_phi μ (y, u) < w} ∩ Icc (0:ℝ) 1 = Icc 0 1 :=
    inter_eq_right.2 (fun u hu => key u hu)
  constructor
  · rw [Measure.restrict_apply' measurableSet_Icc, e1]
    rw [← h1, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  · rw [Measure.restrict_apply' measurableSet_Icc, e2]
    rw [← h1, Measure.restrict_apply MeasurableSet.univ, univ_inter]

/-- slice at an atom containing level `w`. -/
theorem g81q_s2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (y w : ℝ) (hd : 0 < μ.real {y})
    (h1 : μ.real (Iio y) ≤ w) (h2 : w ≤ μ.real (Iic y)) :
    volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) ≤ w} =
        ENNReal.ofReal ((w - μ.real (Iio y)) / μ.real {y}) ∧
    volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) < w} =
        ENNReal.ofReal ((w - μ.real (Iio y)) / μ.real {y}) := by
  have hs := g81q_split μ y
  set a := μ.real (Iio y)
  set d := μ.real {y}
  have hq0 : 0 ≤ (w - a) / d := div_nonneg (by linarith) hd.le
  have hq1 : (w - a) / d ≤ 1 := by rw [div_le_one hd]; linarith
  have hphi : ∀ u, g81q_phi μ (y, u) = a + u * d := by
    intro u; simp only [g81q_phi, a, d]; rw [hs]; ring
  have iff1 : ∀ u, a + u * d ≤ w ↔ u ≤ (w - a) / d := by
    intro u; rw [le_div_iff₀ hd]; constructor <;> intro h <;> linarith
  have iff2 : ∀ u, a + u * d < w ↔ u < (w - a) / d := by
    intro u; rw [lt_div_iff₀ hd]; constructor <;> intro h <;> linarith
  constructor
  · rw [Measure.restrict_apply' measurableSet_Icc, ← g81q_vol_Icc _ hq0 hq1,
      Measure.restrict_apply' measurableSet_Icc]
    congr 1; ext u
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, hphi, iff1]
    constructor
    · rintro ⟨h, h0, -⟩; exact ⟨⟨h0, h⟩, h0, by linarith⟩
    · rintro ⟨⟨h0, h⟩, -, h1'⟩; exact ⟨h, h0, h1'⟩
  · rw [Measure.restrict_apply' measurableSet_Icc, ← g81q_vol_Ico _ hq0 hq1,
      Measure.restrict_apply' measurableSet_Icc]
    congr 1; ext u
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_Ico, hphi, iff2]
    constructor
    · rintro ⟨h, h0, -⟩; exact ⟨⟨h0, h⟩, h0, by linarith⟩
    · rintro ⟨⟨h0, h⟩, -, h1'⟩; exact ⟨h, h0, h1'⟩

/-- slice entirely above `w`. -/
theorem g81q_s3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (y w : ℝ) (h : w ≤ μ.real (Iio y)) :
    volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) < w} = 0 := by
  have hd : 0 ≤ μ.real (Iic y) - μ.real (Iio y) := by
    rw [g81q_split]; simp [measureReal_nonneg]
  rw [Measure.restrict_apply' measurableSet_Icc]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext u; simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_empty_iff_false, iff_false]
  rintro ⟨h1, h0, -⟩
  simp only [g81q_phi] at h1
  nlinarith

theorem g81q_univ : volume.restrict (Icc (0:ℝ) 1) univ = 1 := by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]; simp

theorem g81q_atom_sum (μ : Measure ℝ) [IsProbabilityMeasure μ] (y0 w : ℝ) (hd : 0 < μ.real {y0})
    (hw : μ.real (Iio y0) ≤ w) :
    μ (Iio y0) + ENNReal.ofReal ((w - μ.real (Iio y0)) / μ.real {y0}) * μ {y0} = ENNReal.ofReal w := by
  rw [← ofReal_measureReal (measure_ne_top μ (Iio y0)), ← ofReal_measureReal (measure_ne_top μ {y0}),
    ← ENNReal.ofReal_mul (div_nonneg (by linarith) hd.le), ← ENNReal.ofReal_add measureReal_nonneg
      (mul_nonneg (div_nonneg (by linarith) hd.le) hd.le)]
  congr 1
  field_simp
  ring

theorem g81q_A (μ : Measure ℝ) [IsProbabilityMeasure μ] {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    ENNReal.ofReal w ≤ ∫⁻ y, volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) ≤ w} ∂μ := by
  obtain ⟨y0, h1, h2, hlt⟩ := g81q_star μ hw0 hw1
  set g : ℝ → ENNReal := fun y => volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) ≤ w}
  have hs := g81q_split μ y0
  calc ENNReal.ofReal w ≤ μ (Iio y0) + g y0 * μ {y0} := by
        rcases eq_or_lt_of_le (measureReal_nonneg (μ := μ) (s := {y0})) with hd | hd
        · have : μ.real (Iio y0) = w := by linarith
          rw [← this, ofReal_measureReal (measure_ne_top _ _)]; exact le_self_add
        · rw [show g y0 = _ from (g81q_s2 μ y0 w hd h2 h1).1, g81q_atom_sum μ y0 w hd h2]
    _ = ∫⁻ y in Iio y0, g y ∂μ + ∫⁻ y in {y0}, g y ∂μ := by
        rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 1)
          (fun y hy => (g81q_s1 μ y w (hlt y hy)).1), setLIntegral_const, one_mul, lintegral_singleton]
    _ = ∫⁻ y in Iic y0, g y ∂μ := by
        rw [← lintegral_union (measurableSet_singleton _)
          (show Disjoint (Iio y0) {y0} by simp), Iio_union_right]
    _ ≤ ∫⁻ y, g y ∂μ := setLIntegral_le_lintegral _ _

theorem g81q_B (μ : Measure ℝ) [IsProbabilityMeasure μ] {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    ∫⁻ y, volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) < w} ∂μ ≤ ENNReal.ofReal w := by
  obtain ⟨y0, h1, h2, hlt⟩ := g81q_star μ hw0 hw1
  set g : ℝ → ENNReal := fun y => volume.restrict (Icc (0:ℝ) 1) {u | g81q_phi μ (y, u) < w}
  have hs := g81q_split μ y0
  have hg1 : ∀ y, g y ≤ 1 := fun y => (measure_mono (subset_univ _)).trans_eq g81q_univ
  have hzero : ∫⁻ y in (Iic y0)ᶜ, g y ∂μ = 0 := by
    rw [compl_Iic]
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) (fun y hy =>
      g81q_s3 μ y w (h1.trans (measureReal_mono (Iic_subset_Iio.2 hy))))]
    simp
  rw [← lintegral_add_compl _ measurableSet_Iic, hzero, add_zero, ← Iio_union_right,
    lintegral_union (measurableSet_singleton _) (show Disjoint (Iio y0) {y0} by simp),
    lintegral_singleton]
  have hIio : ∫⁻ y in Iio y0, g y ∂μ ≤ μ (Iio y0) := by
    calc ∫⁻ y in Iio y0, g y ∂μ ≤ ∫⁻ y in Iio y0, 1 ∂μ := lintegral_mono hg1
      _ = μ (Iio y0) := by rw [setLIntegral_const, one_mul]
  rcases eq_or_lt_of_le (measureReal_nonneg (μ := μ) (s := {y0})) with hd | hd
  · have hz : μ {y0} = 0 := by
      rw [← ofReal_measureReal (measure_ne_top _ _), ← hd, ENNReal.ofReal_zero]
    rw [hz, mul_zero, add_zero]
    refine hIio.trans ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h2
  · calc ∫⁻ y in Iio y0, g y ∂μ + g y0 * μ {y0} ≤ μ (Iio y0) + g y0 * μ {y0} := by gcongr
      _ = ENNReal.ofReal w := by
          rw [show g y0 = _ from (g81q_s2 μ y0 w hd h2 h1).2, g81q_atom_sum μ y0 w hd h2]

theorem g81q_phi_meas (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measurable (g81q_phi μ) := by
  have hF : Measurable (fun y : ℝ => μ.real (Iic y)) :=
    Monotone.measurable fun a b h => measureReal_mono (Iic_subset_Iic.2 h)
  have hL : Measurable (fun y : ℝ => μ.real (Iio y)) :=
    Monotone.measurable fun a b h => measureReal_mono (Iio_subset_Iio h)
  unfold g81q_phi
  exact (hL.comp measurable_fst).add (measurable_snd.mul ((hF.comp measurable_fst).sub (hL.comp measurable_fst)))

theorem g81q_squeeze (I : ENNReal) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hI1 : I ≤ 1)
    (hup : ∀ w', 0 < w' → w' < 1 → x < w' → I ≤ ENNReal.ofReal w')
    (hlo : ∀ w'', 0 < w'' → w'' < 1 → w'' ≤ x → ENNReal.ofReal w'' ≤ I) :
    I = ENNReal.ofReal x := by
  have hIt : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hI1
  have ht1 : I.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hI1; simpa using this
  have ht0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hIt]
  congr 1
  apply le_antisymm
  · by_contra h; push Not at h
    rcases eq_or_lt_of_le hx1 with hx | hx
    · linarith
    have := ENNReal.toReal_le_of_le_ofReal (by linarith)
      (hup ((x + I.toReal) / 2) (by linarith) (by linarith) (by linarith))
    linarith
  · by_contra h; push Not at h
    have := (ENNReal.ofReal_le_iff_le_toReal hIt).1
      (hlo ((I.toReal + x) / 2) (by linarith) (by linarith) (by linarith))
    linarith

theorem g81q_main (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (μ.prod (volume.restrict (Icc (0:ℝ) 1))).map (g81q_phi μ) = volume.restrict (Icc (0:ℝ) 1) := by
  set ν := volume.restrict (Icc (0:ℝ) 1)
  have hφ := g81q_phi_meas μ
  haveI : IsProbabilityMeasure ν := ⟨g81q_univ⟩
  have hI : ∀ w, (μ.prod ν).map (g81q_phi μ) (Iic w) = ∫⁻ y, ν {u | g81q_phi μ (y, u) ≤ w} ∂μ := by
    intro w
    rw [Measure.map_apply hφ measurableSet_Iic, Measure.prod_apply (hφ measurableSet_Iic)]
    rfl
  have hJ : ∀ w, (μ.prod ν).map (g81q_phi μ) (Iio w) = ∫⁻ y, ν {u | g81q_phi μ (y, u) < w} ∂μ := by
    intro w
    rw [Measure.map_apply hφ measurableSet_Iio, Measure.prod_apply (hφ measurableSet_Iio)]
    rfl
  set M := (μ.prod ν).map (g81q_phi μ)
  haveI : IsProbabilityMeasure M := Measure.isProbabilityMeasure_map hφ.aemeasurable
  have hup : ∀ w w', 0 < w' → w' < 1 → w < w' → M (Iic w) ≤ ENNReal.ofReal w' := by
    intro w w' h0 h1 hww
    calc M (Iic w) ≤ M (Iio w') := measure_mono (Iic_subset_Iio.2 hww)
      _ ≤ _ := by rw [hJ]; exact g81q_B μ h0 h1
  have hlo : ∀ w w'', 0 < w'' → w'' < 1 → w'' ≤ w → ENNReal.ofReal w'' ≤ M (Iic w) := by
    intro w w'' h0 h1 hww
    calc ENNReal.ofReal w'' ≤ M (Iic w'') := by rw [hI]; exact g81q_A μ h0 h1
      _ ≤ M (Iic w) := measure_mono (Iic_subset_Iic.2 hww)
  have hM1 : ∀ w, M (Iic w) ≤ 1 := fun w => prob_le_one
  have hval : ∀ x, 0 ≤ x → x ≤ 1 → M (Iic x) = ENNReal.ofReal x := fun x h0 h1 =>
    g81q_squeeze _ x h0 h1 (hM1 x) (fun w' a b c => hup x w' a b c) (fun w'' a b c => hlo x w'' a b c)
  refine Measure.ext_of_Iic _ _ fun w => ?_
  rw [Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge w 0 with hw | hw
  · have h0 : M (Iic w) = 0 := by
      apply le_antisymm _ (zero_le)
      calc M (Iic w) ≤ M (Iic 0) := measure_mono (Iic_subset_Iic.2 hw.le)
        _ = 0 := by rw [hval 0 le_rfl zero_le_one, ENNReal.ofReal_zero]
    rw [h0]
    have : Iic w ∩ Icc (0:ℝ) 1 = ∅ := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩; linarith
    rw [this, measure_empty]
  rcases le_or_gt w 1 with hw1 | hw1
  · rw [hval w hw hw1]
    have : Iic w ∩ Icc (0:ℝ) 1 = Icc 0 w := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [this, Real.volume_Icc, sub_zero]
  · have h1 : M (Iic w) = 1 := by
      apply le_antisymm (hM1 w)
      calc (1 : ENNReal) = M (Iic 1) := by rw [hval 1 zero_le_one le_rfl, ENNReal.ofReal_one]
        _ ≤ M (Iic w) := measure_mono (Iic_subset_Iic.2 hw1.le)
    rw [h1]
    have : Iic w ∩ Icc (0:ℝ) 1 = Icc 0 1 := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1', h2⟩; exact ⟨by linarith, h1', h2⟩

    rw [this, Real.volume_Icc]; simp

open MeasureTheory ProbabilityTheory Set RiskFunctionals.Distortion

theorem g82_unif {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y U : Ω → ℝ) (hY : Measurable Y) (hU : IsUniform01 P U)
    (hind : IndepFun Y U P) :
    (∀ ω, distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω)) =
      (1 - U ω) * distributionFunctionLeft (P.map Y) (Y ω) +
        U ω * distributionFunction (P.map Y) (Y ω)) ∧
    IsUniform01 P (fun ω => distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω))) := by
  refine ⟨fun ω => by ring, ?_⟩
  set μ := P.map Y
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hW : (fun ω => distributionFunction μ (Y ω) -
        (1 - U ω) * (distributionFunction μ (Y ω) - distributionFunctionLeft μ (Y ω))) =
      g81q_phi μ ∘ (fun ω => (Y ω, U ω)) := by
    funext ω
    simp only [Function.comp_apply, g81q_phi, distributionFunction, distributionFunctionLeft]
    ring
  rw [hW]
  have hYU : Measurable (fun ω => (Y ω, U ω)) := hY.prodMk hU.1
  refine ⟨(g81q_phi_meas μ).comp hYU, ?_⟩
  rw [← Measure.map_map (g81q_phi_meas μ) hYU,
    (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hU.1.aemeasurable).1 hind, hU.2]
  exact g81q_main μ


open MeasureTheory ProbabilityTheory Set Filter Topology RiskFunctionals.Distortion
open scoped ENNReal NNReal

theorem solution (H : StieltjesFunction ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hG : InDistortionDomain H μ) :
    IntegrableOn (fun u => H (distributionFunction μ u)) (Set.Iic (0 : ℝ)) ∧
    IntegrableOn (fun u => distortionBar H (1 - distributionFunction μ u)) (Set.Ioi (0 : ℝ)) ∧
    distortionFunctional H μ =
      -(∫ u in Set.Iic (0 : ℝ), H (distributionFunction μ u)) +
        ∫ u in Set.Ioi (0 : ℝ), distortionBar H (1 - distributionFunction μ u) := by
  obtain ⟨hH0, hqi, hat⟩ := hG
  set G := distributionFunction μ with hGdef
  set q : ℝ → ℝ := quantileFunction μ with hq
  set ν := H.measure.restrict (Ioc 0 1) with hν
  have hqm : Measurable q := g79q_meas μ
  have hGm : Monotone G := g79q_mono μ
  have hG0 : ∀ u, 0 ≤ G u := fun u => measureReal_nonneg
  have hG1 : ∀ u, G u ≤ 1 := fun u => measureReal_le_one
  have hHG0 : ∀ u, 0 ≤ H (G u) := fun u => hH0 ▸ H.mono (hG0 u)
  have hνu : ν univ = ENNReal.ofReal (H 1) := by
    rw [hν, Measure.restrict_apply MeasurableSet.univ, univ_inter, StieltjesFunction.measure_Ioc,
      hH0, sub_zero]
  haveI : IsFiniteMeasure ν := ⟨by rw [hνu]; exact ENNReal.ofReal_lt_top⟩
  have hgal : ∀ᵐ p ∂ν, p ∈ Ioc (0:ℝ) 1 ∧ ∃ v, p ≤ G v := by
    by_cases h1 : H.measure {1} = 0
    · have : ∀ᵐ p ∂ν, p ≠ 1 := by
        rw [ae_iff]
        simp only [ne_eq, not_not, setOf_eq_eq_singleton]
        exact le_antisymm ((Measure.restrict_apply_le _ _).trans h1.le) bot_le
      filter_upwards [ae_restrict_mem measurableSet_Ioc, this] with p hp hp1
      exact ⟨hp, g79q_wit μ (lt_of_le_of_ne hp.2 hp1)⟩
    · obtain ⟨v, hv⟩ := hat h1
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
      exact ⟨hp, v, hp.2.trans hv⟩
  have hle : ∀ u, ν {p | q p ≤ u} = ENNReal.ofReal (H (G u)) := by
    intro u
    have hset : {p | q p ≤ u} =ᵐ[ν] Iic (G u) := by
      filter_upwards [hgal] with p hp
      exact propext (g79q_qle μ p u hp.1.1 hp.2)
    rw [measure_congr hset, hν, Measure.restrict_apply measurableSet_Iic,
      show Iic (G u) ∩ Ioc 0 1 = Ioc 0 (G u) by
        ext p; simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans (hG1 u)⟩,
      StieltjesFunction.measure_Ioc, hH0, sub_zero]
  have hlt : ∀ u, ν {p | u < q p} = ENNReal.ofReal (H 1 - H (G u)) := by
    intro u
    have : {p | u < q p} = {p | q p ≤ u}ᶜ := by ext p; simp
    rw [this, measure_compl (measurableSet_le hqm measurable_const) (measure_ne_top _ _), hνu, hle u,
      ENNReal.ofReal_sub _ (hHG0 u)]
  have hHGm : Measurable fun u => H (G u) := (H.mono.comp hGm).measurable
  -- positive part
  have hpos : ∫⁻ p, ENNReal.ofReal (q p) ∂ν =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (H 1 - H (G t)) := by
    have := lintegral_eq_lintegral_meas_lt ν (f := fun p => max (q p) 0)
      (ae_of_all _ fun p => le_max_right _ _) (hqm.max measurable_const).aemeasurable
    have e1 : (fun p => ENNReal.ofReal (max (q p) 0)) = fun p => ENNReal.ofReal (q p) := by
      funext p; rcases le_total (q p) 0 with h | h
      · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
      · rw [max_eq_left h]
    rw [e1] at this
    rw [this]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [← hlt t]
    congr 1; ext a
    simp only [mem_setOf_eq, lt_max_iff, or_iff_left (not_lt.2 (show (0:ℝ) < t from ht).le)]
  -- negative part
  have hneg : ∫⁻ p, ENNReal.ofReal (-q p) ∂ν = ∫⁻ u in Iic 0, ENNReal.ofReal (H (G u)) := by
    have := lintegral_eq_lintegral_meas_le ν (f := fun p => max (-q p) 0)
      (ae_of_all _ fun p => le_max_right _ _) (hqm.neg.max measurable_const).aemeasurable
    have e1 : (fun p => ENNReal.ofReal (max (-q p) 0)) = fun p => ENNReal.ofReal (-q p) := by
      funext p; rcases le_total (-q p) 0 with h | h
      · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
      · rw [max_eq_left h]
    rw [e1] at this
    rw [this]
    have e2 : ∫⁻ t in Ioi 0, ν {a | t ≤ max (-q a) 0} =
        ∫⁻ t in Ioi 0, ENNReal.ofReal (H (G (-t))) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [← hle (-t)]
      congr 1; ext a
      simp only [mem_setOf_eq, le_max_iff, or_iff_left (not_le.2 (show (0:ℝ) < t from ht))]
      constructor <;> intro h <;> linarith
    rw [e2, setLIntegral_congr Iio_ae_eq_Iic.symm]
    have hFm : Measurable fun u => ENNReal.ofReal (H (G u)) := ENNReal.measurable_ofReal.comp hHGm
    conv_rhs => rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    rw [setLIntegral_map measurableSet_Iio hFm measurable_neg]
    congr 1
    · ext x; simp
  have hfin1 : ∫⁻ p, ENNReal.ofReal (q p) ∂ν ≠ ∞ := (Integrable.lintegral_lt_top hqi).ne
  have hfin2 : ∫⁻ p, ENNReal.ofReal (-q p) ∂ν ≠ ∞ := (Integrable.lintegral_lt_top hqi.neg).ne
  have hbar : (fun u => distortionBar H (1 - G u)) = fun u => H 1 - H (G u) := by
    funext u; simp [distortionBar]
  have hbarnn : ∀ u, 0 ≤ H 1 - H (G u) := fun u => sub_nonneg.2 (H.mono (hG1 u))
  have hI1 : IntegrableOn (fun u => H (G u)) (Iic 0) :=
    (lintegral_ofReal_ne_top_iff_integrable hHGm.aestronglyMeasurable
      (ae_of_all _ hHG0)).1 (hneg ▸ hfin2)
  have hI2 : IntegrableOn (fun u => H 1 - H (G u)) (Ioi 0) :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_const.sub hHGm).aestronglyMeasurable
      (ae_of_all _ hbarnn)).1 (hpos ▸ hfin1)
  refine ⟨hI1, hbar ▸ hI2, ?_⟩
  rw [hbar, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hHG0) hHGm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hbarnn)
      (measurable_const.sub hHGm).aestronglyMeasurable, ← hpos, ← hneg]
  show ∫ p, q p ∂ν = _
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hqi]
  ring
