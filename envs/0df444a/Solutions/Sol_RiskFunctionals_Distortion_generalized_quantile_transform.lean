-- Prove2me | solution 1 for RiskFunctionals.Distortion.generalized_quantile_transform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:03:29.90368+00:00
-- url     : https://prove2.me/submissions/9353f125-3962-4345-a0c5-e23f05e6372d

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_Orders

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

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
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
