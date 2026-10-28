-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P15.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:40:48.38578+00:00
-- url     : https://prove2.me/submissions/de81ea42-a841-4591-9ea7-d499298121c9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction Topology

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

theorem S200P_attain (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (θ : ℝ) : ∃ u ∈ Set.Icc a b, legendre a b e θ = θ * u - e u := by
  have h := (isCompact_Icc.image_of_continuousOn
    ((continuousOn_const.mul continuousOn_id).sub hcont : ContinuousOn (fun s : ℝ => θ * s - e s) _)).sSup_mem
    ((Set.nonempty_Icc.mpr hab.le).image _)
  obtain ⟨u, hu, h2⟩ := h
  exact ⟨u, hu, h2.symm⟩

theorem S200P_meas (E : FiniteExperiment) (s : ℝ) :
    @Measurable E.Space ℝ≥0∞ E.measurableSpace _
      (fun x => ENNReal.ofReal (Real.exp (s * E.observable x))) := by
  letI := E.measurableSpace
  exact ((E.measurable_observable.const_mul s).exp).ennreal_ofReal

theorem S200P_M_ne_zero (E : FiniteExperiment) (s : ℝ) : exponentialMoment E s ≠ 0 := by
  letI := E.measurableSpace
  intro h
  unfold exponentialMoment at h
  rw [lintegral_eq_zero_iff (S200P_meas E s)] at h
  have : ∀ᵐ x ∂E.measure, False := by
    filter_upwards [h] with x hx
    have : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (s * E.observable x)) :=
      ENNReal.ofReal_pos.2 (Real.exp_pos _)
    simp only [Pi.zero_apply] at hx
    rw [hx] at this
    exact lt_irrefl _ this
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this
  exact E.nonzero_mass (by rw [this]; simp)

theorem S200P_markov (E : FiniteExperiment) (A : Set E.Space) (s c : ℝ)
    (hA : ∀ x ∈ A, c ≤ s * E.observable x) :
    E.measure A ≤ ENNReal.ofReal (Real.exp (-c)) * exponentialMoment E s := by
  letI := E.measurableSpace
  calc E.measure A = ∫⁻ _ in A, 1 ∂E.measure := (setLIntegral_one A).symm
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp (-c)) *
          ENNReal.ofReal (Real.exp (s * E.observable x)) ∂E.measure := by
        apply setLIntegral_mono ((S200P_meas E s).const_mul _)
        intro x hx
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        exact ENNReal.one_le_ofReal.2 (Real.one_le_exp (by linarith [hA x hx]))
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (-c)) *
          ENNReal.ofReal (Real.exp (s * E.observable x)) ∂E.measure :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (Real.exp (-c)) * exponentialMoment E s :=
        lintegral_const_mul _ (S200P_meas E s)

theorem S200P_moment_real (F : LDFamily) (s : ℝ) (t : F.index)
    (hM : exponentialMoment (F.experiment t) s ≠ ⊤) :
    scaledMoment F s t =
      (((F.weight t)⁻¹ * Real.log (exponentialMoment (F.experiment t) s).toReal : ℝ) : EReal) := by
  unfold scaledMoment
  rw [ENNReal.log_pos_real (S200P_M_ne_zero _ s) hM, EReal.coe_mul]

theorem S200P_idx (F : LDFamily) (A : ∀ t : F.index, Set (F.experiment t).Space) (s θ : ℝ)
    (hA : ∀ t, ∀ x ∈ A t, s * θ * F.weight t ≤ s * (F.experiment t).observable x)
    (t : F.index) :
    scaledEvent F A t ≤ ((-(s * θ) : ℝ) : EReal) + scaledMoment F s t := by
  have hw : 0 < F.weight t := F.weight_positive t
  have hwi : 0 < (F.weight t)⁻¹ := inv_pos.2 hw
  set M := exponentialMoment (F.experiment t) s with hMdef
  by_cases hM : M = ⊤
  · have : scaledMoment F s t = ⊤ := by
      unfold scaledMoment; rw [← hMdef, hM, ENNReal.log_top, EReal.coe_mul_top_of_pos hwi]
    rw [this, EReal.coe_add_top]; exact le_top
  rw [S200P_moment_real F s t hM]
  set μA := (F.experiment t).measure (A t) with hμAdef
  by_cases hμ : μA = 0
  · have : scaledEvent F A t = ⊥ := by
      unfold scaledEvent; rw [← hμAdef, hμ, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hwi]
    rw [this]; exact bot_le
  have hμt : μA ≠ ⊤ := ne_top_of_le_ne_top (F.experiment t).finite_mass.ne (measure_mono (Set.subset_univ _))
  have hev : scaledEvent F A t = (((F.weight t)⁻¹ * Real.log μA.toReal : ℝ) : EReal) := by
    unfold scaledEvent; rw [← hμAdef, ENNReal.log_pos_real hμ hμt, EReal.coe_mul]
  rw [hev, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hmk := S200P_markov (F.experiment t) (A t) s (s * θ * F.weight t) (hA t)
  have hM0 : M ≠ 0 := S200P_M_ne_zero _ s
  have hMpos : 0 < M.toReal := ENNReal.toReal_pos hM0 hM
  have hμpos : 0 < μA.toReal := ENNReal.toReal_pos hμ hμt
  have h1 : μA.toReal ≤ Real.exp (-(s * θ * F.weight t)) * M.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) hmk
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have h2 : Real.log μA.toReal ≤ -(s * θ * F.weight t) + Real.log M.toReal := by
    have := Real.log_le_log hμpos h1
    rwa [Real.log_mul (Real.exp_pos _).ne' hMpos.ne', Real.log_exp] at this
  have h3 := mul_le_mul_of_nonneg_left h2 hwi.le
  have h4 : (F.weight t)⁻¹ * (-(s * θ * F.weight t) + Real.log M.toReal) =
      -(s * θ) + (F.weight t)⁻¹ * Real.log M.toReal := by
    field_simp
  linarith

theorem S200P_neBot (F : LDFamily) : (indexFilter F).NeBot := by
  unfold indexFilter
  rw [Filter.comap_neBot_iff]
  intro t ht
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.1 ht
  obtain ⟨x, hx, hNx⟩ := F.index_unbounded N
  exact ⟨⟨x, hx⟩, hN x hNx⟩

theorem S200P_limsup (F : LDFamily) (a b : ℝ) (e : ℝ → ℝ) (hLD : HasLD F a b e)
    (A : ∀ t : F.index, Set (F.experiment t).Space) (s θ : ℝ) (hs : s ∈ Set.Icc a b)
    (hA : ∀ t, ∀ x ∈ A t, s * θ * F.weight t ≤ s * (F.experiment t).observable x) :
    Filter.limsup (scaledEvent F A) (indexFilter F) ≤ ((e s - s * θ : ℝ) : EReal) := by
  haveI := S200P_neBot F
  have hT : Tendsto (fun t => ((-(s * θ) : ℝ) : EReal) + scaledMoment F s t) (indexFilter F)
      (𝓝 (((-(s * θ) : ℝ) : EReal) + (e s : EReal))) := by
    have hc := EReal.continuousAt_add (p := ((((-(s * θ) : ℝ) : EReal)), (e s : EReal)))
      (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
    exact hc.tendsto.comp (tendsto_const_nhds.prodMk_nhds (hLD.2 s hs))
  calc Filter.limsup (scaledEvent F A) (indexFilter F)
      ≤ Filter.limsup (fun t => ((-(s * θ) : ℝ) : EReal) + scaledMoment F s t) (indexFilter F) :=
        Filter.limsup_le_limsup (Eventually.of_forall (S200P_idx F A s θ hA))
    _ = ((-(s * θ) : ℝ) : EReal) + (e s : EReal) := hT.limsup_eq
    _ = ((e s - s * θ : ℝ) : EReal) := by
        rw [show e s - s * θ = -(s * θ) + e s by ring, EReal.coe_add]

theorem S200P_holder (E : FiniteExperiment) (s t : ℝ) (hs : s < 0) (ht : 0 < t) :
    exponentialMoment E 0 ≤
      exponentialMoment E s ^ (t / (t - s)) * exponentialMoment E t ^ (-s / (t - s)) := by
  letI := E.measurableSpace
  have hts : 0 < t - s := by linarith
  have hp : 0 ≤ t / (t - s) := div_nonneg ht.le hts.le
  have hq : 0 ≤ -s / (t - s) := div_nonneg (by linarith) hts.le
  have hpq : t / (t - s) + -s / (t - s) = 1 := by field_simp; ring
  have key := ENNReal.lintegral_mul_norm_pow_le (μ := E.measure)
    (S200P_meas E s).aemeasurable (S200P_meas E t).aemeasurable hp hq hpq
  refine le_of_eq_of_le ?_ key
  unfold exponentialMoment
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq, ← ENNReal.ofReal_mul (by positivity),
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 2
  field_simp
  ring

theorem S200P_three (F : LDFamily) (a b : ℝ) (e : ℝ → ℝ) (hLD : HasLD F a b e) (s t : ℝ)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (h0 : (0 : ℝ) ∈ Set.Icc a b)
    (hs0 : s < 0) (ht0 : 0 < t) : e 0 * (t - s) ≤ t * e s - s * e t := by
  haveI := S200P_neBot F
  have hfin : ∀ r ∈ Set.Icc a b, ∀ᶠ i in indexFilter F, exponentialMoment (F.experiment i) r ≠ ⊤ := by
    intro r hr
    filter_upwards [(hLD.2 r hr).eventually_lt_const (EReal.coe_lt_top (e r))] with i hi
    intro hM
    have hw : 0 < (F.weight i)⁻¹ := inv_pos.2 (F.weight_positive i)
    unfold scaledMoment at hi
    rw [hM, ENNReal.log_top, EReal.coe_mul_top_of_pos hw] at hi
    exact lt_irrefl _ hi
  let R : ℝ → F.index → ℝ := fun r i =>
    (F.weight i)⁻¹ * Real.log (exponentialMoment (F.experiment i) r).toReal
  have hR : ∀ r ∈ Set.Icc a b, Tendsto (R r) (indexFilter F) (𝓝 (e r)) := by
    intro r hr
    rw [← EReal.tendsto_coe]
    refine (hLD.2 r hr).congr' ?_
    filter_upwards [hfin r hr] with i hi
    exact S200P_moment_real F r i hi
  have hts : 0 < t - s := by linarith
  have hev : ∀ᶠ i in indexFilter F, R 0 i * (t - s) ≤ t * R s i - s * R t i := by
    filter_upwards [hfin 0 h0, hfin s hs, hfin t ht] with i h0i hsi hti
    have hw : 0 < (F.weight i)⁻¹ := inv_pos.2 (F.weight_positive i)
    set M0 := exponentialMoment (F.experiment i) 0
    set Ms := exponentialMoment (F.experiment i) s
    set Mt := exponentialMoment (F.experiment i) t
    have hH : M0 ≤ Ms ^ (t / (t - s)) * Mt ^ (-s / (t - s)) := S200P_holder _ s t hs0 ht0
    have p0 : 0 < M0.toReal := ENNReal.toReal_pos (S200P_M_ne_zero _ _) h0i
    have ps : 0 < Ms.toReal := ENNReal.toReal_pos (S200P_M_ne_zero _ _) hsi
    have pt : 0 < Mt.toReal := ENNReal.toReal_pos (S200P_M_ne_zero _ _) hti
    have h1 : M0.toReal ≤ Ms.toReal ^ (t / (t - s)) * Mt.toReal ^ (-s / (t - s)) := by
      have hne : Ms ^ (t / (t - s)) * Mt ^ (-s / (t - s)) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (div_nonneg ht0.le hts.le) hsi)
          (ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) hts.le) hti)
      have := ENNReal.toReal_mono hne hH
      rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at this
    have h2 : Real.log M0.toReal ≤
        t / (t - s) * Real.log Ms.toReal + -s / (t - s) * Real.log Mt.toReal := by
      have := Real.log_le_log p0 h1
      rwa [Real.log_mul (Real.rpow_pos_of_pos ps _).ne' (Real.rpow_pos_of_pos pt _).ne',
        Real.log_rpow ps, Real.log_rpow pt] at this
    have h3 : Real.log M0.toReal * (t - s) ≤ t * Real.log Ms.toReal - s * Real.log Mt.toReal := by
      have := mul_le_mul_of_nonneg_right h2 hts.le
      have e1 : (t / (t - s) * Real.log Ms.toReal + -s / (t - s) * Real.log Mt.toReal) * (t - s)
          = t * Real.log Ms.toReal - s * Real.log Mt.toReal := by
        field_simp; ring
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hw.le
    show (F.weight i)⁻¹ * Real.log M0.toReal * (t - s) ≤
      t * ((F.weight i)⁻¹ * Real.log Ms.toReal) - s * ((F.weight i)⁻¹ * Real.log Mt.toReal)
    nlinarith
  exact le_of_tendsto_of_tendsto ((hR 0 h0).mul_const _)
    (((hR s hs).const_mul t).sub ((hR t ht).const_mul s)) hev

end QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 in
theorem solution (F : LDFamily) (a b : ℝ) (hab : a < b)
    (e : ℝ → ℝ) (hLD : HasLD F a b e) :
    (a ≤ 0 ∧ 0 < b → ∀ theta : ℝ,
      Filter.limsup (scaledEvent F (upperTail F theta)) (indexFilter F) ≤
        if rightSlope b e 0 ≤ (theta : EReal) then ((-legendre a b e theta : ℝ) : EReal) else (e 0 : EReal)) ∧
    (a < 0 ∧ 0 ≤ b → ∀ theta : ℝ,
      Filter.limsup (scaledEvent F (lowerTail F theta)) (indexFilter F) ≤
        if (theta : EReal) ≤ leftSlope a e 0 then ((-legendre a b e theta : ℝ) : EReal) else (e 0 : EReal)) := by
  constructor
  · rintro ⟨ha, hb⟩ θ
    have h0 : (0 : ℝ) ∈ Set.Icc a b := ⟨ha, hb.le⟩
    have hA : ∀ s, 0 ≤ s → ∀ t, ∀ x ∈ upperTail F θ t,
        s * θ * F.weight t ≤ s * (F.experiment t).observable x := by
      intro s hs t x hx
      have hx' : θ * F.weight t < (F.experiment t).observable x := hx
      nlinarith
    have hz := S200P_limsup F a b e hLD _ 0 θ h0 (hA 0 le_rfl)
    simp only [zero_mul, sub_zero] at hz
    split_ifs with hsl
    · obtain ⟨u, hu, hL⟩ := S200P_attain a b hab e hLD.1 θ
      rw [hL]
      rcases le_or_gt 0 u with hu0 | hu0
      · have := S200P_limsup F a b e hLD _ u θ hu (hA u hu0)
        refine this.trans_eq ?_
        congr 1; ring
      · have hsec : ((((e 0 - e u) / (0 - u)) : ℝ) : EReal) ≤ rightSlope b e 0 := by
          apply le_sInf
          rintro v ⟨t, ht0, htb, rfl⟩
          rw [EReal.coe_le_coe_iff, div_le_div_iff₀ (by linarith) (by linarith)]
          have := S200P_three F a b e hLD u t hu ⟨by linarith, htb⟩ h0 hu0 ht0
          nlinarith
        have h1 := EReal.coe_le_coe_iff.1 (hsec.trans hsl)
        rw [div_le_iff₀ (by linarith)] at h1
        refine hz.trans (EReal.coe_le_coe_iff.2 ?_)
        nlinarith
    · exact hz
  · rintro ⟨ha, hb⟩ θ
    have h0 : (0 : ℝ) ∈ Set.Icc a b := ⟨ha.le, hb⟩
    have hA : ∀ s, s ≤ 0 → ∀ t, ∀ x ∈ lowerTail F θ t,
        s * θ * F.weight t ≤ s * (F.experiment t).observable x := by
      intro s hs t x hx
      have hx' : (F.experiment t).observable x < θ * F.weight t := hx
      nlinarith
    have hz := S200P_limsup F a b e hLD _ 0 θ h0 (hA 0 le_rfl)
    simp only [zero_mul, sub_zero] at hz
    split_ifs with hsl
    · obtain ⟨u, hu, hL⟩ := S200P_attain a b hab e hLD.1 θ
      rw [hL]
      rcases le_or_gt u 0 with hu0 | hu0
      · have := S200P_limsup F a b e hLD _ u θ hu (hA u hu0)
        refine this.trans_eq ?_
        congr 1; ring
      · have hsec : leftSlope a e 0 ≤ ((((e u - e 0) / (u - 0)) : ℝ) : EReal) := by
          apply sSup_le
          rintro v ⟨t, hat, ht0, rfl⟩
          rw [EReal.coe_le_coe_iff, div_le_div_iff₀ (by linarith) (by linarith)]
          have := S200P_three F a b e hLD t u ⟨hat, by linarith⟩ hu h0 ht0 hu0
          nlinarith
        have h1 := EReal.coe_le_coe_iff.1 (hsl.trans hsec)
        rw [le_div_iff₀ (by linarith)] at h1
        refine hz.trans (EReal.coe_le_coe_iff.2 ?_)
        nlinarith
    · exact hz

end
