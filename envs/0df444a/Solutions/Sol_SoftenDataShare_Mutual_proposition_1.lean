-- Prove2me | solution 1 for SoftenDataShare.Mutual.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T00:38:31.081068+00:00
-- url     : https://prove2.me/submissions/2e1c9fb3-de3a-4d9d-a18a-27063e506116

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

set_option autoImplicit false
open SoftenDataShare.Mutual

lemma sds_contF {F f : ℝ → ℝ} (hF : MHRDist F f) : ContinuousOn F (Set.Icc 0 1) :=
  fun x hx => (hF.hasDerivWithinAt x hx).continuousWithinAt

lemma sds_hasDerivAt {F f : ℝ → ℝ} (hF : MHRDist F f) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt F (f x) x :=
  (hF.hasDerivWithinAt x (Set.Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)

lemma sds_strictMonoF {F f : ℝ → ℝ} (hF : MHRDist F f) : StrictMonoOn F (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (sds_contF hF)
  intro x hx
  rw [interior_Icc] at hx
  rw [(sds_hasDerivAt hF hx).deriv]
  exact hF.density_pos x (Set.Ioo_subset_Icc_self hx)

lemma sds_F_lt_one {F f : ℝ → ℝ} (hF : MHRDist F f) {z : ℝ} (hz : z ∈ Set.Ico (0:ℝ) 1) :
    F z < 1 := by
  have := sds_strictMonoF hF ⟨hz.1, hz.2.le⟩ ⟨zero_le_one, le_rfl⟩ hz.2
  rwa [hF.F_one] at this

noncomputable def Gf (F f : ℝ → ℝ) (z : ℝ) : ℝ := z - 1 / 2 - (1 - F z) / f z

lemma sds_G_cont {F f : ℝ → ℝ} (hF : MHRDist F f) : ContinuousOn (Gf F f) (Set.Icc 0 1) := by
  unfold Gf
  exact (continuousOn_id.sub continuousOn_const).sub
    ((continuousOn_const.sub (sds_contF hF)).div hF.continuousOn_density
      (fun x hx => (hF.density_pos x hx).ne'))

lemma sds_pos_ratio {F f : ℝ → ℝ} (hF : MHRDist F f) {z : ℝ} (hz : z ∈ Set.Ico (0:ℝ) 1) :
    0 < (1 - F z) / f z :=
  div_pos (by linarith [sds_F_lt_one hF hz]) (hF.density_pos z ⟨hz.1, hz.2.le⟩)

lemma sds_G_strictMono {F f : ℝ → ℝ} (hF : MHRDist F f) : StrictMonoOn (Gf F f) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have haI : a ∈ Set.Ico (0:ℝ) 1 := ⟨ha.1, lt_of_lt_of_le hab hb.2⟩
  unfold Gf
  rcases lt_or_eq_of_le hb.2 with hb1 | hb1
  · have hbI : b ∈ Set.Ico (0:ℝ) 1 := ⟨hb.1, hb1⟩
    have hh := hF.hazard_strictMonoOn haI hbI hab
    have hpa : 0 < hazard F f a := by
      unfold hazard
      exact div_pos (hF.density_pos a ha) (by linarith [sds_F_lt_one hF haI])
    have h2 := one_div_lt_one_div_of_lt hpa hh
    unfold hazard at h2
    rw [one_div_div, one_div_div] at h2
    linarith
  · subst hb1
    have := sds_pos_ratio hF haI
    simp [hF.F_one]
    linarith

lemma sds_isZN_iff {F f : ℝ → ℝ} (hF : MHRDist F f) {z : ℝ} :
    IsZN F f z ↔ z ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧ Gf F f z = 0 := by
  unfold IsZN Gf hazard
  rw [one_div_div]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

lemma sds_pi21_deriv {F f : ℝ → ℝ} (hF : MHRDist F f) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (pi21 F) (-2 * f x * Gf F f x) x := by
  have h := ((((hasDerivAt_id x).const_mul 2).sub_const 1).mul
    ((hasDerivAt_const x (1:ℝ)).sub (sds_hasDerivAt hF hx)))
  have h' : HasDerivAt (pi21 F) _ x := h
  refine h'.congr_deriv ?_
  have hf : f x ≠ 0 := (hF.density_pos x (Set.Ioo_subset_Icc_self hx)).ne'
  unfold Gf
  field_simp
  simp
  ring

lemma sds_pi21_cont {F f : ℝ → ℝ} (hF : MHRDist F f) : ContinuousOn (pi21 F) (Set.Icc 0 1) := by
  unfold pi21
  exact ((continuousOn_const.mul continuousOn_id).sub continuousOn_const).mul
    (continuousOn_const.sub (sds_contF hF))

lemma sds_zN_facts {F f : ℝ → ℝ} (hF : MHRDist F f) {zN : ℝ} (hzN : IsZN F f zN) :
    zN ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧ Gf F f zN = 0 := (sds_isZN_iff hF).1 hzN

lemma sds_pi21_le {F f : ℝ → ℝ} (hF : MHRDist F f) {zN : ℝ} (hzN : IsZN F f zN) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, pi21 F z ≤ pi21 F zN := by
  obtain ⟨hz1, hz2⟩ := sds_zN_facts hF hzN
  have hzNI : zN ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hz1.1], hz1.2.le⟩
  have hmono := sds_G_strictMono hF
  have hinc : StrictMonoOn (pi21 F) (Set.Icc 0 zN) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 zN)
    · exact (sds_pi21_cont hF).mono (Set.Icc_subset_Icc le_rfl hz1.2.le)
    · intro x hx
      rw [interior_Icc] at hx
      have hx1 : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx.1, lt_trans hx.2 hz1.2⟩
      rw [(sds_pi21_deriv hF hx1).deriv]
      have hG : Gf F f x < 0 := by
        rw [← hz2]
        exact hmono ⟨hx.1.le, hx1.2.le⟩ hzNI hx.2
      have := hF.density_pos x (Set.Ioo_subset_Icc_self hx1)
      nlinarith
  have hdec : StrictAntiOn (pi21 F) (Set.Icc zN 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc zN 1)
    · exact (sds_pi21_cont hF).mono (Set.Icc_subset_Icc hzNI.1 le_rfl)
    · intro x hx
      rw [interior_Icc] at hx
      have hx1 : x ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_trans (by linarith [hz1.1]) hx.1, hx.2⟩
      rw [(sds_pi21_deriv hF hx1).deriv]
      have hG : 0 < Gf F f x := by
        rw [← hz2]
        exact hmono hzNI ⟨hx1.1.le, hx1.2.le⟩ hx.1
      have := hF.density_pos x (Set.Ioo_subset_Icc_self hx1)
      nlinarith
  intro z hz
  rcases le_total z zN with h | h
  · exact hinc.monotoneOn ⟨hz.1, h⟩ ⟨hzNI.1, le_rfl⟩ h
  · exact hdec.antitoneOn ⟨le_rfl, hzNI.2⟩ ⟨h, hz.2⟩ h

lemma sds_pi22_zN {F f : ℝ → ℝ} (hF : MHRDist F f) {zN : ℝ} (hzN : IsZN F f zN) :
    pi21 F zN = pi22 F zN zN := by
  obtain ⟨hz1, hz2⟩ := sds_zN_facts hF hzN
  have hzNI : zN ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hz1.1], hz1.2.le⟩
  unfold pi22
  symm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨zN, ⟨hzNI.1, le_rfl⟩, ?_⟩
    simp only [pi21]; ring
  · rintro _ ⟨z, hz, rfl⟩
    have := sds_pi21_le hF hzN z ⟨hz.1, hz.2.trans hzNI.2⟩
    simp only [pi21] at this ⊢
    nlinarith

lemma sds_pi22_cont {F f : ℝ → ℝ} (hF : MHRDist F f) (a b : ℝ) (ha : a ≤ 1) :
    ContinuousOn (fun z => (2 * z - 1) * (1 - F b + F a - F z)) (Set.Icc 0 a) := by
  have := (sds_contF hF).mono (Set.Icc_subset_Icc le_rfl ha)
  exact ((continuousOn_const.mul continuousOn_id).sub continuousOn_const).mul
    ((continuousOn_const.sub this))

lemma sds_integral_f {F f : ℝ → ℝ} (hF : MHRDist F f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) : ∫ x in a..b, f x = F b - F a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
  · exact (sds_contF hF).mono (Set.Icc_subset_Icc ha hb)
  · intro x hx
    have hx' : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (sds_hasDerivAt hF hx').hasDerivWithinAt
  · exact (hF.continuousOn_density.mono (by
      rw [Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc ha hb)).intervalIntegrable


lemma sds_zN_half {F f : ℝ → ℝ} (hF : MHRDist F f) {zN : ℝ} (hzN : IsZN F f zN) :
    1 - F zN = (zN - 1 / 2) * f zN := by
  have h2 := hzN.2
  have hz1 := hzN.1
  have hf : 0 < f zN := hF.density_pos zN ⟨by linarith [hz1.1], hz1.2.le⟩
  unfold hazard at h2
  rw [one_div_div] at h2
  have : (1 - F zN) / f zN = zN - 1 / 2 := by linarith
  rw [div_eq_iff hf.ne'] at this
  linarith

lemma sds_pN2 {F f : ℝ → ℝ} {zN : ℝ} (hzN : IsZN F f zN) : pN2 F f zN = 2 * zN - 1 := by
  unfold pN2
  have hzN' := hzN.2
  have : 1 / hazard F f zN = zN - 1 / 2 := by linarith
  calc 2 / hazard F f zN = 2 * (1 / hazard F f zN) := by ring
    _ = 2 * zN - 1 := by rw [this]; ring

lemma sds_pi21_strictMono {F f : ℝ → ℝ} (hF : MHRDist F f) {zN : ℝ} (hzN : IsZN F f zN) :
    StrictMonoOn (pi21 F) (Set.Icc 0 zN) := by
  obtain ⟨hz1, hz2⟩ := sds_zN_facts hF hzN
  have hzNI : zN ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hz1.1], hz1.2.le⟩
  have hmono := sds_G_strictMono hF
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 zN)
  · exact (sds_pi21_cont hF).mono (Set.Icc_subset_Icc le_rfl hz1.2.le)
  · intro x hx
    rw [interior_Icc] at hx
    have hx1 : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx.1, lt_trans hx.2 hz1.2⟩
    rw [(sds_pi21_deriv hF hx1).deriv]
    have hG : Gf F f x < 0 := by
      rw [← hz2]
      exact hmono ⟨hx.1.le, hx1.2.le⟩ hzNI hx.2
    have := hF.density_pos x (Set.Ioo_subset_Icc_self hx1)
    nlinarith

lemma sds_part1 {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f) (hzN : IsZN F f zN)
    (b : ℝ) (hb0 : zN < b) (hb1 : b ≤ 1) :
    piN1 F f zN < pi1 f zN b ∧ piN2 F f zN < pi2 F f zN b := by
  obtain ⟨hz1, hz2⟩ := sds_zN_facts hF hzN
  have hz0 : 0 ≤ zN := by linarith [hz1.1]
  have hbI : b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hb1⟩
  have hfc : ContinuousOn f (Set.Icc 0 1) := hF.continuousOn_density
  have hFzN0 : 0 < F zN := by
    have := sds_strictMonoF hF ⟨le_rfl, zero_le_one⟩ ⟨hz0, hz1.2.le⟩ (by linarith [hz1.1])
    rwa [hF.F_zero] at this
  have hFb1 : F b ≤ 1 := by
    have := (sds_strictMonoF hF).monotoneOn hbI ⟨zero_le_one, le_rfl⟩ hb1
    rwa [hF.F_one] at this
  have hfint0 : ContinuousOn f (Set.uIcc 0 zN) :=
    hfc.mono (by rw [Set.uIcc_of_le hz0]; exact Set.Icc_subset_Icc le_rfl hz1.2.le)
  constructor
  · -- firm 1
    have hdiff : pi1 f zN b - piN1 F f zN = ∫ x in (0:ℝ)..zN, (2 * b - 2 * zN) * f x := by
      unfold pi1 piN1
      rw [sds_pN2 hzN, ← intervalIntegral.integral_sub]
      · congr 1; ext x; ring
      · apply ContinuousOn.intervalIntegrable
        exact ContinuousOn.mul (by fun_prop) hfint0
      · apply ContinuousOn.intervalIntegrable
        exact ContinuousOn.mul (by fun_prop) hfint0
    rw [intervalIntegral.integral_const_mul, sds_integral_f hF le_rfl hz0 hz1.2.le,
      hF.F_zero] at hdiff
    have : 0 < (2 * b - 2 * zN) * (F zN - 0) := by
      apply mul_pos <;> linarith
    linarith
  · -- firm 2
    have hI2 : ∫ x in zN..b, f x = F b - F zN := sds_integral_f hF hz0 hb0.le hb1
    have hint : IntervalIntegrable f MeasureTheory.volume zN b :=
      (hfc.mono (by rw [Set.uIcc_of_le hb0.le]; exact Set.Icc_subset_Icc hz0 hb1)).intervalIntegrable
    have hpos2 : 0 < ∫ x in zN..b, (2 * x - 2 * zN) * f x := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ hb0
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul (by fun_prop)
        exact hfc.mono (by rw [Set.uIcc_of_le hb0.le]; exact Set.Icc_subset_Icc hz0 hb1)
      · intro x hx
        have := hF.density_pos x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have : 0 < 2 * x - 2 * zN := by linarith [hx.1]
        positivity
    have hsplit : ∫ x in zN..b, (2 * x - 1) * f x =
        (2 * zN - 1) * (F b - F zN) + ∫ x in zN..b, (2 * x - 2 * zN) * f x := by
      rw [← hI2, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
      · congr 1; ext x; ring
      · exact (hint.const_mul _)
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul (by fun_prop)
        exact hfc.mono (by rw [Set.uIcc_of_le hb0.le]; exact Set.Icc_subset_Icc hz0 hb1)
    unfold pi2 pi21 piN2
    rw [sds_pN2 hzN, hsplit]
    have : 0 ≤ (b - zN) * (1 - F b) := mul_nonneg (by linarith) (by linarith)
    nlinarith

lemma sds_part2 {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f) (hzN : IsZN F f zN) :
    ∃ b' ∈ Set.Ioo zN 1, pi22 F zN b' < pi21 F b' := by
  obtain ⟨hz1, hz2⟩ := sds_zN_facts hF hzN
  have hz0 : 0 ≤ zN := by linarith [hz1.1]
  have hzNI1 : zN ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hz1.1], hz1.2⟩
  have hfz : 0 < f zN := hF.density_pos zN ⟨hz0, hz1.2.le⟩
  have hhalf := sds_zN_half hF hzN
  set z0 : ℝ := (1 / 2 + zN) / 2 with hz0def
  have hz0a : 1 / 2 < z0 := by rw [hz0def]; linarith [hz1.1]
  have hz0b : z0 < zN := by rw [hz0def]; linarith [hz1.1]
  have hmono := sds_pi21_strictMono hF hzN
  have hc : pi21 F z0 < pi21 F zN :=
    hmono ⟨by linarith, hz0b.le⟩ ⟨hz0, le_rfl⟩ hz0b
  -- derivative of F at zN
  have hD : HasDerivAt F (f zN) zN := sds_hasDerivAt hF hzNI1
  have hslope : Filter.Tendsto (slope F zN) (nhdsWithin zN (Set.Ioi zN)) (nhds (f zN)) :=
    (hasDerivAt_iff_tendsto_slope.1 hD).mono_left
      (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hFcont : ContinuousAt F zN := hD.continuousAt
  have hFlim : Filter.Tendsto F (nhdsWithin zN (Set.Ioi zN)) (nhds (F zN)) :=
    hFcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpicont : Filter.Tendsto (pi21 F) (nhdsWithin zN (Set.Ioi zN)) (nhds (pi21 F zN)) := by
    have : ContinuousAt (pi21 F) zN := by
      unfold pi21
      exact ((continuousAt_const.mul continuousAt_id).sub continuousAt_const).mul
        (continuousAt_const.sub hFcont)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  -- E3 limit
  have hE3lim : Filter.Tendsto (fun b => (1 - F b) - (zN - z0) * slope F zN b)
      (nhdsWithin zN (Set.Ioi zN)) (nhds ((1 - F zN) - (zN - z0) * f zN)) :=
    (tendsto_const_nhds.sub hFlim).sub (tendsto_const_nhds.mul hslope)
  have hE3pos : 0 < (1 - F zN) - (zN - z0) * f zN := by
    rw [hhalf, hz0def]; nlinarith
  have hE3 : ∀ᶠ b in nhdsWithin zN (Set.Ioi zN), 0 < (1 - F b) - (zN - z0) * slope F zN b :=
    hE3lim.eventually (lt_mem_nhds hE3pos)
  have hE2 : ∀ᶠ b in nhdsWithin zN (Set.Ioi zN), pi21 F z0 < pi21 F b :=
    hpicont.eventually (lt_mem_nhds hc)
  have hE1 : ∀ᶠ b in nhdsWithin zN (Set.Ioi zN), b < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds hz1.2)
  have hE0 : ∀ᶠ b in nhdsWithin zN (Set.Ioi zN), zN < b := self_mem_nhdsWithin
  obtain ⟨b, ⟨⟨⟨hb0, hb1⟩, hb2⟩, hb3⟩⟩ := (((hE0.and hE1).and hE2).and hE3).exists
  refine ⟨b, ⟨hb0, hb1⟩, ?_⟩
  have hbI : b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hb1.le⟩
  have hFb : F zN < F b := sds_strictMonoF hF ⟨hz0, hz1.2.le⟩ hbI hb0
  have hFb1 : F b < 1 := sds_F_lt_one hF ⟨hbI.1, hb1⟩
  -- unpack E3
  have hE3' : (zN - z0) * (F b - F zN) < (b - zN) * (1 - F b) := by
    rw [slope_def_field] at hb3
    have hbz : 0 < b - zN := by linarith
    have h := mul_pos hbz hb3
    have : (b - zN) * ((1 - F b) - (zN - z0) * ((F b - F zN) / (b - zN))) =
        (b - zN) * (1 - F b) - (zN - z0) * (F b - F zN) := by
      field_simp
    linarith
  unfold pi22
  rw [IsCompact.sSup_lt_iff_of_continuous isCompact_Icc ⟨0, le_rfl, hz0⟩
    (sds_pi22_cont hF zN b hz1.2.le)]
  intro z hz
  have hzI : z ∈ Set.Icc (0:ℝ) 1 := ⟨hz.1, hz.2.trans hz1.2.le⟩
  have hFz : F z ≤ F zN := (sds_strictMonoF hF).monotoneOn hzI ⟨hz0, hz1.2.le⟩ hz.2
  have hpib : pi21 F b = (2 * b - 1) * (1 - F b) := rfl
  have hpib0 : 0 < pi21 F b := by rw [hpib]; apply mul_pos <;> linarith
  have hφ : (2 * z - 1) * (1 - F b + F zN - F z) = pi21 F z - (2 * z - 1) * (F b - F zN) := by
    unfold pi21; ring
  rcases le_or_gt z (1 / 2) with h1 | h1
  · have : (2 * z - 1) * (1 - F b + F zN - F z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  rcases le_or_gt z z0 with h2 | h2
  · have hle : pi21 F z ≤ pi21 F z0 :=
      hmono.monotoneOn ⟨hz.1, hz.2⟩ ⟨by linarith, hz0b.le⟩ h2
    have : 0 ≤ (2 * z - 1) * (F b - F zN) := mul_nonneg (by linarith) (by linarith)
    rw [hφ]; linarith
  · have hle : pi21 F z ≤ pi21 F zN :=
      hmono.monotoneOn ⟨hz.1, hz.2⟩ ⟨hz0, le_rfl⟩ hz.2
    have : (2 * z0 - 1) * (F b - F zN) ≤ (2 * z - 1) * (F b - F zN) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hpiz : pi21 F zN = (2 * zN - 1) * (1 - F zN) := rfl
    rw [hφ]
    nlinarith

theorem solution {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) :
    (∀ b : ℝ, zN < b → b ≤ 1 →
        piN1 F f zN < pi1 f zN b ∧ piN2 F f zN < pi2 F f zN b) ∧
      ∃ b' ∈ Set.Ioo zN 1, pi22 F zN b' < pi21 F b' ∧
        piN1 F f zN < pi1 f zN b' ∧ piN2 F f zN < pi2 F f zN b' := by
  refine ⟨fun b hb hb1 => sds_part1 hF hzN b hb hb1, ?_⟩
  obtain ⟨b, hb, h⟩ := sds_part2 hF hzN
  exact ⟨b, hb, h, sds_part1 hF hzN b hb.1 hb.2.le⟩
