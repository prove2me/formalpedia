-- Prove2me | solution 1 for SoftenDataShare.Mutual.pi21_lt_pi21_zN
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:03:21.314046+00:00
-- url     : https://prove2.me/submissions/74c9c29d-a852-4b0c-b88c-8cb8e0283e9f

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

theorem solution {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, z ≠ zN → pi21 F z < pi21 F zN := by
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
  intro z hz hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hinc ⟨hz.1, h.le⟩ ⟨hzNI.1, le_rfl⟩ h
  · exact hdec ⟨le_rfl, hzNI.2⟩ ⟨h.le, hz.2⟩ h
