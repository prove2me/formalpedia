-- Prove2me | solution 1 for SoftenDataShare.Mutual.zN_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:59:40.500113+00:00
-- url     : https://prove2.me/submissions/8b61e328-0784-4461-8513-9e30801cd5a3

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

theorem solution {F f : ℝ → ℝ} (hF : MHRDist F f) :
    ∃! z : ℝ, IsZN F f z := by
  have hmono := sds_G_strictMono hF
  have hG1 : Gf F f 1 = 1 / 2 := by simp [Gf, hF.F_one]; norm_num
  have hGhalf : Gf F f (1 / 2) < 0 := by
    have := sds_pos_ratio hF (z := 1 / 2) ⟨by norm_num, by norm_num⟩
    unfold Gf
    linarith
  obtain ⟨z0, hz0, hz0G⟩ := intermediate_value_Icc (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    ((sds_G_cont hF).mono (Set.Icc_subset_Icc (by norm_num) le_rfl))
    (show (0:ℝ) ∈ Set.Icc (Gf F f (1 / 2)) (Gf F f 1) from ⟨hGhalf.le, by rw [hG1]; norm_num⟩)
  have hz0a : z0 ≠ 1 / 2 := by rintro rfl; linarith
  have hz0b : z0 ≠ 1 := by rintro rfl; rw [hG1] at hz0G; norm_num at hz0G
  refine ⟨z0, (sds_isZN_iff hF).2 ⟨⟨lt_of_le_of_ne hz0.1 (Ne.symm hz0a), lt_of_le_of_ne hz0.2 hz0b⟩, hz0G⟩, ?_⟩
  intro y hy
  obtain ⟨hy1, hy2⟩ := (sds_isZN_iff hF).1 hy
  have hyI : y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy1.1], hy1.2.le⟩
  have hzI : z0 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hz0.1], hz0.2⟩
  exact hmono.injOn hyI hzI (by rw [hy2, hz0G])
