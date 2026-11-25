-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_exists_tendsto_pow_zero_a94ec10e85d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:29.457531+00:00
-- url     : https://prove2.me/submissions/6ac292ca-f9bc-4f9d-832f-9129dc4ed151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_apply_ae5c0d4341c5
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_mul_a4f80d01f319
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_nhdsNE_zero_neBot_71889b9ea3f1
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_eventually_mul_mem_of_isCompact_2b6e19c23fce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise
variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (hR : ¬ DiscreteTopology R) :
    ∃ t : R, t ≠ 0 ∧ Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 0) := by
  let _ : MeasurableSpace R := borel R
  have _ : BorelSpace R := ⟨rfl⟩
  have _ := nhdsNE_zero_neBot hR
  let ν : Measure R := addHaar

  let md : ∀ a : R, a ≠ 0 → ℝ≥0 := fun a ha => addEquivAddHaarChar (mulLeftAddEquiv a ha)
  have md_image : ∀ (a : R) (ha : a ≠ 0) (S : Set R),
      ν ((fun x => a * x) '' S) = (md a ha : ℝ≥0∞) * ν S := by
    intro a ha S
    have h := addEquivAddHaarChar_smul_preimage ν (X := (fun x => a * x) '' S)
      (mulLeftAddEquiv a ha)
    have hpre : (mulLeftAddEquiv a ha) ⁻¹' ((fun x => a * x) '' S) = S :=
      preimage_image_eq S (mulLeftAddEquiv a ha).injective
    rw [hpre, ENNReal.smul_def, smul_eq_mul] at h
    exact h.symm
  have md_pos : ∀ (a : R) (ha : a ≠ 0), 0 < md a ha := fun a ha => addEquivAddHaarChar_pos _
  have md_mul : ∀ (a b : R) (ha : a ≠ 0) (hb : b ≠ 0),
      md (a * b) (mul_ne_zero ha hb) = md b hb * md a ha := by
    intro a b ha hb
    simp only [md]
    rw [mulLeftAddEquiv_mul a b ha hb, addEquivAddHaarChar_trans]
  have md_pow : ∀ (a : R) (ha : a ≠ 0) (n : ℕ), md (a ^ n) (pow_ne_zero n ha) = md a ha ^ n := by
    intro a ha n
    induction n with
    | zero =>
      simp only [md, pow_zero]
      have : mulLeftAddEquiv (1 : R) one_ne_zero = ContinuousAddEquiv.refl R := by
        ext x; simp [mulLeftAddEquiv_apply]
      rw [this, addEquivAddHaarChar_refl]
    | succ n ih =>
      have h := md_mul (a ^ n) a (pow_ne_zero n ha) ha
      simp only [← pow_succ] at h
      rw [h, ih, pow_succ, mul_comm]

  obtain ⟨V0, hV0c, hV0n⟩ : ∃ V0 : Set R, IsCompact V0 ∧ V0 ∈ 𝓝 (0 : R) :=
    exists_compact_mem_nhds 0
  set W : Set R := insert 1 V0 with hWdef
  have hWc : IsCompact W := hV0c.insert 1
  have hWn : W ∈ 𝓝 (0 : R) := mem_of_superset hV0n (subset_insert _ _)
  have h1W : (1 : R) ∈ W := mem_insert _ _
  have hWpos : 0 < ν W := measure_pos_of_mem_nhds ν hWn
  have hWfin : ν W ≠ ∞ := hWc.measure_lt_top.ne
  have hV0pos : 0 < ν V0 := measure_pos_of_mem_nhds ν hV0n
  obtain ⟨O, hOsup, hOo, hOlt⟩ := Set.exists_isOpen_lt_of_lt ({0} : Set R) (ν V0)
    (by rw [measure_singleton (μ := ν) (0 : R)]; exact hV0pos)
  obtain ⟨V, hVn, hVsub, hVc⟩ := local_compact_nhds
    (inter_mem (hOo.mem_nhds (hOsup rfl)) hV0n)
  have hVW : V ⊆ W := fun x hx => subset_insert _ _ (hVsub hx).2
  have hVO : ν V < ν W :=
    ((measure_mono fun x hx => (hVsub hx).1).trans_lt hOlt).trans_le
      (measure_mono (subset_insert _ _))

  obtain ⟨t, htV, ht0⟩ := ((eventually_mul_mem_of_isCompact hWc hVn).filter_mono
    nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ({0}ᶜ : Set R) ∈ 𝓝[≠] (0 : R)) |>.exists
  have ht0' : t ≠ 0 := ht0
  have hmd_t : md t ht0' < 1 := by
    have h1 : ν ((fun x => t * x) '' W) ≤ ν V :=
      measure_mono (by rintro _ ⟨w, hw, rfl⟩; exact htV w hw)
    rw [md_image] at h1
    have h2 : (md t ht0' : ℝ≥0∞) * ν W < 1 * ν W := by rw [one_mul]; exact h1.trans_lt hVO
    have h3 := (ENNReal.mul_lt_mul_iff_left hWpos.ne' hWfin).mp h2
    exact_mod_cast h3

  let S : ℕ → Set R := fun n => (fun x => t ^ n * x) '' W
  have hSc : ∀ n, IsCompact (S n) := fun n => hWc.image (continuous_const.mul continuous_id)
  have hSanti : Antitone S := by
    apply antitone_nat_of_succ_le
    intro n
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨t * w, hVW (htV w hw), by simp only [pow_succ, mul_assoc]⟩
  have hSmem : ∀ n, t ^ n ∈ S n := fun n => ⟨1, h1W, mul_one _⟩

  set C : Set R := (fun p : R × R => p.1 * p.2) '' (W ×ˢ W)
  have hCfin : ν C ≠ ∞ := ((hWc.prod hWc).image continuous_mul).measure_lt_top.ne
  have hinter : ∀ a ∈ ⋂ n, S n, a = 0 := by
    intro a ha
    by_contra ha0
    have key : ∀ n : ℕ, (md a ha0 : ℝ≥0∞) * ν W ≤ (md t ht0' : ℝ≥0∞) ^ n * ν C := by
      intro n
      obtain ⟨w, hw, hwa⟩ := mem_iInter.mp ha n
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp only [mul_zero] at hwa
        exact ha0 hwa.symm
      have hmd : md a ha0 = md w hw0 * md t ht0' ^ n := by
        have := md_mul (t ^ n) w (pow_ne_zero n ht0') hw0
        simp only [hwa] at this
        rw [this, md_pow]
      have hsub : (fun x => w * x) '' W ⊆ C := by
        rintro _ ⟨x, hx, rfl⟩; exact ⟨(w, x), ⟨hw, hx⟩, rfl⟩
      calc (md a ha0 : ℝ≥0∞) * ν W
          = (md t ht0' : ℝ≥0∞) ^ n * ((md w hw0 : ℝ≥0∞) * ν W) := by
            rw [hmd]; push_cast; ring
        _ = (md t ht0' : ℝ≥0∞) ^ n * ν ((fun x => w * x) '' W) := by rw [md_image]
        _ ≤ (md t ht0' : ℝ≥0∞) ^ n * ν C := by gcongr
    have hlim : Tendsto (fun n : ℕ => (md t ht0' : ℝ≥0∞) ^ n * ν C) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr (ENNReal.coe_lt_one_iff.mpr hmd_t))
        (Or.inr hCfin) (a := 0) (b := ν C)
      rwa [zero_mul] at h
    have hle := ge_of_tendsto' hlim key
    have hpos : 0 < (md a ha0 : ℝ≥0∞) * ν W :=
      ENNReal.mul_pos (by exact_mod_cast (md_pos a ha0).ne') hWpos.ne'
    exact absurd hle (not_le.mpr hpos)
  refine ⟨t, ht0', ?_⟩
  intro U hU
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact hSanti.directed_ge hSc
    (U := U) (fun x hx => by rw [hinter x hx]; exact hU)
  rw [mem_map, mem_atTop_sets]
  exact ⟨n, fun m hm => hn (hSanti hm (hSmem m))⟩
end GroundTheory.Heights₂.Theta
