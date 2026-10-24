-- Prove2me | solution 1 for OutpatientWalkIn.SmallCap.lemma_D_3_unobs_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:46:28.214541+00:00
-- url     : https://prove2.me/submissions/19a8f59f-5381-4e5c-8b3b-fe99a072d2e7

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Definitions.Def_OutpatientWalkIn_SmallCap_Setting

namespace OWSC_D3

open OutpatientWalkIn.SmallCap Set

theorem w_continuousOn (w : ℝ → ℝ) (hc : ConvexOn ℝ (Ici 0) w) (hm : StrictMonoOn w (Ici 0))
    (h0 : w 0 = 0) : ContinuousOn w (Ici 0) := by
  apply hc.continuousOn_Ici
  have hup : ∀ t ∈ Icc (0:ℝ) 1, w t ≤ t * w 1 := by
    intro t ht
    have := hc.2 (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 zero_le_one)
      (sub_nonneg.2 ht.2) ht.1 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, h0] at this
    linarith
  have hlo : ∀ t ∈ Ici (0:ℝ), 0 ≤ w t := by
    intro t ht
    rw [← h0]; exact hm.monotoneOn (Set.mem_Ici.2 le_rfl) ht ht
  rw [ContinuousWithinAt, h0]
  have hlim : Filter.Tendsto (fun t : ℝ => t * w 1) (nhdsWithin 0 (Ici 0)) (nhds 0) := by
    have : Filter.Tendsto (fun t : ℝ => t * w 1) (nhds 0) (nhds (0 * w 1)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht using hlo t ht
  · have : ∀ᶠ t in nhdsWithin (0:ℝ) (Ici 0), t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, this] with t ht ht1
    exact hup t ⟨ht, ht1.le⟩

/-- walk/balk split of a mass `L ≥ 0` among non-schedulers. -/
theorem walk_balk (M : Model) (hM : M.Standing) (μS : ℝ) (hμS : μS ∈ Ico 0 M.mu)
    (L : ℝ) (hL : 0 ≤ L) (h0 : 0 < M.u1W μS 0) (hL' : M.u1W μS L < 0) :
    ∃ x ∈ Ioo 0 L, M.u1W μS x = 0 := by
  have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
  have hwc := w_continuousOn M.w hM.w_convex hM.w_strictMono hM.w_zero
  have hgc : ContinuousOn (fun x => M.u1W μS x) (Icc 0 L) := by
    have harg : ContinuousOn (fun p : ℝ => (p + M.lamE) / (M.mu - μS)) (Icc 0 L) :=
      ((continuous_id.add continuous_const).div_const _).continuousOn
    have hmaps : MapsTo (fun p : ℝ => (p + M.lamE) / (M.mu - μS)) (Icc 0 L) (Ici 0) := by
      intro p hp
      exact Set.mem_Ici.2 (div_nonneg (by have := hp.1; linarith [hM.lamE_nonneg]) hW.le)
    have := hwc.comp harg hmaps
    exact continuousOn_const.sub (continuousOn_const.mul this)
  obtain ⟨x, hx, hxz⟩ := intermediate_value_Icc' hL hgc ⟨hL'.le, h0.le⟩
  refine ⟨x, ⟨?_, ?_⟩, hxz⟩
  · rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h] at hxz; simp only at hxz; linarith
    · exact h
  · rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h] at hxz; simp only at hxz; linarith
    · exact h

end OWSC_D3

open OutpatientWalkIn.SmallCap Set

theorem solution (M : Model) (hM : M.Standing) (μS : ℝ) (hμS : μS ∈ Set.Ico 0 M.mu) :
    ∃ u : UnobsStrategy, M.IsUnobsEq μS u := by
  have hlam := hM.lam_pos
  have hlamE := hM.lamE_nonneg
  have hR := hM.R_pos
  have hCD := hM.CD_pos
  have hCW := hM.CW_pos
  have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
  have hwnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ M.w x := by
    intro x hx
    rw [← hM.w_zero]
    exact hM.w_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  have hWR : ∀ x, 0 ≤ x → M.u1W μS x ≤ M.R := by
    intro x hx
    unfold Model.u1W
    have := hwnn ((x + M.lamE) / (M.mu - μS)) (div_nonneg (by linarith) hW.le)
    nlinarith
  rcases eq_or_lt_of_le hμS.1 with h0 | hpos
  · -- μS = 0: only walk / balk
    by_cases hA : M.u1W μS M.lam ≥ 0
    · refine ⟨⟨0, M.lam, 0⟩, le_rfl, hlam.le, le_rfl, by simp, fun h => by linarith,
        fun _ => rfl, fun h => by simp at h, fun _ => ⟨hA, fun h => by linarith⟩,
        fun h => by simp at h⟩
    push Not at hA
    by_cases hB : M.u1W μS 0 ≤ 0
    · refine ⟨⟨0, 0, M.lam⟩, le_rfl, le_rfl, hlam.le, by simp, fun h => by linarith,
        fun _ => rfl, fun h => by simp at h, fun h => by simp at h,
        fun _ => ⟨hB, fun h => by linarith⟩⟩
    push Not at hB
    obtain ⟨x, hx, hxz⟩ := OWSC_D3.walk_balk M hM μS hμS M.lam hlam.le hB hA
    refine ⟨⟨0, x, M.lam - x⟩, le_rfl, hx.1.le, by linarith [hx.2], by simp, fun h => by linarith,
      fun _ => rfl, fun h => by simp at h, fun _ => ⟨by simp [hxz], fun h => by linarith⟩,
      fun _ => ⟨by simp [hxz], fun h => by linarith⟩⟩
  · -- μS > 0
    set s0 := 2 * M.R * μS ^ 2 / (M.CD + 2 * M.R * μS) with hs0
    have hden : 0 < M.CD + 2 * M.R * μS := by positivity
    have hs0pos : 0 < s0 := by positivity
    have hs0lt : s0 < μS := by
      rw [hs0, div_lt_iff₀ hden]; nlinarith
    have hu1S_nonneg : ∀ t, 0 ≤ t → t ≤ s0 → 0 ≤ M.u1S μS t := by
      intro t ht hts
      have htm : t < μS := lt_of_le_of_lt hts hs0lt
      unfold Model.u1S dbar
      have hd' : 0 < μS - t := by linarith
      have hd : 0 < 2 * μS * (μS - t) := by positivity
      rw [hs0, le_div_iff₀ hden] at hts
      have key : M.CD * t ≤ M.R * (2 * μS * (μS - t)) := by nlinarith
      have : M.CD * (t / (2 * μS * (μS - t))) ≤ M.R := by
        rw [mul_div_assoc', div_le_iff₀ hd]; linarith
      linarith
    have hu1S_s0 : M.u1S μS s0 = 0 := by
      unfold Model.u1S dbar
      have : μS - s0 = M.CD * μS / (M.CD + 2 * M.R * μS) := by
        rw [hs0]; field_simp; ring
      rw [this, hs0]
      field_simp
      ring
    set m := min s0 M.lam with hm
    have hm0 : 0 < m := lt_min hs0pos hlam
    have hms0 : m ≤ s0 := min_le_left _ _
    have hmlam : m ≤ M.lam := min_le_right _ _
    have hmμ : m < μS := lt_of_le_of_lt hms0 hs0lt
    have hmcase : m < M.lam → m = s0 := by
      intro h
      rcases min_choice s0 M.lam with h' | h'
      · exact h'
      · have : m = M.lam := by rw [hm]; exact h'
        linarith
    by_cases hA : M.u1W μS 0 ≤ 0
    · -- regime SnB
      refine ⟨⟨m, 0, M.lam - m⟩, hm0.le, le_rfl, by linarith, by simp, fun _ => hmμ,
        fun h => by linarith, fun _ => ⟨?_, hu1S_nonneg m hm0.le hms0⟩,
        fun h => by simp at h, fun h => ⟨hA, fun _ => ?_⟩⟩
      · simp only
        linarith [hu1S_nonneg m hm0.le hms0]
      · simp only at h
        rw [hmcase (by linarith), hu1S_s0]
    push Not at hA
    by_cases hB : M.u1W μS (M.lam - m) < 0
    · -- regime SWB
      obtain ⟨x, hx, hxz⟩ := OWSC_D3.walk_balk M hM μS hμS (M.lam - m) (by linarith) hA hB
      have hml : m < M.lam := by linarith [hx.1, hx.2]
      have hu0 : M.u1S μS m = 0 := by rw [hmcase hml, hu1S_s0]
      refine ⟨⟨m, x, M.lam - m - x⟩, hm0.le, hx.1.le, by linarith [hx.2], by simp, fun _ => hmμ,
        fun h => by linarith, fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, fun _ => ?_⟩,
        fun _ => ⟨?_, fun _ => ?_⟩⟩ <;> simp only <;> simp [hxz, hu0]
    push Not at hB
    -- regime SnW / interior
    have hwc := OWSC_D3.w_continuousOn M.w hM.w_convex hM.w_strictMono hM.w_zero
    set h : ℝ → ℝ := fun t => M.u1S μS t - M.u1W μS (M.lam - t) with hh
    by_cases hC : 0 ≤ h m
    · have hcase : M.lam - m > 0 → M.u1W μS (M.lam - m) = M.u1S μS m := by
        intro hp
        have hml : m < M.lam := by linarith
        have hu0 : M.u1S μS m = 0 := by rw [hmcase hml, hu1S_s0]
        simp only [hh] at hC
        rw [hu0] at hC ⊢; linarith
      refine ⟨⟨m, M.lam - m, 0⟩, hm0.le, by linarith, le_rfl, by simp, fun _ => hmμ,
        fun h => by linarith, fun _ => ⟨?_, hu1S_nonneg m hm0.le hms0⟩,
        fun hp => ⟨hB, fun _ => (hcase hp).ge⟩, fun h => by simp at h⟩
      simp only [hh] at hC
      simp only; linarith
    push Not at hC
    have hhc : ContinuousOn h (Icc 0 m) := by
      have h1 : ContinuousOn (fun t => M.u1S μS t) (Icc 0 m) := by
        unfold Model.u1S dbar
        apply continuousOn_const.sub
        apply continuousOn_const.mul
        apply ContinuousOn.div continuousOn_id
        · exact (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
        · intro t ht
          have : 0 < μS - t := by linarith [ht.2]
          positivity
      have harg : ContinuousOn (fun t : ℝ => (M.lam - t + M.lamE) / (M.mu - μS)) (Icc 0 m) :=
        (((continuous_const.sub continuous_id).add continuous_const).div_const _).continuousOn
      have hmaps : MapsTo (fun t : ℝ => (M.lam - t + M.lamE) / (M.mu - μS)) (Icc 0 m) (Ici 0) := by
        intro t ht
        exact Set.mem_Ici.2 (div_nonneg (by linarith [ht.2]) hW.le)
      have h2 : ContinuousOn (fun t => M.u1W μS (M.lam - t)) (Icc 0 m) := by
        unfold Model.u1W
        exact continuousOn_const.sub (continuousOn_const.mul (hwc.comp harg hmaps))
      exact h1.sub h2
    have hh0 : 0 ≤ h 0 := by
      simp only [hh]
      have : M.u1S μS 0 = M.R := by simp [Model.u1S, dbar]
      rw [this, sub_zero]; linarith [hWR M.lam hlam.le]
    obtain ⟨t, ht, htz⟩ := intermediate_value_Icc' hm0.le hhc ⟨hC.le, hh0⟩
    have heq : M.u1S μS t = M.u1W μS (M.lam - t) := by
      have : h t = 0 := htz
      simp only [hh] at this; linarith
    have hS0 : 0 ≤ M.u1S μS t := hu1S_nonneg t ht.1 (le_trans ht.2 hms0)
    refine ⟨⟨t, M.lam - t, 0⟩, ht.1, by linarith [ht.2], le_rfl, by simp,
      fun _ => lt_of_le_of_lt ht.2 hmμ, fun h => by linarith,
      fun _ => ⟨heq.ge, hS0⟩, fun _ => ⟨by simp only; linarith, fun _ => heq.le⟩,
      fun h => by simp at h⟩
