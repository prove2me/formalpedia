-- Prove2me | solution 1 for OutpatientWalkIn.SmallCap.proposition_1_obs_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:53:36.72836+00:00
-- url     : https://prove2.me/submissions/54e4bf5d-651c-4351-9b39-26a45c9ce87e

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Definitions.Def_OutpatientWalkIn_SmallCap_Setting
import Theorems.Thm_OutpatientWalkIn_SmallCap_proposition_C_2_delta
import Theorems.Thm_OutpatientWalkIn_SmallCap_blockProb_pos

namespace P6ExCore

open OutpatientWalkIn.SmallCap Set

/-- A convex function on `[0,∞)`, increasing, with `w 0 = 0`, is continuous on `[0,∞)`. -/
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

theorem exists_core (M : Model) (hM : M.Standing) (μS : ℝ) (hμS : μS ∈ Ico 0 M.mu)
    (hpos : ∀ δ, 0 ≤ δ → 0 < blockProb M.lam δ μS)
    (hcont : ContinuousOn (fun δ => blockProb M.lam δ μS) (Ici 0)) :
    ∃ e : ObsStrategy, M.IsObsEq μS e := by
  have hlam := hM.lam_pos
  have hlamE := hM.lamE_nonneg
  have hR := hM.R_pos
  have hCD := hM.CD_pos
  have hCW := hM.CW_pos
  have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
  have hwc := w_continuousOn M.w hM.w_convex hM.w_strictMono hM.w_zero
  set π : ℝ → ℝ := fun δ => blockProb M.lam δ μS with hπdef
  set g : ℝ → ℝ := fun p => M.u2W μS p with hgdef
  have hgc : ContinuousOn g (Ici 0) := by
    have harg : ContinuousOn (fun p : ℝ => (M.lamE + p * M.lam) / (M.mu - μS)) (Ici 0) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).div_const _).continuousOn
    have hmaps : MapsTo (fun p : ℝ => (M.lamE + p * M.lam) / (M.mu - μS)) (Ici 0) (Ici 0) := by
      intro p hp
      exact Set.mem_Ici.2 (div_nonneg (by have := Set.mem_Ici.1 hp; positivity) hW.le)
    have := hwc.comp harg hmaps
    exact continuousOn_const.sub (continuousOn_const.mul this)
  have hgw : ∀ p, 0 ≤ p → g p ≤ M.R := by
    intro p hp
    have : 0 ≤ M.w ((M.lamE + p * M.lam) / (M.mu - μS)) := by
      rw [← hM.w_zero]
      exact hM.w_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl)
        (Set.mem_Ici.2 (div_nonneg (by positivity) hW.le))
        (div_nonneg (by positivity) hW.le)
    show M.R - M.CW * _ ≤ M.R
    nlinarith
  set δR := M.R / M.CD with hδR
  have hδR0 : 0 ≤ δR := div_nonneg hR.le hCD.le
  have hCDδR : M.CD * δR = M.R := by rw [hδR]; field_simp
  set πR := π δR
  have hπR : 0 < πR := hpos δR hδR0
  by_cases h1 : g 0 ≤ 0
  · -- Regime SnB
    refine ⟨⟨δR, 0, πR⟩, hδR0, le_rfl, hπR.le, by simpa using hπR, ?_, ?_, ?_, ?_, ?_⟩
    · intro d _ hd
      simp only [zero_div, zero_mul, zero_add, u2B, mul_zero]
      unfold Model.u2S
      have : M.CD * d ≤ M.CD * δR := mul_le_mul_of_nonneg_left hd hCD.le
      linarith
    · intro d hd
      simp only [zero_div, zero_mul, zero_add, u2B, mul_zero]
      unfold Model.u2S
      have : M.CD * δR < M.CD * d := mul_lt_mul_of_pos_left hd hCD
      linarith
    · simp [πR, π]
    · left; rfl
    · right; exact h1
  push_neg at h1
  by_cases h2 : 0 ≤ g πR
  · -- Regime SnW: solve R - C_D δ = u²_W(π(δ)) on [0, R/C_D]
    set h : ℝ → ℝ := fun δ => M.R - M.CD * δ - g (π δ)
    have hhc : ContinuousOn h (Icc 0 δR) := by
      have hπc : ContinuousOn π (Icc 0 δR) := hcont.mono Icc_subset_Ici_self
      have hmaps : MapsTo π (Icc 0 δR) (Ici 0) := fun δ hδ =>
        Set.mem_Ici.2 (hpos δ hδ.1).le
      exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).sub
        (hgc.comp hπc hmaps)
    have ha : 0 ≤ h 0 := by
      show 0 ≤ M.R - M.CD * 0 - g (π 0)
      have := hgw (π 0) (hpos 0 le_rfl).le
      linarith
    have hb : h δR ≤ 0 := by
      show M.R - M.CD * δR - g (π δR) ≤ 0
      rw [hCDδR]; linarith
    obtain ⟨δs, hδs, hδsz⟩ := intermediate_value_Icc' hδR0 hhc ⟨hb, ha⟩
    have hz : M.R - M.CD * δs = g (π δs) := by
      have : h δs = 0 := hδsz
      simp only [h] at this; linarith
    have hpδ : 0 < π δs := hpos δs hδs.1
    have hU : π δs / (π δs + 0) * M.u2W μS (π δs) + 0 / (π δs + 0) * u2B = g (π δs) := by
      rw [add_zero, div_self hpδ.ne']; simp [u2B, g]
    refine ⟨⟨δs, π δs, 0⟩, hδs.1, hpδ.le, le_rfl, by simpa using hpδ, ?_, ?_, ?_, ?_, ?_⟩
    · intro d _ hd
      show M.u2S d ≥ π δs / (π δs + 0) * M.u2W μS (π δs) + 0 / (π δs + 0) * u2B
      rw [hU]; unfold Model.u2S
      have : M.CD * d ≤ M.CD * δs := mul_le_mul_of_nonneg_left hd hCD.le
      linarith
    · intro d hd
      show M.u2S d < π δs / (π δs + 0) * M.u2W μS (π δs) + 0 / (π δs + 0) * u2B
      rw [hU]; unfold Model.u2S
      have : M.CD * δs < M.CD * d := mul_lt_mul_of_pos_left hd hCD
      linarith
    · show π δs + 0 = blockProb M.lam δs μS
      simp [π]
    · right
      show g (π δs) ≥ u2B
      rw [← hz]; unfold u2B
      have : M.CD * δs ≤ M.CD * δR := mul_le_mul_of_nonneg_left hδs.2 hCD.le
      linarith
    · left; rfl
  push_neg at h2
  · -- Regime SWB: δ = R/C_D, u²_W(p_W) = 0
    have hgc' : ContinuousOn g (Icc 0 πR) := hgc.mono Icc_subset_Ici_self
    obtain ⟨ps, hps, hpsz⟩ := intermediate_value_Icc' hπR.le hgc' ⟨h2.le, h1.le⟩
    have hps0 : 0 < ps := by
      rcases eq_or_lt_of_le hps.1 with h | h
      · rw [← h] at hpsz; linarith
      · exact h
    have hpsR : ps < πR := by
      rcases eq_or_lt_of_le hps.2 with h | h
      · rw [h] at hpsz; linarith
      · exact h
    have hg0 : M.u2W μS ps = 0 := hpsz
    have hsum : ps + (πR - ps) = πR := by ring
    have hU : ps / (ps + (πR - ps)) * M.u2W μS ps + (πR - ps) / (ps + (πR - ps)) * u2B = 0 := by
      rw [hg0]; simp [u2B]
    refine ⟨⟨δR, ps, πR - ps⟩, hδR0, hps0.le, by linarith, by simpa [hsum] using hπR,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro d _ hd
      show M.u2S d ≥ ps / (ps + (πR - ps)) * M.u2W μS ps + (πR - ps) / (ps + (πR - ps)) * u2B
      rw [hU]; unfold Model.u2S
      have : M.CD * d ≤ M.CD * δR := mul_le_mul_of_nonneg_left hd hCD.le
      linarith
    · intro d hd
      show M.u2S d < ps / (ps + (πR - ps)) * M.u2W μS ps + (πR - ps) / (ps + (πR - ps)) * u2B
      rw [hU]; unfold Model.u2S
      have : M.CD * δR < M.CD * d := mul_lt_mul_of_pos_left hd hCD
      linarith
    · show ps + (πR - ps) = blockProb M.lam δR μS
      rw [hsum]
    · right; show M.u2W μS ps ≥ u2B; rw [hg0]; rfl
    · right; show M.u2W μS ps ≤ u2B; rw [hg0]; rfl

end P6ExCore

open OutpatientWalkIn.SmallCap

theorem solution (M : Model) (hM : M.Standing) (μS : ℝ) (hμS : μS ∈ Set.Ico 0 M.mu) :
    ∃ e : ObsStrategy, M.IsObsEq μS e := by
  rcases eq_or_lt_of_le hμS.1 with h0 | hpos
  · have hb : ∀ δ, blockProb M.lam δ μS = 1 := by
      intro δ; unfold blockProb; simp [← h0]
    refine P6ExCore.exists_core M hM μS hμS (fun δ _ => by rw [hb]; exact one_pos) ?_
    have : (fun δ => blockProb M.lam δ μS) = fun _ => (1:ℝ) := funext hb
    rw [this]; exact continuousOn_const
  · exact P6ExCore.exists_core M hM μS hμS
      (fun δ hδ => blockProb_pos M.lam hM.lam_pos μS hpos δ hδ)
      (proposition_C_2_delta M.lam hM.lam_pos μS hpos).2
