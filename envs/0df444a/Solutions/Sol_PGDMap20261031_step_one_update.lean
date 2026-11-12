-- Prove2me | solution 1 for PGDMap20261031.step_one_update
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:49:16.254365+00:00
-- url     : https://prove2.me/submissions/f50cebcb-f56c-4e94-bd1b-c09ca3aff82a

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Stepsize

open PGDMap20261031 Filter Topology

private lemma denominator_pos (q h : ℝ) (hq : 0 ≤ q) (hh : validStep h) :
    0 < h * (2 - h + h * q) := by
  exact mul_pos hh.1 (add_pos_of_pos_of_nonneg (sub_pos.mpr hh.2) (mul_nonneg hh.1.le hq))

private lemma denominator_strict_mono (q h u : ℝ) (hq : 1 / 2 ≤ q)
    (hh : validStep h) (hu : validStep u) (hhu : h < u) :
    h * (2 - h + h * q) < u * (2 - u + u * q) := by
  have hsum : 0 < h + u := add_pos hh.1 hu.1
  have hbracket : 0 < 2 + (q - 1) * (u + h) := by
    nlinarith [hh.2, hu.2, mul_nonneg (by linarith : 0 ≤ q - 1 / 2) hsum.le]
  have hprod := mul_pos (sub_pos.mpr hhu) hbracket
  nlinarith only [hprod]

theorem solution : OneUpdateClaim := by
  constructor
  · intro q hq hqhalf
    let H : ℝ := 1 / (1 - q)
    have hden : 0 < 1 - q := by linarith
    have hH : validStep H := by
      constructor
      · exact div_pos (by norm_num) hden
      · apply (div_lt_iff₀ hden).2
        linarith
    refine ⟨hH, ?_⟩
    intro u hu huneq
    simp only [curve, if_pos (show (1 : ℕ) = 1 from rfl)]
    unfold curveOne
    apply (div_lt_div_iff₀ (denominator_pos q H hq hH) (denominator_pos q u hq hu)).2
    have hsq : 0 < (u - H) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr huneq)
    have hidentity : H * (2 - H + H * q) - u * (2 - u + u * q) =
        (1 - q) * (u - H) ^ 2 := by
      dsimp [H]
      field_simp [ne_of_gt hden]
      <;> ring
    nlinarith [mul_pos hden hsq]
  · intro q hq
    have hqpos : 0 < q := by linarith
    have hqnonneg : 0 ≤ q := hqpos.le
    have hboundary : ∀ h, validStep h → curveOne 2 q ≤ curveOne h q := by
      intro h hh
      have hdh := denominator_pos q h hqnonneg hh
      have hd2 : 0 < (2 : ℝ) * (2 - 2 + 2 * q) := by nlinarith
      have hbracket : 0 < 2 * q + (q - 1) * h := by
        nlinarith [hq, hh.2, mul_nonneg (by linarith : 0 ≤ q - 1 / 2) hh.1.le]
      have hprod := mul_pos (sub_pos.mpr hh.2) hbracket
      unfold curveOne
      apply (div_le_div_iff₀ hd2 hdh).2
      nlinarith only [hprod]
    have hbelow : BddBelow (oneStepValues q) := by
      refine ⟨curveOne 2 q, ?_⟩
      rintro v ⟨h, hh, rfl⟩
      exact hboundary h hh
    have hnonempty : (oneStepValues q).Nonempty :=
      ⟨curveOne 1 q, 1, ⟨by norm_num, by norm_num⟩, rfl⟩
    have hcont : ContinuousAt (fun h : ℝ => curveOne h q) 2 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      have : 0 < (2 : ℝ) * (2 - 2 + 2 * q) := by nlinarith
      exact ne_of_gt this
    have hevent : ∀ᶠ h : ℝ in 𝓝[<] 2, validStep h := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 2))] with h hlt hgt
      exact ⟨hgt, hlt⟩
    have hlimit : Tendsto (fun h : ℝ => curveOne h q) (𝓝[<] 2) (𝓝 (curveOne 2 q)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hsinf : sInf (oneStepValues q) = curveOne 2 q := by
      apply le_antisymm
      · apply ge_of_tendsto hlimit
        exact hevent.mono (fun h hh => csInf_le hbelow ⟨h, hh, rfl⟩)
      · exact le_csInf hnonempty (by
          rintro v ⟨h, hh, rfl⟩
          exact hboundary h hh)
    constructor
    · intro h hh
      let u := (h + 2) / 2
      have hu : validStep u := by dsimp [u]; constructor <;> linarith [hh.1, hh.2]
      refine ⟨u, hu, ?_⟩
      have hless : h < u := by dsimp [u]; linarith [hh.2]
      unfold curveOne
      apply (div_lt_div_iff₀ (denominator_pos q u hqnonneg hu)
        (denominator_pos q h hqnonneg hh)).2
      linarith [denominator_strict_mono q h u hq hh hu hless]
    · rw [hsinf]
      exact hlimit
