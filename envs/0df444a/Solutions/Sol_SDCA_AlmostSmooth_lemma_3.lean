-- Prove2me | solution 1 for SDCA.AlmostSmooth.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:36:54.317242+00:00
-- url     : https://prove2.me/submissions/bdbe111a-011d-4cfc-8cf5-c35d8b79aa43

import Mathlib
import Definitions.Def_SDCA_Lipschitz_conj

set_option autoImplicit false
open SDCA.Lipschitz

theorem solution (φ : ℝ → ℝ) (L : ℝ) (hL : ∀ a b : ℝ, |φ a - φ b| ≤ L * |a - b|)
    (α : ℝ) (hα : L < |α|) :
    conj φ α = ⊤ := by
  unfold conj
  rw [iSup_eq_top]
  intro b hb
  obtain ⟨r, hbr, -⟩ := EReal.lt_iff_exists_real_btwn.mp hb
  set ε : ℝ := |α| - L with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  -- choose z = t * sign α with t large
  set t : ℝ := (max 0 (r + φ 0 + 1)) / ε with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htε : t * ε = max 0 (r + φ 0 + 1) := by rw [ht]; field_simp
  set z : ℝ := t * SignType.sign α with hz
  have hαne : α ≠ 0 := by
    intro h; rw [h] at hα; simp at hα
    have : (0:ℝ) ≤ L := by
      have := hL 1 0; simp at this; exact (abs_nonneg _).trans this
    linarith
  have hzα : z * α = t * |α| := by
    rw [hz]
    rcases lt_or_gt_of_ne hαne with h | h
    · simp [h, abs_of_neg h]
    · simp [h, abs_of_pos h]
  have hzabs : |z| = t := by
    rw [hz]
    rcases lt_or_gt_of_ne hαne with h | h
    · simp [h, abs_of_nonneg ht0]
    · simp [h, abs_of_nonneg ht0]
  refine ⟨z, ?_⟩
  refine lt_trans hbr ?_
  rw [EReal.coe_lt_coe_iff]
  have h1 := hL z 0
  have h2 : |φ z - φ 0| ≤ L * t := by simpa [hzabs] using h1
  have h3 := (abs_le.mp h2).2
  have h4 : r + 1 ≤ t * ε - φ 0 := by
    rw [htε]; linarith [le_max_right 0 (r + φ 0 + 1)]
  have h5 : t * |α| = t * ε + L * t := by rw [hε]; ring
  show r < z * α - φ z
  rw [hzα, h5]
  linarith
