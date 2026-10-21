-- Prove2me | solution 1 for RetailerMarketplace.Entry.eq_A2_vStar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:37:40.472987+00:00
-- url     : https://prove2.me/submissions/c64392c8-296c-4dcd-a33f-1e46c0df781b

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

set_option autoImplicit false
open RetailerMarketplace.Entry

theorem rme_hD (f lam : ℝ) (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - f * (1 - lam) := by
  obtain ⟨hf0, hf1⟩ := hf
  obtain ⟨hl0, hl1⟩ := hlam
  nlinarith [mul_nonneg hf0 hl0]

theorem rme_dpi (c f lam v : ℝ) (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    dPi c f lam v = (v - vT c f) * ((1 - f) * (lam - f * (1 - lam))) / (1 - f * (1 - lam)) := by
  have hD := (rme_hD f lam hf hlam).ne'
  have hE : (1 - f) ≠ 0 := by linarith [hf.2]
  unfold dPi piSBMT_M piSBT_M pbarT vT
  generalize hDd : 1 - f * (1 - lam) = D at hD ⊢
  generalize hEd : 1 - f = E at hE ⊢
  field_simp
  subst hDd
  subst hEd
  ring

theorem rme_K (f lam : ℝ) (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) :
    0 < lam - f * (1 - lam) := by
  obtain ⟨hf0, hf1⟩ := hf
  obtain ⟨hl0, hl1⟩ := hlam
  rcases lt_or_eq_of_le hl0 with h | h
  · nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hf1.le)]
  · subst h; nlinarith

theorem solution (c f lam : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) :
    dPi c f lam (vStar c f lam) = piSBM c (vT c f) ∧
      vT c f ≤ vStar c f lam ∧
      (0 < f → vT c f < vStar c f lam) ∧
      (f = 0 → vStar c f lam = c ∧ vT c f = c) ∧
      (∀ v u : ℝ, vStar c f lam ≤ v → u < vT c f → piSBM c u < dPi c f lam v) := by
  have hlam0 : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hlam.1], hlam.2⟩
  have h1 : 0 < 1 - f := by linarith [hf.2]
  have hD := rme_hD f lam hf hlam0
  have hK := rme_K f lam hf hlam
  have hdiff : vStar c f lam - vT c f = c * f * (1 - f * (1 - lam)) / ((1 - f) ^ 2 * (lam - f * (1 - lam))) := by
    unfold vStar vT
    field_simp
    ring
  have hge : vT c f ≤ vStar c f lam := by
    have : 0 ≤ c * f * (1 - f * (1 - lam)) / ((1 - f) ^ 2 * (lam - f * (1 - lam))) := by
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg hc.le hf.1) hD.le
      · exact (mul_pos (pow_pos h1 2) hK).le
    linarith
  have hd1 : dPi c f lam (vStar c f lam) = piSBM c (vT c f) := by
    rw [rme_dpi c f lam _ hf hlam0]
    unfold vStar vT piSBM
    field_simp
    ring
  refine ⟨hd1, hge, ?_, ?_, ?_⟩
  · intro hf0
    have : 0 < c * f * (1 - f * (1 - lam)) / ((1 - f) ^ 2 * (lam - f * (1 - lam))) := by
      apply div_pos
      · exact mul_pos (mul_pos hc hf0) hD
      · exact mul_pos (pow_pos h1 2) hK
    linarith
  · intro hf0
    subst hf0
    have hl : lam ≠ 0 := by linarith [hlam.1]
    refine ⟨?_, ?_⟩
    · unfold vStar; field_simp; ring
    · unfold vT; simp
  · intro v u hv hu
    have hmono : dPi c f lam (vStar c f lam) ≤ dPi c f lam v := by
      rw [rme_dpi c f lam _ hf hlam0, rme_dpi c f lam v hf hlam0]
      have : 0 < (1 - f) * (lam - f * (1 - lam)) / (1 - f * (1 - lam)) := div_pos (mul_pos h1 hK) hD
      have e : ∀ x, (x - vT c f) * ((1 - f) * (lam - f * (1 - lam))) / (1 - f * (1 - lam)) =
          (x - vT c f) * ((1 - f) * (lam - f * (1 - lam)) / (1 - f * (1 - lam))) := by
        intro x; ring
      rw [e, e]
      exact mul_le_mul_of_nonneg_right (by linarith) this.le
    unfold piSBM at hd1 ⊢
    linarith
