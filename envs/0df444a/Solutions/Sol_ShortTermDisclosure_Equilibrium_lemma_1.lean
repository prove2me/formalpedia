-- Prove2me | solution 1 for ShortTermDisclosure.Equilibrium.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:28:31.611459+00:00
-- url     : https://prove2.me/submissions/0a89fdee-c26b-4c12-a135-21aa9855b4e2

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace Aux_STD_l1

open ShortTermDisclosure.Equilibrium MeasureTheory

lemma cm_eq (muhi t : ℝ) (ht : t ≤ muhi) : condMeanAbove muhi t = (t + muhi) / 2 := by
  unfold condMeanAbove
  split_ifs with h
  · rw [integral_id]
    have : muhi - t ≠ 0 := by linarith
    field_simp
    ring
  · have : t = muhi := le_antisymm ht (not_lt.mp h)
    rw [this]; ring

lemma thr (η muhi x t : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hx : muhi / 2 < x)
    (hbr : IsSHBestResponse η muhi x t) : (2 - η) * t = 2 * x - η * muhi := by
  obtain ⟨ht0, ht1, hup, hlow⟩ := hbr
  have hcm := cm_eq muhi t ht1
  have hmu : 0 ≤ muhi := le_trans ht0 ht1
  have htpos : 0 < t := by
    by_contra h
    push_neg at h
    have h0 : t = 0 := le_antisymm h ht0
    have := hup 0 ⟨le_rfl, hmu⟩ (by rw [h0])
    unfold netBenefit at this
    rw [hcm, h0] at this
    nlinarith [mul_le_mul_of_nonneg_right hη1 hmu]
  have g1 : 0 ≤ η * ((t + muhi) / 2) + (1 - η) * t - x := by
    have := hup t ⟨ht0, ht1⟩ le_rfl
    unfold netBenefit at this; rwa [hcm] at this
  have g2 : η * ((t + muhi) / 2) + (1 - η) * t - x ≤ 0 := by
    by_contra hg
    push_neg at hg
    set g := η * ((t + muhi) / 2) + (1 - η) * t - x with hgd
    set ε := min t g / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min htpos hg)
    have hεt : ε ≤ t / 2 := by rw [hε]; linarith [min_le_left t g]
    have hεg : ε ≤ g / 2 := by rw [hε]; linarith [min_le_right t g]
    have := hlow (t - ε) ⟨by linarith, by linarith⟩ (by linarith)
    unfold netBenefit at this
    rw [hcm] at this
    nlinarith
  nlinarith

end Aux_STD_l1

open ShortTermDisclosure.Equilibrium Aux_STD_l1 in
theorem solution (η muhi x t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hm : 0 < muhi)
    (hx0 : muhi / 2 < x) (hx1 : x < muhi) :
    IsSHBestResponse η muhi x t ↔
      t = (1 + lam η) * x - lam η * muhi := by
  have h2η : 0 < 2 - η := by linarith
  have hlam : lam η = η / (2 - η) := rfl
  constructor
  · intro hbr
    have := thr η muhi x t hη0 hη1 hx0 hbr
    rw [hlam]; field_simp; linarith
  · intro ht
    have ht' : (2 - η) * t = 2 * x - η * muhi := by
      rw [ht, hlam]; field_simp; ring
    have ht0 : 0 < t := by
      by_contra h; push_neg at h; nlinarith
    have ht1 : t < muhi := by
      by_contra h; push_neg at h; nlinarith
    have hcm := cm_eq muhi t ht1.le
    refine ⟨ht0.le, ht1.le, ?_, ?_⟩
    · intro mu _ hmu
      unfold netBenefit; rw [hcm]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - η) (by linarith : (0:ℝ) ≤ mu - t)]
    · intro mu _ hmu
      unfold netBenefit; rw [hcm]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - η) (by linarith : (0:ℝ) ≤ t - mu)]
