-- Prove2me | solution 1 for RetailerMarketplace.UnitFee.lemma_B_1_sbmt_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:29:48.141664+00:00
-- url     : https://prove2.me/submissions/39b6ceaf-2ad7-4b32-829d-b397b0a05053

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

set_option autoImplicit false
open MeasureTheory RetailerMarketplace.UnitFee

theorem solution (c fs ts ε f' t' lam : ℝ) (hc : 0 < c)
    (hfs : fs ∈ Set.Ico (0 : ℝ) 1) (hε : 0 < ε) (hεts : ε < ts)
    (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hf' : f' = (ε + fs * (c + ts - ε)) / (c + ts)) (ht' : t' = ts - ε) (v : ℝ) :
    pbarT c f' t' lam v * f' + t' > pbarT c fs ts lam v * fs + ts ↔ vT c fs ts < v := by
  obtain ⟨hf0, hf1⟩ := hfs
  obtain ⟨hl1, hl2⟩ := hlam
  have hpos : 0 < c + ts := by linarith
  have h1 : 0 < 1 - fs := by linarith
  have hD : 0 < 1 - fs * (1 - lam) := by nlinarith
  have hc' : 0 < c + ts - ε := by linarith
  have e1 : 1 - f' = (1 - fs) * (c + ts - ε) / (c + ts) := by
    rw [hf']; field_simp; ring
  have hD' : 0 < 1 - f' * (1 - lam) := by
    have : f' < 1 := by
      have : 0 < 1 - f' := by rw [e1]; positivity
      linarith
    have : 0 ≤ f' := by
      rw [hf']; apply div_nonneg _ hpos.le
      have : 0 ≤ c + ts - ε := hc'.le
      positivity
    nlinarith
  have key : pbarT c f' t' lam v * f' + t' - (pbarT c fs ts lam v * fs + ts)
      = ε * lam * ((1 - fs) * v - (c + ts)) / ((1 - fs * (1 - lam)) * (1 - f' * (1 - lam)) * (c + ts)) := by
    have hP : pbarT c f' t' lam v * (1 - f' * (1 - lam)) = lam * v + (1 - lam) * (c + t') := by
      unfold pbarT; exact div_mul_cancel₀ _ hD'.ne'
    have hP0 : pbarT c fs ts lam v * (1 - fs * (1 - lam)) = lam * v + (1 - lam) * (c + ts) := by
      unfold pbarT; exact div_mul_cancel₀ _ hD.ne'
    set P' := pbarT c f' t' lam v
    set P0 := pbarT c fs ts lam v
    have hf'' : f' * (c + ts) = ε + fs * (c + ts - ε) := by rw [hf']; field_simp
    rw [eq_div_iff (by positivity)]
    subst ht'
    linear_combination (f' * (1 - fs * (1 - lam)) * (c + ts)) * hP
      - (fs * (1 - f' * (1 - lam)) * (c + ts)) * hP0
      + ((1 - lam) * (c + ts) + lam * v) * hf''
  unfold vT
  rw [div_lt_iff₀ h1, gt_iff_lt, ← sub_pos, key, div_pos_iff_of_pos_right (by positivity)]
  constructor <;> intro h
  · have h2 : 0 < (1 - fs) * v - (c + ts) := by
      have := pos_of_mul_pos_right h (by positivity)
      exact this
    nlinarith
  · exact mul_pos (mul_pos hε (by linarith)) (by nlinarith)
