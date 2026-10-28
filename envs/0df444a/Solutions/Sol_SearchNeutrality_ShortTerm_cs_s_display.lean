-- Prove2me | solution 1 for SearchNeutrality.ShortTerm.cs_s_display
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:31:48.719908+00:00
-- url     : https://prove2.me/submissions/e48a7b7a-abe4-4194-bd64-5f0666277d84

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace Aux_SearchNeutrality_ShortTerm_cs_s_display

open SearchNeutrality.ShortTerm

lemma cont (a : ℝ) : Continuous (fun c : ℝ => max (a - c) 0) := by fun_prop

lemma Iint (a : ℝ) (ha : a ≤ 1) :
    ∫ c in (0 : ℝ)..1, max (a - c) 0 = (max a 0) ^ 2 / 2 := by
  rcases le_or_gt a 0 with h | h
  · rw [max_eq_right h]
    have : ∫ c in (0 : ℝ)..1, max (a - c) 0 = ∫ c in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro c hc
      rw [Set.uIcc_of_le zero_le_one] at hc
      simp only
      exact max_eq_right (by linarith [hc.1])
    rw [this]
    simp
  · rw [max_eq_left h.le]
    rw [← intervalIntegral.integral_add_adjacent_intervals ((cont a).intervalIntegrable 0 a)
      ((cont a).intervalIntegrable a 1)]
    have h1 : ∫ c in (0 : ℝ)..a, max (a - c) 0 = ∫ c in (0 : ℝ)..a, (a - c) := by
      apply intervalIntegral.integral_congr
      intro c hc
      rw [Set.uIcc_of_le h.le] at hc
      simp only
      exact max_eq_left (by linarith [hc.2])
    have h2 : ∫ c in a..1, max (a - c) 0 = ∫ c in a..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro c hc
      rw [Set.uIcc_of_le ha] at hc
      simp only
      exact max_eq_right (by linarith [hc.1])
    rw [h1, h2, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
    ring

lemma Tint (ρ1 ρ2 p1 p2 : ℝ) (h1 : ρ2 * (p1 - p2) ≤ 1) (h2 : ρ2 * (1 - p2) ≤ 1) :
    ∫ c in (0 : ℝ)..1, typeSurplus ρ1 ρ2 p1 p2 c =
      ρ1 * (1 - p1) + ρ1 * ((max (ρ2 * (p1 - p2)) 0) ^ 2 / 2) +
        (1 - ρ1) * ((max (ρ2 * (1 - p2)) 0) ^ 2 / 2) := by
  unfold typeSurplus
  have i1 := (cont (ρ2 * (p1 - p2))).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have i2 := (cont (ρ2 * (1 - p2))).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [intervalIntegral.integral_add ((intervalIntegrable_const.add i1).const_mul ρ1)
    (i2.const_mul (1 - ρ1))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const i1, Iint _ h1, Iint _ h2]
  simp
  ring

end Aux_SearchNeutrality_ShortTerm_cs_s_display

open Aux_SearchNeutrality_ShortTerm_cs_s_display in
open SearchNeutrality.ShortTerm in
theorem solution (ρH ρL : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (α pF pT : ℝ) (hpF : pF ∈ Set.Icc (0 : ℝ) 1) (hpT : pT ∈ Set.Icc (0 : ℝ) 1) :
    consumerSurplus ρH ρL α neutral pF pT = csS ρH ρL α pF pT := by
  obtain ⟨hF0, hF1⟩ := hpF
  obtain ⟨hT0, hT1⟩ := hpT
  have hb : ∀ x : ℝ, x ≤ 1 → ρL * x ≤ 1 := fun x hx => by
    rcases le_or_gt x 0 with h | h
    · nlinarith
    · nlinarith
  unfold consumerSurplus
  rw [show (Finset.univ : Finset CType) = {CType.f, CType.t} from rfl,
    Finset.sum_pair (by decide)]
  simp only [neutral, Product.other, matchProb, price, mass]
  rw [Tint _ _ _ _ (hb _ (by linarith)) (hb _ (by linarith)),
    Tint _ _ _ _ (hb _ (by linarith)) (hb _ (by linarith))]
  rw [max_eq_left (by nlinarith : (0:ℝ) ≤ ρL * (1 - pT)),
    max_eq_left (by nlinarith : (0:ℝ) ≤ ρL * (1 - pF))]
  unfold csS
  rcases le_or_gt pT pF with h | h
  · rw [max_eq_left (by nlinarith : (0:ℝ) ≤ ρL * (pF - pT)),
      max_eq_right (by nlinarith : ρL * (pT - pF) ≤ 0), if_pos h]
    ring
  · rw [max_eq_right (by nlinarith : ρL * (pF - pT) ≤ 0),
      max_eq_left (by nlinarith : (0:ℝ) ≤ ρL * (pT - pF)), if_neg (not_le.2 h)]
    ring
