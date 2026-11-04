-- Prove2me | solution 1 for SearchNeutrality.Commission.cs_ns_display_half
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:53:47.003248+00:00
-- url     : https://prove2.me/submissions/2ac812cb-9e7c-47a4-adee-b68411f3fa12

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model
import Definitions.Def_SearchNeutrality_Commission_ClosedForms

open SearchNeutrality.Commission

lemma sumC' (g : CType → ℝ) : ∑ k : CType, g k = g .f + g .t := by
  rw [show (Finset.univ : Finset CType) = {.f, .t} from rfl]
  rw [Finset.sum_pair (by decide)]

lemma int_pos_part (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ c in (0:ℝ)..1, max (a - c) 0 = a ^ 2 / 2 := by
  have hc : Continuous (fun c : ℝ => max (a - c) 0) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ c in (0:ℝ)..a, max (a - c) 0 = ∫ c in (0:ℝ)..a, (a - c) := by
    apply intervalIntegral.integral_congr
    intro c hc'
    rw [Set.uIcc_of_le ha0] at hc'
    exact max_eq_left (by linarith [hc'.2])
  have h2 : ∫ c in a..1, max (a - c) 0 = ∫ c in a..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro c hc'
    rw [Set.uIcc_of_le ha1] at hc'
    exact max_eq_right (by linarith [hc'.1])
  rw [h1, h2, intervalIntegral.integral_sub ((by fun_prop : Continuous _).intervalIntegrable _ _) ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  simp
  ring

lemma int_typeSurplus (ρ1 ρ2 p1 p2 : ℝ) (h1 : 0 ≤ ρ2 * (p1 - p2)) (h1' : ρ2 * (p1 - p2) ≤ 1)
    (h2 : 0 ≤ ρ2 * (1 - p2)) (h2' : ρ2 * (1 - p2) ≤ 1) :
    ∫ c in (0:ℝ)..1, typeSurplus ρ1 ρ2 p1 p2 c
      = ρ1 * (1 - p1 + (ρ2 * (p1 - p2)) ^ 2 / 2) + (1 - ρ1) * ((ρ2 * (1 - p2)) ^ 2 / 2) := by
  unfold typeSurplus
  have ca : Continuous (fun c : ℝ => max (ρ2 * (p1 - p2) - c) 0) := by fun_prop
  have cb : Continuous (fun c : ℝ => max (ρ2 * (1 - p2) - c) 0) := by fun_prop
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _) ((by fun_prop : Continuous _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _) (ca.intervalIntegrable _ _),
    int_pos_part _ h1 h1', int_pos_part _ h2 h2']
  simp

theorem solution (ρH ρL : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (pF pT : ℝ) (hpF : pF ∈ Set.Icc (0 : ℝ) 1) (hpT : pT ∈ Set.Icc (0 : ℝ) 1) (hle : pT ≤ pF) :
    consumerSurplus ρH ρL (1 / 2) fPrimeAll pF pT = csNS ρH ρL (1 / 2) pF pT := by
  obtain ⟨hp0, hp1⟩ := hpF
  obtain ⟨hq0, hq1⟩ := hpT
  have hH0 : 0 < ρH := by linarith
  unfold consumerSurplus
  rw [sumC']
  simp only [fPrimeAll, matchProb, Product.other, price, mass]
  rw [int_typeSurplus _ _ _ _ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith),
    int_typeSurplus _ _ _ _ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)]
  unfold csNS
  ring
