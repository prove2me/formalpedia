-- Prove2me | solution 1 for ShortTermDisclosure.Equilibrium.benchmark
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:57:06.621164+00:00
-- url     : https://prove2.me/submissions/6ee46a52-ea4d-4b62-bd86-71acf45fdf00

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace Aux_STD_benchmark
open ShortTermDisclosure.Equilibrium

theorem mv_formula (muhi t v : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ muhi) :
    managerValue muhi t v = ((muhi ^ 2 - t ^ 2) / 2 + t * v) / muhi := by
  set f : ℝ → ℝ := fun mu => if t ≤ mu then mu else v with hf
  have hMV : managerValue muhi t v = (∫ mu in (0:ℝ)..muhi, f mu) / muhi := rfl
  have hI1 : IntervalIntegrable f MeasureTheory.volume 0 t := by
    apply (intervalIntegrable_const (c := v)).congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le ht0] at hx
    simp [hf, not_le.mpr hx.2]
  have hI2 : IntervalIntegrable f MeasureTheory.volume t muhi := by
    apply (intervalIntegral.intervalIntegrable_id).congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le ht1] at hx
    simp [hf, hx.1.le]
  have e1 : (∫ mu in (0:ℝ)..t, f mu) = t * v := by
    rw [intervalIntegral.integral_congr_Ioo_of_le ht0 (g := fun _ => v)]
    · simp
    · intro x hx
      simp [hf, not_le.mpr hx.2]
  have e2 : (∫ mu in t..muhi, f mu) = (muhi ^ 2 - t ^ 2) / 2 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le ht1 (g := fun x => x)]
    · simp [integral_id]
    · intro x hx
      simp [hf, hx.1.le]
  rw [hMV, ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, e1, e2]
  ring

theorem br_eq (muhi x t : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ muhi)
    (h : IsSHBestResponse 0 muhi x t) : t = x := by
  obtain ⟨ht0, ht1, hA, hB⟩ := h
  unfold netBenefit at hA hB
  rcases lt_trichotomy t x with hlt | heq | hgt
  · have := hA t ⟨ht0, ht1⟩ le_rfl
    linarith
  · exact heq
  · have := hB ((x + t) / 2) ⟨by linarith, by linarith⟩ (by linarith)
    linarith

end Aux_STD_benchmark

open ShortTermDisclosure.Equilibrium in
theorem solution (P : Params) (hP : P.Standing)
    (v N tD tN : ℝ) (hv : v ∈ Set.Icc P.vlo P.vhi)
    (hN : N ∈ Set.Icc P.vlo P.vhi)
    (hD : IsSHBestResponse 0 P.muhi v tD)
    (hND : IsSHBestResponse 0 P.muhi N tN) :
    managerValue P.muhi tD v - managerValue P.muhi tN v =
      (v - N) ^ 2 / (2 * P.muhi) ∧
    managerValue P.muhi tN v ≤ managerValue P.muhi tD v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hN1, hN2⟩ := hN
  have hm : 0 < P.muhi := by linarith
  have eD := Aux_STD_benchmark.br_eq P.muhi v tD (by linarith) (by linarith) hD
  have eN := Aux_STD_benchmark.br_eq P.muhi N tN (by linarith) (by linarith) hND
  subst eD eN
  rw [Aux_STD_benchmark.mv_formula P.muhi tD tD (by linarith) (by linarith),
    Aux_STD_benchmark.mv_formula P.muhi tN tD (by linarith) (by linarith)]
  have key : ((P.muhi ^ 2 - tD ^ 2) / 2 + tD * tD) / P.muhi -
      ((P.muhi ^ 2 - tN ^ 2) / 2 + tN * tD) / P.muhi = (tD - tN) ^ 2 / (2 * P.muhi) := by
    field_simp
    ring
  refine ⟨key, ?_⟩
  have : 0 ≤ (tD - tN) ^ 2 / (2 * P.muhi) := by positivity
  linarith
