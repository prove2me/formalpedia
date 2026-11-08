-- Prove2me | solution 1 for OceanPlastic.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:39:26.328741+00:00
-- url     : https://prove2.me/submissions/7a678f16-98d8-4a1a-be46-d76e98538f60

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark

open OceanPlastic Params in
theorem solution (P : Params) :
    (∀ h q : ℝ, IsMaxOn (P.collectorUtility h) Set.univ q ↔ q = h / P.k) ∧
    (∀ h : ℝ, P.qt h = P.M * (h / P.k)) ∧
    (∀ h : ℝ, IsMaxOn P.processorObjB Set.univ h ↔ h = P.pm / 2) ∧
    P.qt (P.pm / 2) = P.VB ∧
    P.pm / 2 * P.qt (P.pm / 2) = P.PiBC ∧
    P.processorObjB (P.pm / 2) = P.PiBP ∧
    P.VB = P.M * P.pm / (2 * P.k) ∧
    P.PiBC = P.M * P.pm ^ 2 / (4 * P.k) ∧
    P.PiBP = P.M * P.pm ^ 2 / (4 * P.k) := by
  have hk := P.k_pos
  have hM := P.M_pos
  have hcu : ∀ h y, P.collectorUtility h (h / P.k) - P.collectorUtility h y =
      P.k / 2 * (y - h / P.k) ^ 2 := by
    intro h y; unfold collectorUtility; field_simp <;> ring
  have hpo : ∀ h, P.processorObjB (P.pm / 2) - P.processorObjB h =
      P.M / P.k * (h - P.pm / 2) ^ 2 := by
    intro h; unfold processorObjB qt; field_simp <;> ring
  refine ⟨fun h q => ?_, fun h => ?_, fun h => ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [isMaxOn_iff]
    constructor
    · intro H
      have h1 := H (h / P.k) (Set.mem_univ _)
      have h2 := hcu h q
      have h3 : P.k / 2 * (q - h / P.k) ^ 2 ≤ 0 := by linarith
      have h4 : (q - h / P.k) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (q - h / P.k)]) (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
      linarith
    · rintro rfl y _
      have h2 := hcu h y
      nlinarith [sq_nonneg (y - h / P.k)]
  · unfold qt; ring
  · rw [isMaxOn_iff]
    constructor
    · intro H
      have h1 := H (P.pm / 2) (Set.mem_univ _)
      have h2 := hpo h
      have h3 : P.M / P.k * (h - P.pm / 2) ^ 2 ≤ 0 := by linarith
      have hMk : 0 < P.M / P.k := div_pos hM hk
      have h4 : (h - P.pm / 2) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (h - P.pm / 2)]) (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
      linarith
    · rintro rfl y _
      have h2 := hpo y
      have hMk : 0 < P.M / P.k := div_pos hM hk
      nlinarith [sq_nonneg (y - P.pm / 2)]
  · unfold qt VB; field_simp <;> ring
  · unfold qt PiBC; field_simp <;> ring
  · unfold processorObjB qt PiBP; field_simp <;> ring
