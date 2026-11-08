-- Prove2me | solution 1 for OceanPlastic.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:28:29.895804+00:00
-- url     : https://prove2.me/submissions/be789fbf-3806-4b0a-a47b-b70cb68b847c

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark
import Definitions.Def_OceanPlastic_CaseO

open OceanPlastic OceanPlastic.Params in
theorem solution (P : Params) (rc rp : ℝ) (hrc : 0 ≤ rc) (hrp : 0 ≤ rp) (hdom : rc ≤ P.pm + rp) :
    (∀ h q : ℝ, IsMaxOn (P.collectorUtility (h + rc)) Set.univ q ↔ q = (h + rc) / P.k) ∧
    (∀ h : ℝ, P.qt (h + rc) = P.M * ((h + rc) / P.k)) ∧
    (∀ h : ℝ, (0 ≤ h ∧ IsMaxOn (P.processorObjO rc rp) (Set.Ici 0) h) ↔
      h = (P.pm + rp - rc) / 2) ∧
    P.qt ((P.pm + rp - rc) / 2 + rc) = P.VO (rc + rp) ∧
    ((P.pm + rp - rc) / 2 + rc) * P.qt ((P.pm + rp - rc) / 2 + rc) = P.PiOC (rc + rp) ∧
    P.processorObjO rc rp ((P.pm + rp - rc) / 2) = P.PiOP (rc + rp) := by
  have hk : 0 < P.k := P.k_pos
  have hM : 0 < P.M := P.M_pos
  have hc : 0 < P.M / P.k := div_pos hM hk
  have hk0 : P.k ≠ 0 := hk.ne'
  -- collector utility identity
  have cu : ∀ a x : ℝ, P.collectorUtility a (a / P.k) - P.collectorUtility a x
      = P.k / 2 * (x - a / P.k) ^ 2 := by
    intro a x
    unfold collectorUtility
    field_simp
    ring
  -- processor identity
  have po : ∀ x : ℝ, P.processorObjO rc rp ((P.pm + rp - rc) / 2) - P.processorObjO rc rp x
      = P.M / P.k * (x - (P.pm + rp - rc) / 2) ^ 2 := by
    intro x
    unfold processorObjO qt
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h q
    constructor
    · intro H
      have h1 := isMaxOn_iff.mp H ((h + rc) / P.k) (Set.mem_univ _)
      have h2 := cu (h + rc) q
      have h3 : P.k / 2 * (q - (h + rc) / P.k) ^ 2 ≤ 0 := by linarith
      have h4 : (q - (h + rc) / P.k) ^ 2 = 0 := by
        apply le_antisymm _ (sq_nonneg _)
        by_contra hne
        push_neg at hne
        have : 0 < P.k / 2 * (q - (h + rc) / P.k) ^ 2 := mul_pos (by linarith) hne
        linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
      linarith
    · rintro rfl
      refine isMaxOn_iff.mpr (fun x _ => ?_)
      have h2 := cu (h + rc) x
      have : 0 ≤ P.k / 2 * (x - (h + rc) / P.k) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith
  · intro h
    unfold qt
    ring
  · intro h
    constructor
    · rintro ⟨h0, H⟩
      have hmem : (P.pm + rp - rc) / 2 ∈ Set.Ici (0:ℝ) := by
        simp only [Set.mem_Ici]; linarith
      have h1 := isMaxOn_iff.mp H _ hmem
      have h2 := po h
      have h3 : P.M / P.k * (h - (P.pm + rp - rc) / 2) ^ 2 ≤ 0 := by linarith
      have h4 : (h - (P.pm + rp - rc) / 2) ^ 2 = 0 := by
        apply le_antisymm _ (sq_nonneg _)
        by_contra hne
        push_neg at hne
        have : 0 < P.M / P.k * (h - (P.pm + rp - rc) / 2) ^ 2 := mul_pos hc hne
        linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
      linarith
    · rintro rfl
      refine ⟨by linarith, isMaxOn_iff.mpr (fun x _ => ?_)⟩
      have h2 := po x
      have : 0 ≤ P.M / P.k * (x - (P.pm + rp - rc) / 2) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
      linarith
  · unfold qt VO
    field_simp
    ring
  · unfold qt PiOC
    field_simp
    ring
  · unfold processorObjO qt PiOP
    field_simp
    ring
