-- Prove2me | solution 1 for SalesEffort.opt_rate_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:28:14.693273+00:00
-- url     : https://prove2.me/submissions/cb8013b4-a2c7-4869-896f-ee6b8b995cf5

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

open SalesEffort in
theorem solution (M : Model) {Δ Δ' ℓ ℓ' : ℝ} (hΔ : Δ ≤ Δ')
    (hℓ : IsOptRate M Δ ℓ) (hℓ' : IsOptRate M Δ' ℓ') : ℓ ≤ ℓ' := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨hmem, hmax⟩ := hℓ
  obtain ⟨hmem', hmax'⟩ := hℓ'
  have a1 := hmax ℓ' hmem'
  have a2 := hmax' ℓ hmem
  simp only at a1 a2
  have hpos : 0 < ℓ - ℓ' := by linarith
  have hsum : (ℓ - ℓ') * (Δ' - Δ) ≤ 0 := by nlinarith
  have hΔeq : Δ' = Δ := by
    by_contra hne
    have : 0 < Δ' - Δ := lt_of_le_of_ne (by linarith) (fun h => hne (by linarith))
    have := mul_pos hpos this
    linarith
  subst hΔeq
  obtain ⟨α, hα, hsc⟩ := M.c_strongConvex
  have hstrict := hsc.strictConvexOn hα
  have hc := hstrict.2 hmem hmem' (ne_of_gt hlt) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at hc
  have hm : (1/2 : ℝ) * ℓ + (1/2) * ℓ' ∈ Icc M.lo M.hi :=
    ⟨by linarith [hmem.1, hmem'.1], by linarith [hmem.2, hmem'.2]⟩
  have a3 := hmax _ hm
  simp only at a3
  nlinarith
