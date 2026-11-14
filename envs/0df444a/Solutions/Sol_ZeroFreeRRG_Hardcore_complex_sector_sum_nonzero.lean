-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.complex_sector_sum_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:44:36.929804+00:00
-- url     : https://prove2.me/submissions/c8ce6828-5c01-4946-899f-3b3e2f71779c

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem solution {ι : Type} (S : Finset ι) (z : ι → ℂ) (u : ℂ) (c : ℝ)
    (hu : ‖u‖ = 1) (hc : 0 < c)
    (hsector : ∀ i ∈ S, c * ‖z i‖ ≤ (star u * z i).re)
    (hne : ∃ i ∈ S, z i ≠ 0) :
    c * (∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖ ∧ (∑ i ∈ S, z i) ≠ 0 := by
  classical
  have hsum : c * (∑ i ∈ S, ‖z i‖) ≤ (star u * ∑ i ∈ S, z i).re := by
    rw [Finset.mul_sum,Finset.mul_sum]
    rw [Complex.re_sum]
    exact Finset.sum_le_sum hsector
  have hre : (star u * ∑ i ∈ S, z i).re ≤ ‖∑ i ∈ S, z i‖ := by
    calc
      _ ≤ ‖star u * ∑ i ∈ S, z i‖ := Complex.re_le_norm _
      _ = _ := by simp [norm_mul,hu]
  have hbound := hsum.trans hre
  obtain ⟨j,hj,hj0⟩ := hne
  have hpos : 0 < ∑ i ∈ S, ‖z i‖ := by
    apply Finset.sum_pos'
    · intro i hi
      exact norm_nonneg _
    · exact ⟨j,hj,norm_pos_iff.mpr hj0⟩
  refine ⟨hbound,?_⟩
  intro hz
  have : 0 < ‖∑ i ∈ S, z i‖ := (mul_pos hc hpos).trans_le hbound
  simpa [hz] using this
