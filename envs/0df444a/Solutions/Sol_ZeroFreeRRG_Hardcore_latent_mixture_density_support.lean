-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.latent_mixture_density_support
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:40:33.857867+00:00
-- url     : https://prove2.me/submissions/ba490836-f75a-4342-a4cc-443d2a353108

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem solution {ι : Type} [Fintype ι] (A u v : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    let S := ∑ i, A i
    let L := ∑ i, A i*u i
    let R := ∑ i, A i*v i
    let T := ∑ i, A i*u i*v i
    0 ≤ T ∧ 0 ≤ L*R/S ∧ (L*R/S = 0 → T=0) := by
  classical
  dsimp only
  let S := ∑ i, A i
  let L := ∑ i, A i*u i
  let R := ∑ i, A i*v i
  let T := ∑ i, A i*u i*v i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hA i)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => mul_nonneg (hA i) (hu i))
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => mul_nonneg (hA i) (hv i))
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hA i) (hu i)) (hv i))
  have hSzero : S=0 → T=0 := by
    intro h
    have ha : ∀ i, A i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hA i)).mp h i (Finset.mem_univ i)
    dsimp [T]
    simp [ha]
  have hLzero : L=0 → T=0 := by
    intro h
    have ha : ∀ i, A i*u i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hA i) (hu i))).mp h i (Finset.mem_univ i)
    dsimp [T]
    simp [ha]
  have hRzero : R=0 → T=0 := by
    intro h
    have ha : ∀ i, A i*v i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hA i) (hv i))).mp h i (Finset.mem_univ i)
    dsimp [T]
    apply Finset.sum_eq_zero
    intro i hi
    calc
      A i*u i*v i = (A i*v i)*u i := by ring
      _ = 0 := by rw [ha i]; ring
  refine ⟨hT,div_nonneg (mul_nonneg hL hR) hS,?_⟩
  intro hzero
  by_cases hS0 : S=0
  · exact hSzero hS0
  · have hLR : L*R=0 := (div_eq_zero_iff).mp hzero |>.resolve_right hS0
    rcases mul_eq_zero.mp hLR with hL0 | hR0
    · exact hLzero hL0
    · exact hRzero hR0
