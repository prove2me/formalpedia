-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.remark_2_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:45:08.771483+00:00
-- url     : https://prove2.me/submissions/5bf9a031-59b8-4a85-b1a4-63a31d75f0a4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26

attribute [local instance] Classical.propDecidable

theorem solution (n : ℕ) :
    yjm (Fin.last (n + 2)) ∉ Subalgebra.center ℂ (SymmetricAlgebra (n + 3)) := by
  intro hc
  rw [Subalgebra.mem_center_iff] at hc
  set L : Fin (n + 3) := Fin.last (n + 2) with hL
  set m : Fin (n + 3) := ⟨n + 1, by omega⟩ with hm
  set z : Fin (n + 3) := ⟨0, by omega⟩ with hz
  have hmL : m ≠ L := by simp [hm, hL, Fin.ext_iff]
  have hzL : z ≠ L := by simp [hz, hL, Fin.ext_iff]
  have hzm : z ≠ m := by simp [hz, hm, Fin.ext_iff]
  set s := Equiv.swap m L with hs
  have key := hc (MonoidAlgebra.single s 1)
  have e := congrArg (fun f : SymmetricAlgebra (n + 3) => f.coeff (Equiv.swap z L * s)) key
  have hzlt : z < L := by simp [hz, hL, Fin.lt_def]
  simp only [yjm, swapAlgebraElement, Finset.mul_sum, Finset.sum_mul,
    MonoidAlgebra.single_mul_single, one_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply] at e
  have hzlt : z < L := by simp [hz, hL, Fin.lt_def]
  have hl : (∑ k ∈ Finset.univ.filter (fun k : Fin (n + 3) => k < L),
      if s * Equiv.swap k L = Equiv.swap z L * s then (1 : ℂ) else 0) = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [if_neg]
    intro h
    have := congrArg (fun p : Equiv.Perm (Fin (n + 3)) => p z) h
    simp only [Equiv.Perm.mul_apply] at this
    have hs0 : s z = z := Equiv.swap_apply_of_ne_of_ne hzm hzL
    rw [hs0, Equiv.swap_apply_left] at this
    by_cases hk0 : k = z
    · subst hk0
      rw [Equiv.swap_apply_left, hs, Equiv.swap_apply_right] at this
      exact hmL this
    · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hk0) hzL, hs0] at this
      exact hzL this
  have hr : (∑ k ∈ Finset.univ.filter (fun k : Fin (n + 3) => k < L),
      if Equiv.swap k L * s = Equiv.swap z L * s then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_eq_single z]
    · simp
    · intro k hk hkz
      rw [if_neg]
      intro h
      have h' := mul_right_cancel h
      have := congrArg (fun p : Equiv.Perm (Fin (n + 3)) => p z) h'
      simp only [Equiv.swap_apply_left] at this
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hkz) hzL] at this
      exact hzL this
    · intro h; exact absurd (by simp [hzlt]) h
  rw [hl, hr] at e
  exact zero_ne_one e
