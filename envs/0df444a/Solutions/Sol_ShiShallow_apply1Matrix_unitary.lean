-- Prove2me | solution 1 for ShiShallow.apply1Matrix_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:22:01.794997+00:00
-- url     : https://prove2.me/submissions/d8027a10-d2bf-4715-a858-c8a27b0feab5

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_isLocal_apply1Matrix
import Theorems.Thm_ShiShallow_sum_of_vanishing_single

section
open ShiShallow

theorem solution {n : ℕ} {U : Matrix Bool Bool ℂ} (hU : U.conjTranspose * U = 1) (i : Fin n) :
    (apply1Matrix U i).conjTranspose * apply1Matrix U i = 1 := by
  classical
  ext y z
  have hentry : ((apply1Matrix U i).conjTranspose * apply1Matrix U i) y z
      = ∑ w : Bits n, (starRingEnd ℂ) (apply1Matrix U i w y) * apply1Matrix U i w z := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hentry]
  by_cases hoff : ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k
  · have hvan : ∀ w : Bits n, (¬ ∀ k, k ∉ ({i} : Finset (Fin n)) → w k = y k) →
        (starRingEnd ℂ) (apply1Matrix U i w y) * apply1Matrix U i w z = 0 := by
      intro w hw
      rw [(isLocal_apply1Matrix U i).vanish hw]
      simp
    rw [sum_of_vanishing_single i y _ hvan]
    have hval : ∀ b : Bool,
        (starRingEnd ℂ) (apply1Matrix U i (Function.update y i b) y)
            * apply1Matrix U i (Function.update y i b) z
          = (starRingEnd ℂ) (U b (y i)) * U b (z i) := by
      intro b
      have c1 : ∀ k, k ∉ ({i} : Finset (Fin n)) → Function.update y i b k = y k :=
        fun k hk => Function.update_of_ne (by simpa using hk) _ _
      have c2 : ∀ k, k ∉ ({i} : Finset (Fin n)) → Function.update y i b k = z k :=
        fun k hk => (c1 k hk).trans (hoff k hk)
      simp only [apply1Matrix, Matrix.of_apply, if_pos c1, if_pos c2, Function.update_self]
    simp only [hval]
    have hUsum : ∑ b : Bool, (starRingEnd ℂ) (U b (y i)) * U b (z i) = (U.conjTranspose * U) (y i) (z i) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hUsum, hU, Matrix.one_apply, Matrix.one_apply]
    by_cases hyz : y = z
    · subst hyz; simp
    · have hne : y i ≠ z i := by
        intro h
        refine hyz (funext fun k => ?_)
        by_cases hk : k = i
        · subst hk; exact h
        · exact hoff k (by simpa using hk)
      simp [hyz, hne]
  · have hz : ∀ w : Bits n,
        (starRingEnd ℂ) (apply1Matrix U i w y) * apply1Matrix U i w z = 0 := by
      intro w
      by_cases hw : ∀ k, k ∉ ({i} : Finset (Fin n)) → w k = y k
      · have hvz : apply1Matrix U i w z = 0 :=
          (isLocal_apply1Matrix U i).vanish
            (fun hc => hoff (fun k hk => (hw k hk).symm.trans (hc k hk)))
        rw [hvz, mul_zero]
      · rw [(isLocal_apply1Matrix U i).vanish hw]; simp
    have hyz : y ≠ z := fun h => hoff (fun k _ => by rw [h])
    simp [hz, Matrix.one_apply, hyz]

end
