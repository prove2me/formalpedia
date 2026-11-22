-- Prove2me | solution 1 for ShiShallow.acceptProb_eq_conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:57:16.974031+00:00
-- url     : https://prove2.me/submissions/95ef89e0-4eb6-45ad-bf98-01fdd5ac2740

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
import Theorems.Thm_ShiShallow_IsLocal_conjTranspose
import Theorems.Thm_ShiShallow_mulVec_inputState
import Theorems.Thm_ShiShallow_ofReal_norm_sq
import Theorems.Thm_ShiShallow_runLayered_eq_mulVec

section
open ShiShallow

theorem solution {n m : ℕ} (c : Layered (n + m)) (x : Bits n)
    (out : Fin (n + m)) :
    ((acceptProb c x out : ℝ) : ℂ)
      = ((circMatrix c).conjTranspose * projOut out * circMatrix c) (padIn x) (padIn x) := by
  classical
  set U := circMatrix c with hUdef
  have inner : ∀ a v : Bits (n + m), (U.conjTranspose * projOut out) a v
      = star (U v a) * (if v out = true then 1 else 0) := by
    intro a v
    rw [Matrix.mul_apply, Finset.sum_eq_single v]
    · by_cases h : v out = true <;>
        simp [Matrix.conjTranspose_apply, projOut, Matrix.of_apply, h]
    · intro u _ hu
      have hzero : projOut out u v = 0 := by
        simp only [projOut, Matrix.of_apply]
        exact if_neg (fun hc => hu hc.1)
      rw [hzero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hrhs : (U.conjTranspose * projOut out * U) (padIn x) (padIn x)
      = ∑ v : Bits (n + m),
          if v out = true then star (U v (padIn x)) * U v (padIn x) else 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [inner]
    by_cases h : v out = true
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero, zero_mul]
  have hstate : ∀ y : Bits (n + m), runLayered c (inputState x) y = U y (padIn x) := by
    intro y; rw [runLayered_eq_mulVec, mulVec_inputState]
  rw [hrhs]
  unfold acceptProb
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y out = true
  · rw [if_pos hy, if_pos hy, hstate y, ofReal_norm_sq]
  · rw [if_neg hy, if_neg hy, Complex.ofReal_zero]

end
