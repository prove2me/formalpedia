-- Prove2me | solution 1 for ShiShallow.isLocal_conj_layer
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:55:45.086985+00:00
-- url     : https://prove2.me/submissions/4969365f-81a2-4615-b1de-349db6a2cb79

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
import Definitions.Def_ShiShallow_Cone
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_IsLocal_conjTranspose
import Theorems.Thm_ShiShallow_conj_eq_of_disjoint
import Theorems.Thm_ShiShallow_conj_mul_eq
import Theorems.Thm_ShiShallow_disjoint_coneStep
import Theorems.Thm_ShiShallow_gateMatrix_unitary
import Theorems.Thm_ShiShallow_isLocal_conj
import Theorems.Thm_ShiShallow_isLocal_gateMatrix

section
open ShiShallow

theorem solution {n : ℕ} (l : List (Instr n)) (hl : LayerOk l)
    {S : Finset (Fin n)} {A : Op n} (hA : IsLocal S A) :
    IsLocal (coneStep l S) ((layerMatrix l).conjTranspose * A * layerMatrix l) := by
  induction l with
  | nil =>
    rw [layerMatrix_nil, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, coneStep_nil]
    exact hA
  | cons g t ih =>
    rw [LayerOk, List.pairwise_cons] at hl
    obtain ⟨hgt, hlt⟩ := hl
    have hinner := ih hlt
    rw [layerMatrix_cons, conj_mul_eq, coneStep_cons]
    by_cases hmeet : (g.support ∩ S).Nonempty
    · rw [if_pos hmeet]
      exact isLocal_conj hinner (isLocal_gateMatrix g)
    · rw [if_neg hmeet]
      have hdS : Disjoint g.support S := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact Finset.not_nonempty_iff_eq_empty.1 hmeet
      have hd : Disjoint g.support (coneStep t S) := disjoint_coneStep t S hdS hgt
      rw [conj_eq_of_disjoint hinner (isLocal_gateMatrix g) hd (gateMatrix_unitary g)]
      exact hinner

end
