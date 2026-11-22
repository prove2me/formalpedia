-- Prove2me | solution 1 for ShiShallow.isLocal_projOut
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:01:53.657969+00:00
-- url     : https://prove2.me/submissions/5c881438-223b-4304-9cc4-59b33f253de9

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

section
open ShiShallow

theorem solution {n : ℕ} (out : Fin n) : IsLocal {out} (projOut out) := by
  have hout : out ∈ ({out} : Finset (Fin n)) := Finset.mem_singleton_self out
  constructor
  · intro y z hne
    have hyz : y ≠ z := fun h => hne (fun k _ => by rw [h])
    simp only [projOut, Matrix.of_apply]
    exact if_neg (fun hc => hyz hc.1)
  · intro y z y' z' hy hz hyz hyz'
    have key : (y = z) ↔ (y' = z') := by
      constructor
      · intro h
        funext k
        by_cases hk : k = out
        · rw [hk, ← hy out hout, ← hz out hout, h]
        · exact hyz' k (by simpa using hk)
      · intro h
        funext k
        by_cases hk : k = out
        · rw [hk, hy out hout, hz out hout, h]
        · exact hyz k (by simpa using hk)
    simp only [projOut, Matrix.of_apply, key, hy out hout]

end
