-- Prove2me | solution 1 for ShiShallow.acceptProb_eq_of_agree_on_cone
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T06:02:45.473792+00:00
-- url     : https://prove2.me/submissions/d5d5a294-d76e-4c38-ad7a-00c0d58162e1

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
import Theorems.Thm_ShiShallow_IsLocal_diag_congr
import Theorems.Thm_ShiShallow_acceptProb_eq_conj_entry
import Theorems.Thm_ShiShallow_isLocal_conj_circuit
import Theorems.Thm_ShiShallow_isLocal_projOut
import Theorems.Thm_ShiShallow_padIn_castAdd
import Theorems.Thm_ShiShallow_padIn_natAdd

section
open ShiShallow

theorem solution {n m : ℕ} (c : Layered (n + m)) (out : Fin (n + m))
    (hc : ∀ l ∈ c, LayerOk l) (x x' : Bits n)
    (hagree : ∀ i : Fin n, Fin.castAdd m i ∈ coneOf c {out} → x i = x' i) :
    acceptProb c x out = acceptProb c x' out := by
  have hloc := isLocal_conj_circuit c hc (isLocal_projOut out)
  have hpad : ∀ k ∈ coneOf c {out}, padIn (m := m) x k = padIn (m := m) x' k := by
    intro k
    refine Fin.addCases (motive := fun k => k ∈ coneOf c {out} →
      padIn (m := m) x k = padIn (m := m) x' k) ?_ ?_ k
    · intro i hi; rw [padIn_castAdd, padIn_castAdd]; exact hagree i hi
    · intro j _; rw [padIn_natAdd, padIn_natAdd]
  have hcast : ((acceptProb c x out : ℝ) : ℂ) = ((acceptProb c x' out : ℝ) : ℂ) := by
    rw [acceptProb_eq_conj_entry c x out, acceptProb_eq_conj_entry c x' out]
    exact hloc.diag_congr hpad
  exact_mod_cast hcast

end
