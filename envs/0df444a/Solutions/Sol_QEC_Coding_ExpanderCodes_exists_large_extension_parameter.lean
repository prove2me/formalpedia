-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_large_extension_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:10.38898+00:00
-- url     : https://prove2.me/submissions/78dfc3ea-f64e-407b-bfd8-fd13dafe4301

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSpecialization
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_full_degree_parameter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution (p N : ℕ) [hPrime : Fact p.Prime] :
    ∃ n : ℕ, 2 < n ∧ N ≤ Nat.card (GaloisField p n) ∧
      ∃ y : GaloisField p n, y ≠ 0 ∧ 1 + y ≠ 0 ∧
        Irreducible (minpoly (ZMod p) y) ∧
        (minpoly (ZMod p) y).natDegree = n ∧
        adjoin (ZMod p) ({y} : Set (GaloisField p n)) = ⊤ := by
  refine ⟨N + 3, by omega, ?_, exists_full_degree_parameter p (N + 3) (by omega)⟩
  rw [GaloisField.card p (N + 3) (by omega)]
  have hPow : N + 3 < p ^ (N + 3) := Nat.lt_pow_self hPrime.out.one_lt
  omega
end QEC.Coding.ExpanderCodes
