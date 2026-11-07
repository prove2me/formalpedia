-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_split_full_degree_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:30:55.635195+00:00
-- url     : https://prove2.me/submissions/0e40a04a-5327-4909-a143-fe71b2ffeece

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSpecialization
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_square_root_of_even_finrank
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_full_degree_parameter


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open scoped QuadraticAlgebra
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution (p n : ℕ) [Fact p.Prime]
    (hPositive : 0 < n) (epsilon : ZMod p)
    (hEpsilon : epsilon ≠ 0) (hNonSquare : ∀ r : ZMod p, r ^ 2 ≠ epsilon) :
    ∃ y r : GaloisField p (2 * n), y ≠ 0 ∧ 1 + y ≠ 0 ∧ r ≠ 0 ∧
      r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n := by
  obtain ⟨y, hY, hOne, hIrreducible, hDegree, _⟩ :=
    exists_full_degree_parameter p (2 * n) (by omega)
  obtain ⟨r, hRoot⟩ := exists_square_root_of_even_finrank
    (K := GaloisField p (2 * n)) epsilon hNonSquare (by
      rw [GaloisField.finrank p (by omega)]
      exact dvd_mul_right 2 n)
  refine ⟨y, r, hY, hOne, ?_, hRoot, hIrreducible, hDegree⟩
  intro hZero
  have hImage : algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon = 0 := by
    simpa only [hZero, zero_pow (by decide : 2 ≠ 0)] using hRoot.symm
  exact hEpsilon ((algebraMap (ZMod p) (GaloisField p (2 * n))).injective
    (by simpa only [map_zero] using hImage))
end QEC.Coding.ExpanderCodes
