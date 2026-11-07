-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_even_psl_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:31.389946+00:00
-- url     : https://prove2.me/submissions/01389f4a-2ab5-48cc-be60-c85ec7cde0ce

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_square_ratio_generator
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_constant_square_root_of_even_finrank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution (p n : ℕ) [hPrime : Fact p.Prime]
    (hDegree : 1 < n) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0) :
    ∃ y r s i : GaloisField p (2 * n),
      y ≠ 0 ∧ 1 + y ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
      r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon ∧
      s ^ 2 = y / (1 + y) ∧ i ^ 2 = -1 ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n := by
  have hCard : 3 < Nat.card (GaloisField p (2 * n)) := by
    rw [GaloisField.card p (2 * n) (by omega)]
    have := Nat.lt_pow_self hPrime.out.one_lt (n := 2 * n)
    omega
  obtain ⟨y, s, hY, hOne, hS, hRatio, hGenerate⟩ :=
    exists_square_ratio_generator (F := ZMod p) hCard
  have hEven : 2 ∣ Module.finrank (ZMod p) (GaloisField p (2 * n)) := by
    rw [GaloisField.finrank p (by omega)]
    exact dvd_mul_right 2 n
  obtain ⟨r, hRoot⟩ := exists_constant_square_root_of_even_finrank epsilon hEven
  obtain ⟨i, hI⟩ := exists_constant_square_root_of_even_finrank (-1 : ZMod p) hEven
  have hR : r ≠ 0 := by
    intro hZero
    have hImage : algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon = 0 := by
      simpa [hZero] using hRoot.symm
    exact hEpsilon ((algebraMap (ZMod p) (GaloisField p (2 * n))).injective
      (by simpa only [map_zero] using hImage))
  have hMinDegree := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) y).mp
    hGenerate
  refine ⟨y, r, s, i, hY, hOne, hR, hS, hRoot, hRatio, ?_,
    minpoly.irreducible (IsIntegral.of_finite (ZMod p) y), ?_⟩
  · simpa only [map_neg, map_one] using hI
  · rw [GaloisField.finrank p (n := 2 * n) (by omega)] at hMinDegree
    exact hMinDegree
end QEC.Coding.ExpanderCodes
