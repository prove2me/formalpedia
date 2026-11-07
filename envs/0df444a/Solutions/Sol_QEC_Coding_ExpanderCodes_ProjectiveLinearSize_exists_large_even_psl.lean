-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.ProjectiveLinearSize.exists_large_even_psl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:25.924756+00:00
-- url     : https://prove2.me/submissions/563380e5-6fa5-4f12-badf-1bb777838f41

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveLinearSize_field_card_le_psl_card
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_split_full_degree_parameter


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveLinearSize
open Matrix
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.ProjectiveLinearSize
theorem _root_.solution (p N : ℕ) [hPrime : Fact p.Prime]
    (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
    (hNonSquare : ∀ r : ZMod p, r ^ 2 ≠ epsilon) :
    ∃ n : ℕ, 1 < n ∧
      N ≤ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p (2 * n))) ∧
      ∃ y r : GaloisField p (2 * n), y ≠ 0 ∧ 1 + y ≠ 0 ∧ r ≠ 0 ∧
        r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon ∧
        Irreducible (minpoly (ZMod p) y) ∧
        (minpoly (ZMod p) y).natDegree = 2 * n := by
  refine ⟨N + 2, by omega, ?_,
    exists_split_full_degree_parameter p (N + 2) (by omega)
      epsilon hEpsilon hNonSquare⟩
  apply le_trans _ (field_card_le_psl_card (K := GaloisField p (2 * (N + 2))))
  rw [GaloisField.card p (2 * (N + 2)) (by omega)]
  have hPow := Nat.lt_pow_self hPrime.out.one_lt (n := 2 * (N + 2))
  omega
end QEC.Coding.ExpanderCodes.ProjectiveLinearSize
