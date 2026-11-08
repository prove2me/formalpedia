-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerator401_conj_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:00:43.98387+00:00
-- url     : https://prove2.me/submissions/2b791f9b-188d-42c1-a349-70d33cb09cdb

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsMatrix401_mul_conj
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGL401_det

set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
namespace QEC.Coding.BalancedProduct.LPSGenerators
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    lpsGenerator401 q hq t.conj
        ((ShellIndex401.conj_mem_shell401_iff t).mpr ht) =
      (lpsGenerator401 q hq t ht)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  change Matrix.ProjGenLinGroup.mk (lpsGL401 q hq t ht) *
      Matrix.ProjGenLinGroup.mk
        (lpsGL401 q hq t.conj
          ((ShellIndex401.conj_mem_shell401_iff t).mpr ht)) = 1
  rw [← map_mul]
  apply (Matrix.ProjGenLinGroup.mk_eq_one).mpr
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨(lpsGL401 q hq t ht).det, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (Matrix.scalar (Fin 2) ((lpsGL401 q hq t ht).det : ZMod q)) i j =
    (lpsMatrix401 q t * lpsMatrix401 q t.conj) i j
  rw [lpsMatrix401_mul_conj q t ht, lpsGL401_det q hq t ht]
  simp [Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply]
end QEC.Coding.BalancedProduct.LPSGenerators
