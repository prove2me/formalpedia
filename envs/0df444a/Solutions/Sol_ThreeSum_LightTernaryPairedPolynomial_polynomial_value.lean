-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPolynomial.polynomial_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:55.389888+00:00
-- url     : https://prove2.me/submissions/401589a4-5f79-4075-9053-aab678f57d95

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_polynomial_eval
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_atoms_encode
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_val


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPolynomial
theorem _root_.solution (m : ℕ) (T : Quad m → ℤ) (σ : State)
    (hT : ∀ q, (atomExpr m q).val σ=T q) :
    ((polynomial m).compile (atoms m)).val σ=value T := by
  rw [Circuit.compile_val,polynomial_eval]
  apply Finset.sum_congr rfl
  intro perm hperm
  apply Finset.sum_congr rfl
  intro τ hτ
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [atoms_encode,hT]
end ThreeSum.LightTernaryPairedPolynomial
