-- Prove2me | solution 1 for PermanentFormulaLowerBound.algebraicIndependent_of_jacobianMinor_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/d0908615-16bc-4e03-9886-e022956410cc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero
import Theorems.Thm_PermanentFormulaLowerBound_totalDegree_pderiv_lt_of_ne_zero
import Theorems.Thm_PermanentFormulaLowerBound_eq_C_of_forall_pderiv_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}
namespace PermanentFormulaLowerBound
theorem _root_.solution
    [Field F] [CharZero F] [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ)
    (hdet : (jacobianMinor g cols).det ≠ 0) :
    AlgebraicIndependent F g := by
  rw [algebraicIndependent_iff]
  intro H hH
  have hmain : ∀ n : ℕ, ∀ p : MvPolynomial ι F,
      p.totalDegree = n → MvPolynomial.aeval g p = 0 → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hdegree hrelation
      have hpartials : ∀ i : ι, MvPolynomial.pderiv i p = 0 := by
        intro i
        by_cases hi : MvPolynomial.pderiv i p = 0
        · exact hi
        · have hlt : (MvPolynomial.pderiv i p).totalDegree < n := by
            rw [← hdegree]
            exact totalDegree_pderiv_lt_of_ne_zero p i hi
          exact ih _ hlt (MvPolynomial.pderiv i p) rfl
            (aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero
              g cols p hdet hrelation i)
      have hconstant := eq_C_of_forall_pderiv_eq_zero p hpartials
      rw [hconstant] at hrelation ⊢
      simpa using hrelation
  exact hmain H.totalDegree H rfl hH
end PermanentFormulaLowerBound
