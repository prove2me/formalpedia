-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanentPermutationMonomial_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/60cf2d99-b493-4ebd-8548-ba24bd880844

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    MvPolynomial.pderiv (a, b)
        (∏ i : Fin n, (MvPolynomial.X (i, σ i) :
          MvPolynomial (Fin n × Fin n) ℂ)) =
      if σ a = b then
        ∏ i : {i : Fin n // i ≠ a},
          (MvPolynomial.X (i.1, σ i.1) :
            MvPolynomial (Fin n × Fin n) ℂ)
      else 0 := by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun i : Fin n =>
      (MvPolynomial.X (i, σ i) : MvPolynomial (Fin n × Fin n) ℂ)) a,
    MvPolynomial.pderiv_mul]
  have hrest :
      MvPolynomial.pderiv (a, b)
        (∏ i : {i : Fin n // i ≠ a},
          (MvPolynomial.X (i.1, σ i.1) :
            MvPolynomial (Fin n × Fin n) ℂ)) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hmem
    have hsubset := MvPolynomial.vars_prod (s := Finset.univ)
      (fun i : {i : Fin n // i ≠ a} =>
        (MvPolynomial.X (i.1, σ i.1) :
          MvPolynomial (Fin n × Fin n) ℂ))
    have hbi := hsubset hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hbi
    have hpair : (a, b) = (i.1, σ i.1) := by
      simpa [MvPolynomial.vars_X] using hi
    exact i.property (congrArg Prod.fst hpair).symm
  by_cases hab : σ a = b
  · subst b
    simp [hrest]
  · have hpair : (a, σ a) ≠ (a, b) := by
      intro h
      exact hab (congrArg Prod.snd h)
    simp [hab, hrest, MvPolynomial.pderiv_X_of_ne hpair]
end PermanentFormulaLowerBound
