-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutationOutsideProduct_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/52199e0c-f0f0-48e2-92cd-39813a17b316

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
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (z : matchingOutside d) :
    MvPolynomial.pderiv z (matchingPermutationOutsideProduct d σ) =
      if σ z.1.1 = z.1.2 then
        ∏ i : {i : Fin n // i ≠ z.1.1},
          matchingPermutationOutsideFactor d σ i.1
      else 0 := by
  classical
  change MvPolynomial.pderiv z
    (∏ i : Fin n, matchingPermutationOutsideFactor d σ i) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (matchingPermutationOutsideFactor d σ) z.1.1,
    MvPolynomial.pderiv_mul]
  have hrest :
      MvPolynomial.pderiv z
        (∏ i : {i : Fin n // i ≠ z.1.1},
          matchingPermutationOutsideFactor d σ i.1) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hmem
    have hsubset := MvPolynomial.vars_prod (s := Finset.univ)
      (fun i : {i : Fin n // i ≠ z.1.1} =>
        matchingPermutationOutsideFactor d σ i.1)
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hsubset hmem)
    unfold matchingPermutationOutsideFactor at hi
    split at hi
    · simp at hi
    · rename_i w hw
      have hzw : z = w := by
        simpa [MvPolynomial.vars_X] using hi
      have hpair : (i.1, σ i.1) = z.1 := by
        have heq := congrArg (matchingVariableEquiv d) hw
        simpa [hzw] using heq
      exact i.property (congrArg Prod.fst hpair)
  by_cases hz : σ z.1.1 = z.1.2
  · have hmarked :
        (matchingVariableEquiv d).symm (z.1.1, σ z.1.1) =
          .inr z := by
        apply (matchingVariableEquiv d).injective
        simp [hz]
    have hfactor :
        matchingPermutationOutsideFactor d σ z.1.1 =
          MvPolynomial.X z := by
      unfold matchingPermutationOutsideFactor
      rw [hmarked]
    rw [hrest, hfactor]
    simp [hz]
  · have hfirst :
        MvPolynomial.pderiv z
          (matchingPermutationOutsideFactor d σ z.1.1) = 0 := by
        unfold matchingPermutationOutsideFactor
        split
        · simp
        · rename_i w hw
          apply MvPolynomial.pderiv_X_of_ne
          intro hzw
          have hpair : (z.1.1, σ z.1.1) = z.1 := by
            have heq := congrArg (matchingVariableEquiv d) hw
            simpa [hzw] using heq
          exact hz (congrArg Prod.snd hpair)
    rw [hrest, hfirst]
    simp [hz]
end PermanentFormulaLowerBound
