-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.blockLeaves_pos_of_eval_eq_permanent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/3bc80896-19e9-4326-ad8c-d4b1539c339f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_yLeafCount_rename_matchingVariableEquiv
import Theorems.Thm_PermanentFormulaLowerBound_Formula_eval_rename_eq_matchingMarkedPermanent
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_yLeafCount_rename_matchingVariableEquiv
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_eval_rename_eq_matchingMarkedPermanent
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_yLeafCount_pos_of_eval_eq_matchingMarkedPermanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
variable {ι : Type u} {κ : Type v} {R : Type w}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution
    {n : ℕ} (f : RationalFormula (Fin n × Fin n) ℂ)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n))
    (s : Finset (Fin n × Fin n)) (a b : Fin n)
    (hab : (a, b) ∈ s) :
    0 < blockLeaves s f := by
  classical
  let d : (↥s) ↪ Fin n × Fin n :=
    ⟨Subtype.val, Subtype.val_injective⟩
  letI : Nonempty (↥s) := ⟨⟨(a, b), hab⟩⟩
  have hset : matchingMarkedFinset d = s := by
    ext i
    simp [matchingMarkedFinset, d]
  have hrename := eval_rename_eq_matchingMarkedPermanent d f hf
  have hpos := yLeafCount_pos_of_eval_eq_matchingMarkedPermanent
    d (rename (matchingVariableEquiv d).symm f) hrename
  rw [yLeafCount_rename_matchingVariableEquiv, hset] at hpos
  exact hpos
end PermanentFormulaLowerBound.RationalFormula
