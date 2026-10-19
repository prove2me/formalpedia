-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.yLeafCount_rename_matchingVariableEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/195707a9-b276-43b3-b14e-51388819cad8

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {ι : Type u} {κ : Type v} {R : Type w}
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {n : ℕ} {Y : Type u} [Fintype Y]
    (d : Y ↪ Fin n × Fin n) (f : Formula (Fin n × Fin n) R) :
    yLeafCount (rename (matchingVariableEquiv d).symm f) =
      blockLeaves (matchingMarkedFinset d) f := by
  classical
  induction f with
  | var i =>
      cases h : (matchingVariableEquiv d).symm i with
      | inl y =>
          have hi : d y = i := by
            have he := (matchingVariableEquiv d).apply_symm_apply i
            simpa [h] using he
          have hmem : i ∈ matchingMarkedFinset d :=
            (mem_matchingMarkedFinset d i).mpr ⟨y, hi⟩
          simp [rename, yLeafCount, blockLeaves, h, hmem]
      | inr z =>
          have hi : i ∉ matchingMarkedFinset d := by
            intro hmem
            obtain ⟨y, hy⟩ := (mem_matchingMarkedFinset d i).mp hmem
            have he : (matchingVariableEquiv d).symm i = .inl y := by
              apply (matchingVariableEquiv d).injective
              simpa only [Equiv.apply_symm_apply, matchingVariableEquiv_inl]
                using hy.symm
            rw [h] at he
            cases he
          simp [rename, yLeafCount, blockLeaves, h, hi]
  | const c => simp [rename, yLeafCount, blockLeaves]
  | add f g hf hg => simp [rename, yLeafCount, blockLeaves, hf, hg]
  | sub f g hf hg => simp [rename, yLeafCount, blockLeaves, hf, hg]
  | mul f g hf hg => simp [rename, yLeafCount, blockLeaves, hf, hg]
end PermanentFormulaLowerBound.Formula
