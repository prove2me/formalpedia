-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.sum_blockLeaves_le_variableLeaves_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/17810d3f-1f72-4509-8c25-89a8942c158c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ]
    (blocks : κ → Finset ι)
    (hdisjoint : ∀ a b : κ, a ≠ b → Disjoint (blocks a) (blocks b))
    (f : RationalFormula ι R) :
    (∑ a : κ, blockLeaves (blocks a) f) ≤ variableLeaves f := by
  classical
  induction f with
  | var i =>
      change (∑ a : κ, if i ∈ blocks a then 1 else 0) ≤ 1
      rw [Finset.sum_boole]
      apply Finset.card_le_one.mpr
      intro a ha b hb
      by_contra hne
      have hia : i ∈ blocks a := (Finset.mem_filter.mp ha).2
      have hib : i ∈ blocks b := (Finset.mem_filter.mp hb).2
      exact Finset.disjoint_left.mp (hdisjoint a b hne) hia hib
  | const _ =>
      simp [blockLeaves, variableLeaves]
  | add f g hf hg =>
      simpa [blockLeaves, variableLeaves, Finset.sum_add_distrib]
        using Nat.add_le_add hf hg
  | sub f g hf hg =>
      simpa [blockLeaves, variableLeaves, Finset.sum_add_distrib]
        using Nat.add_le_add hf hg
  | mul f g hf hg =>
      simpa [blockLeaves, variableLeaves, Finset.sum_add_distrib]
        using Nat.add_le_add hf hg
  | div f g hf hg =>
      simpa [blockLeaves, variableLeaves, Finset.sum_add_distrib]
        using Nat.add_le_add hf hg
end PermanentFormulaLowerBound.RationalFormula
