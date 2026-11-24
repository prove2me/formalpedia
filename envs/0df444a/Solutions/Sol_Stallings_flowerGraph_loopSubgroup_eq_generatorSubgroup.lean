-- Prove2me | solution 1 for Stallings.flowerGraph_loopSubgroup_eq_generatorSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:14:53.864385+00:00
-- url     : https://prove2.me/submissions/7491ee4c-3d12-46bd-bf3a-498c2616e59c

import Definitions.Def_Stallings_Folding
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Definitions.Def_Stallings_Flower
import Theorems.Thm_Stallings_flower_hasCosetPotential
import Theorems.Thm_Stallings_flowerWalk
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
import Theorems.Thm_Stallings_InverseMultigraph_walk_cosetPotential
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution (S : List Word) :
    (flowerGraph S).loopSubgroup none = generatorSubgroup S := by
  apply le_antisymm
  · change Subgroup.closure
      {g : Free | ∃ w : Word, wordEval w = g ∧ (flowerGraph S).Walk none w none} ≤
      generatorSubgroup S
    apply (Subgroup.closure_le (generatorSubgroup S)).2
    intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    rw [← hw]
    have hpotential := InverseMultigraph.walk_cosetPotential (flowerGraph S)
      (generatorSubgroup S) (flowerPotential S) (flower_hasCosetPotential S) hwalk
    have hcoset : CosetEquivalent (generatorSubgroup S) 1 (wordEval w) := by
      simpa [flowerPotential] using hpotential
    have hinv : (wordEval w)⁻¹ ∈ generatorSubgroup S := by
      simpa [CosetEquivalent] using hcoset
    simpa using (generatorSubgroup S).inv_mem hinv
  · apply (Subgroup.closure_le ((flowerGraph S).loopSubgroup none)).2
    intro g hg
    rcases hg with ⟨i, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨S.get i, rfl, flowerWalk S i⟩
end Stallings
