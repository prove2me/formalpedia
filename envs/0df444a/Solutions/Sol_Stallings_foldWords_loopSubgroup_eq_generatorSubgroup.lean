-- Prove2me | solution 1 for Stallings.foldWords_loopSubgroup_eq_generatorSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:16:17.087402+00:00
-- url     : https://prove2.me/submissions/b778b9f5-8daa-4e73-b1ba-0e17e3cc23f9

import Definitions.Def_Stallings_Folding
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Definitions.Def_Stallings_Flower
import Theorems.Thm_Stallings_flower_hasCosetPotential
import Theorems.Thm_Stallings_flowerGraph_loopSubgroup_eq_generatorSubgroup
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
import Theorems.Thm_Stallings_foldAutomaton_loopSubgroup_eq
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution (S : List Word) :
    (foldWords S).loopSubgroup = generatorSubgroup S := by
  calc
    (foldWords S).loopSubgroup = (flowerGraph S).loopSubgroup none := by
      have hpotential : HasCosetPotential (flowerGraph S)
          ((flowerGraph S).loopSubgroup none) (flowerPotential S) := by
        intro v x w hedge
        have h := flower_hasCosetPotential S hedge
        rw [← flowerGraph_loopSubgroup_eq_generatorSubgroup S] at h
        exact h
      simpa [foldWords] using foldAutomaton_loopSubgroup_eq (flowerGraph S) none
        (flowerPotential S) hpotential (by rfl)
    _ = generatorSubgroup S := flowerGraph_loopSubgroup_eq_generatorSubgroup S
end Stallings
