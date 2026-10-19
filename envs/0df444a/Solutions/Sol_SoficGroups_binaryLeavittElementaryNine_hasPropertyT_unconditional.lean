-- Prove2me | solution 1 for SoficGroups.binaryLeavittElementaryNine_hasPropertyT_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/91753129-7e23-4326-8d70-fd6bb0faa523

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_hasPropertyT_of_mulEquiv
import Theorems.Thm_SoficGroups_hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
import Theorems.Thm_SoficGroups_finiteOuterBlockCyclicRootFamily_iSup_eq_top

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators
namespace SoficGroups
theorem _root_.solution :
    HasPropertyT.{0, vSharp} (binaryLeavittElementaryGroup 9) := by
  classical
  obtain ⟨s, hs⟩ :=
    Algebra.FiniteType.out (R := ZMod 2) (A := BinaryLeavitt)
  letI : HasPropertyT.{0, vSharp}
      (elementaryGroup (Fin 3)
        (Matrix (Fin 3) (Fin 3) BinaryLeavitt)) :=
    hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
      (finiteBlockCoefficientSpan s)
      (finiteOuterBlockCyclicRootFamily_iSup_eq_top s hs)
  exact hasPropertyT_of_mulEquiv
    ((LeavittElementaryMorita.elementaryBlockGroupEquiv
      (ι := Fin 3) (κ := Fin 3) (R := BinaryLeavitt)).trans
      (LeavittElementaryMorita.elementaryReindexGroupEquiv
        (R := BinaryLeavitt)
        (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)))
end SoficGroups
