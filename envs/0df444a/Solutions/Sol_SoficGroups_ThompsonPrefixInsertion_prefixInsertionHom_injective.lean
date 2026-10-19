-- Prove2me | solution 1 for SoficGroups.ThompsonPrefixInsertion.prefixInsertionHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/e1702757-013d-41e1-8651-eed29ac6d20f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ThompsonPrefixInsertion
open scoped BigOperators
namespace SoficGroups.ThompsonPrefixInsertion
theorem _root_.solution (a : List (Fin 2)) :
    Function.Injective (prefixInsertionHom a) :=
  (prefixCornerUnitHom_injective (singletonPrefixCode a)).comp
    (Units.mapEquiv
      (Matrix.uniqueRingEquiv (m := Fin 1)
        (A := BinaryLeavitt)).symm.toMulEquiv).injective
end SoficGroups.ThompsonPrefixInsertion
