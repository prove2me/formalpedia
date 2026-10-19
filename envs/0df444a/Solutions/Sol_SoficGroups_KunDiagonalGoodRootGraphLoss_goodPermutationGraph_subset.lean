-- Prove2me | solution 1 for SoficGroups.KunDiagonalGoodRootGraphLoss.goodPermutationGraph_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/fb84747c-b31f-4089-a06a-902f0dfc8158

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
namespace SoficGroups.KunDiagonalGoodRootGraphLoss
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    goodPermutationGraph p B ⊆ SoficGroups.permutationGraph p :=
  Finset.filter_subset _ _
end SoficGroups.KunDiagonalGoodRootGraphLoss
