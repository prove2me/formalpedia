-- Prove2me | solution 1 for SoficGroups.finiteOuterElementaryRootConjugates_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/6317f4a6-1890-4b9c-920b-da2bd67036d2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_conjugate_by_successor
import Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_commute_of_nonadjacent
import Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_commute_same

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
omit [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A C P Q : Matrix (Fin 3) (Fin 3) R) :
    Commute
      (MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd P))
        (elementaryRootHom i j hij (Multiplicative.ofAdd A)))
      (MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd Q))
        (elementaryRootHom i j hij (Multiplicative.ofAdd C))) := by
  rw [MulAut.conj_apply, MulAut.conj_apply,
    finiteOuterElementaryRoot_conjugate_by_successor
      i j k hij hjk hik A P,
    finiteOuterElementaryRoot_conjugate_by_successor
      i j k hij hjk hik C Q]
  have hzz := finiteOuterElementaryRoot_commute_same
    i k hik (A * P) (C * Q)
  have hzx := finiteOuterElementaryRoot_commute_of_nonadjacent
    i k i j hik hij hik.symm hij.symm (A * P) C
  have hxz := finiteOuterElementaryRoot_commute_of_nonadjacent
    i j i k hij hik hij.symm hik.symm A (C * Q)
  have hxx := finiteOuterElementaryRoot_commute_same i j hij A C
  exact (hzz.inv_inv.mul_right hzx.inv_left).mul_left
    (hxz.inv_right.mul_right hxx)
end SoficGroups
