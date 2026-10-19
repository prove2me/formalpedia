-- Prove2me | solution 1 for SoficGroups.matched_partition_part_eq_of_target_part_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/dc0eba8c-3180-41a9-86a7-b6d73e93bd06

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    {x y : V} (hx : x ∈ matchedCore R D)
    (hy : y ∈ matchedCore R D)
    (hpart : Q.part x = Q.part y) :
    P.part x = P.part y := by
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨E, hE, hyE⟩ := Finset.mem_biUnion.mp hy
  have hxparts := Finset.mem_inter.mp hxC
  have hyparts := Finset.mem_inter.mp hyE
  have hQx : Q.part x = D C :=
    Q.part_eq_of_mem (hD C hC) hxparts.2
  have hQy : Q.part y = D E :=
    Q.part_eq_of_mem (hD E hE) hyparts.2
  have hCE : C = E := hinj hC hE (hQx.symm.trans (hpart.trans hQy))
  calc
    P.part x = C := P.part_eq_of_mem (hR hC) hxparts.1
    _ = E := hCE
    _ = P.part y := (P.part_eq_of_mem (hR hE) hyparts.1).symm
end SoficGroups
