-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockProductCentral_centerComplement_inner_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/b6577dca-fbc6-4cdf-b6c1-4708d54b4f28

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteBlockGaloisField_natCard
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_commute_left
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_commute_right
import Theorems.Thm_SoficGroups_finiteOuterBlockGaloisConjugatorWithCoefficient_mem
import Theorems.Thm_SoficGroups_finiteOuterBlockGaloisConjugateRootsWithCoefficient_commute
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_le_galoisConjugates
import Theorems.Thm_SoficGroups_heisenbergFiniteFamily_centerComplement_inner_sq_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    {H : Type v₁} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (π : UnitaryRepresentation
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) H)
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π
      (finiteOuterBlockRootSubgroup W i j hij))
    (haZ : a ∈
      (unitaryFixedSubmodule π
        (finiteOuterBlockProductCentralRootSubgroup W i k hik B))ᗮ)
    (hb : b ∈ unitaryFixedSubmodule π
      (finiteOuterBlockRootSubgroup W j k hjk)) :
    8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  letI : Fintype finiteBlockGaloisField :=
    Fintype.ofFinite finiteBlockGaloisField
  have hcard : Fintype.card finiteBlockGaloisField = 8 := by
    simpa only [Nat.card_eq_fintype_card] using
      finiteBlockGaloisField_natCard
  have hbound := heisenbergFiniteFamily_centerComplement_inner_sq_le
    π
    (finiteOuterBlockRootSubgroup W i j hij)
    (finiteOuterBlockProductCentralRootSubgroup W i k hik B)
    (fun t : finiteBlockGaloisField =>
      finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B t)
    (by
      intro x z
      exact finiteOuterBlockProductCentralRoot_commute_left
        W i j k hij hik B x z x.property z.property)
    (by
      intro t z
      exact finiteOuterBlockProductCentralRoot_commute_right
        W i j k hjk hik B
        (finiteOuterBlockGaloisConjugatorWithCoefficient
          W j k hjk B t) z
        (finiteOuterBlockGaloisConjugatorWithCoefficient_mem
          W j k hjk B t) z.property)
    (by
      intro s t hst x x'
      exact finiteOuterBlockGaloisConjugateRootsWithCoefficient_commute
        W i j k hij hjk hik B s t x x' x.property x'.property)
    (by
      intro s t hst
      exact finiteOuterBlockProductCentralRoot_le_galoisConjugates
        W i j k hij hjk hik B s t hst)
    ha haZ
    (by
      intro t
      exact
        (mem_unitaryFixedSubmodule π
          (finiteOuterBlockRootSubgroup W j k hjk) b).mp hb
          ⟨finiteOuterBlockGaloisConjugatorWithCoefficient
            W j k hjk B t,
            finiteOuterBlockGaloisConjugatorWithCoefficient_mem
              W j k hjk B t⟩)
  simpa [hcard] using hbound
end SoficGroups
