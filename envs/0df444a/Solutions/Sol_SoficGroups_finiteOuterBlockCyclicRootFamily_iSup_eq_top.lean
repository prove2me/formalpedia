-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockCyclicRootFamily_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/1c35948a-38fd-447a-aa4a-035fe8326158

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_cyclicFiniteBlockRootSubgroup_eq_elementaryGroup
import Theorems.Thm_SoficGroups_finiteOuterBlockRootSubgroup_map_flatten

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators
namespace SoficGroups
theorem _root_.solution
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (s : Finset R)
    (hs : Algebra.adjoin (ZMod 2) (↑s : Set R) = ⊤) :
    (⨆ i : Fin 3,
      finiteOuterBlockCyclicRootFamily (finiteBlockCoefficientSpan s) i) =
        ⊤ := by
  let W : Submodule (ZMod 2) R := finiteBlockCoefficientSpan s
  let L : Subgroup
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
    finiteOuterBlockRootSubgroup W 0 1 (by decide) ⊔
      finiteOuterBlockRootSubgroup W 1 2 (by decide) ⊔
        finiteOuterBlockRootSubgroup W 2 0 (by decide)
  let φ := finiteOuterBlockFlattenHom (R := R)
  have hmap :
      L.map φ = elementaryGroup (Fin 9) R := by
    calc
      L.map φ = cyclicFiniteBlockRootSubgroup W := by
        dsimp [L, φ]
        rw [Subgroup.map_sup, Subgroup.map_sup,
          finiteOuterBlockRootSubgroup_map_flatten,
          finiteOuterBlockRootSubgroup_map_flatten,
          finiteOuterBlockRootSubgroup_map_flatten]
        rfl
      _ = elementaryGroup (Fin 9) R := by
        exact cyclicFiniteBlockRootSubgroup_eq_elementaryGroup s hs
  let e :
      elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) ≃*
        elementaryGroup (Fin 9) R :=
    (LeavittElementaryMorita.elementaryBlockGroupEquiv
      (ι := Fin 3) (κ := Fin 3) (R := R)).trans
      (LeavittElementaryMorita.elementaryReindexGroupEquiv
        (R := R) (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9))
  have hcompat
      (x : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :
      (e x : (Matrix (Fin 9) (Fin 9) R)ˣ) = φ x := by
    rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact (Units.mapEquiv
      (finiteBlockFlattenRingEquiv (R := R)).toMulEquiv).injective hxy
  have hLtop : L = ⊤ := by
    apply top_unique
    intro x _
    have hx :
        φ x ∈ elementaryGroup (Fin 9) R := by
      rw [← hcompat]
      exact (e x).property
    rw [← hmap] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have heq : z = x := hinj hzx
    simpa [heq] using hz
  apply top_unique
  rw [← hLtop]
  dsimp [L, W]
  exact sup_le
    (sup_le
      (le_iSup (finiteOuterBlockCyclicRootFamily
        (finiteBlockCoefficientSpan s)) 0)
      (le_iSup (finiteOuterBlockCyclicRootFamily
        (finiteBlockCoefficientSpan s)) 1))
    (le_iSup (finiteOuterBlockCyclicRootFamily
      (finiteBlockCoefficientSpan s)) 2)
end SoficGroups
