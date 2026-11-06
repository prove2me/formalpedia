-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:21:38.903696+00:00
-- url     : https://prove2.me/submissions/34ad580c-ae8e-4e3f-8237-beb476ccdfd1

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_globalAdeleFilter_mem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSandwichRank_eq_defect_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_add_diagonal_eq_of_sandwichRank_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDefect_le_genus

section
namespace QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] globalAdeleSandwichAlgebra
attribute [local instance] globalAdeleSandwichScalarTower
namespace GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] globalAdeleSandwichFilterAddCommGroup
attribute [local instance] globalAdeleSandwichFilterModule
private theorem riemannRochDefect_eq_genus_of_ge
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E)
    (hD : riemannRochDefect (k := k) (F := F) D =
      functionFieldGenus (k := k) (F := F)) :
    riemannRochDefect (k := k) (F := F) E =
      functionFieldGenus (k := k) (F := F) := by
  have hlower := riemannRochDefect_mono
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
  have hupper := riemannRochDefect_le_genus
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F E
  omega
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleSandwichAlgebra
attribute [local instance] globalAdeleSandwichAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleSandwichScalarTower
attribute [local instance] globalAdeleSandwichScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichFilterAddCommGroup
attribute [local instance] globalAdeleSandwichFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichFilterModule
attribute [local instance] globalAdeleSandwichFilterModule
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    {D : Divisor (GlobalPlace k F)}
    (hD : riemannRochDefect (k := k) (F := F) D =
      functionFieldGenus (k := k) (F := F)) :
    globalAdeleTopSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) D +
        diagonalAdeleSubmodule (k := k) (F := F) := by
  apply le_antisymm
  · intro a _
    obtain ⟨Da, ha⟩ := exists_globalAdeleFilter_mem (k := k) (F := F) a
    let E := D ⊔ Da
    have hDE : D ≤ E := le_sup_left
    have hE : riemannRochDefect (k := k) (F := F) E =
        functionFieldGenus (k := k) (F := F) :=
      riemannRochDefect_eq_genus_of_ge
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE hD
    have hrank := globalAdeleSandwichRank_eq_defect_sub
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
    have hzero : globalAdeleSandwichRank (k := k) (F := F) D E hDE = 0 := by
      rw [hrank, hE, hD, sub_self]
    have heq := globalAdeleFilter_add_diagonal_eq_of_sandwichRank_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE hzero
    have hmem : a ∈ globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F) :=
      Submodule.mem_sup_left (globalAdeleFilter_mono le_sup_right ha)
    rw [heq] at hmem
    exact hmem
  · exact le_top
end QEC.Coding.AlgebraicGeometry.GlobalPlace
