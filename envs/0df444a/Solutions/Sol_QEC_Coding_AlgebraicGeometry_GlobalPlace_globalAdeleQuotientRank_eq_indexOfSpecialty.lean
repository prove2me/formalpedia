-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientRank_eq_indexOfSpecialty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:25:50.021+00:00
-- url     : https://prove2.me/submissions/d237919a-2195-4cb6-8f78-18d3630483fc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleQuotientRank_eq_sandwichRank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_riemannRochDefect_eq_genus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSandwichRank_eq_defect_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDefect_le_genus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochIndexOfSpecialty_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleQuotientAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleQuotientScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientFilterModule
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (D : Divisor (GlobalPlace k F)) :
    globalAdeleQuotientRank (k := k) (F := F) D =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
  obtain ⟨G, hG⟩ := exists_riemannRochDefect_eq_genus
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  let E := D ⊔ G
  have hDE : D ≤ E := le_sup_left
  have hGE : G ≤ E := le_sup_right
  have hE : riemannRochDefect (k := k) (F := F) E =
      (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) := by
    have hlower := riemannRochDefect_mono
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hGE
    have hupper := riemannRochDefect_le_genus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F E
    omega
  have hfull :=
    globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hE
  have hrank := globalAdeleQuotientRank_eq_sandwichRank
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE hfull
  have hsandwich := globalAdeleSandwichRank_eq_defect_sub
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
  have hindex := riemannRochIndexOfSpecialty_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  have hsandwichGenus :
      globalAdeleSandwichRank (k := k) (F := F) D E hDE =
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) -
          riemannRochDefect (k := k) (F := F) D := by
    rw [hsandwich, hE]
  have hindexGenus :
      (riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D : ℤ) =
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) -
          riemannRochDefect (k := k) (F := F) D := by
    rw [hindex]
    simp only [riemannRochDefect]
    ring
  calc
    globalAdeleQuotientRank (k := k) (F := F) D =
        (globalAdeleSandwichRank (k := k) (F := F) D E hDE).toNat := hrank
    _ = ((functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) -
          riemannRochDefect (k := k) (F := F) D).toNat := by
      rw [hsandwichGenus]
    _ = riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
      rw [← hindexGenus]
      simp only [Int.toNat_natCast]
end QEC.Coding.AlgebraicGeometry.GlobalPlace
