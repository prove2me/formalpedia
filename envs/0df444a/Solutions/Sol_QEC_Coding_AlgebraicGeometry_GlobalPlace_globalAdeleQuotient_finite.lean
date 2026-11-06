-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotient_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:25:49.180699+00:00
-- url     : https://prove2.me/submissions/e6dc1726-4d00-47ca-9d85-f6555cdb6daf

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_riemannRochDefect_eq_genus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffQuotient_finite_of_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDefect_le_genus
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
    Module.Finite k (GlobalAdeleQuotient (k := k) (F := F) D) := by
  classical
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
  let p := globalAdeleFilter (k := k) (F := F) E
  let q := Submodule.comap p.subtype
    (globalAdeleFilter (k := k) (F := F) D)
  let denominator := globalAdeleFilterAddDiagonal (k := k) (F := F) D
  letI : AddCommGroup ↥p := Submodule.addCommGroup _
  letI : Module k ↥p := Submodule.module _
  haveI : Module.Finite k (↥p ⧸ q) :=
    globalAdeleFilterDiffQuotient_finite_of_le hDE
  let quotientMap := denominator.mkQ.comp (p.subtype : p →ₗ[k]
    GlobalAdele (k := k) (F := F))
  have hqker : q ≤ quotientMap.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    apply (Submodule.Quotient.mk_eq_zero denominator).mpr
    exact Submodule.mem_sup_left hx
  let induced := q.liftQ quotientMap hqker
  have hinduced : Function.Surjective induced := by
    intro z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective denominator z
    have ha : a ∈ p + diagonalAdeleSubmodule (k := k) (F := F) := by
      rw [← hfull]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp ha with ⟨x, hxp, y, hyr, hxy⟩
    refine ⟨Submodule.Quotient.mk ⟨x, hxp⟩, ?_⟩
    change Submodule.Quotient.mk x = Submodule.Quotient.mk a
    apply (Submodule.Quotient.eq denominator).mpr
    have hnegy : -y ∈ denominator :=
      denominator.neg_mem (Submodule.mem_sup_right hyr)
    simpa only [← hxy, sub_add_eq_sub_sub, sub_self, zero_sub] using hnegy
  exact Module.Finite.of_surjective induced hinduced
end QEC.Coding.AlgebraicGeometry.GlobalPlace
