-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientRank_eq_sandwichRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:18:48.862597+00:00
-- url     : https://prove2.me/submissions/58f54d37-4c38-4942-a82a-10c2c882e95f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
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
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E)
    (hfull : globalAdeleTopSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) :
    globalAdeleQuotientRank (k := k) (F := F) D =
      (globalAdeleSandwichRank (k := k) (F := F) D E hDE).toNat := by
  classical
  let denominator := globalAdeleFilterAddDiagonal (k := k) (F := F) D
  let topModule := globalAdeleTopSubmodule (k := k) (F := F)
  letI : AddCommGroup ↥topModule := Submodule.addCommGroup _
  letI : Module k ↥topModule := Submodule.module _
  let q := Submodule.comap topModule.subtype denominator
  let e : ↥topModule ≃ₗ[k] GlobalAdele (k := k) (F := F) :=
    Submodule.topEquiv (R := k) (M := GlobalAdele (k := k) (F := F))
  have hmap := Submodule.map_comap_subtype
    (p := topModule) (p' := denominator)
  have heq : (e : ↥topModule →ₗ[k] GlobalAdele (k := k) (F := F)) =
      topModule.subtype := by
    apply LinearMap.ext
    rintro ⟨a, ha⟩
    apply Subtype.ext
    funext P
    rfl
  have hqmap : q.map (e : ↥topModule →ₗ[k]
      GlobalAdele (k := k) (F := F)) = denominator := by
    rw [show q.map (e : ↥topModule →ₗ[k]
        GlobalAdele (k := k) (F := F)) = q.map topModule.subtype by rw [heq],
      hmap, inf_eq_right]
    exact le_top
  dsimp only [globalAdeleQuotientRank, globalAdeleSandwichRank,
    globalAdeleFilterAddDiagonal, denominator]
  rw [← (Submodule.Quotient.equiv q denominator e hqmap).finrank_eq,
    hfull.symm]
  simp only [topModule, globalAdeleTopSubmodule, q]
  simp only [denominator, globalAdeleFilterAddDiagonal,
    Int.ofNat_eq_natCast, Int.toNat_natCast]
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
