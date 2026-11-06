-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffDimension_mono_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:47:08.261024+00:00
-- url     : https://prove2.me/submissions/652753af-d7e0-49f8-9901-c4183c90b704

import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffQuotient_finite_of_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterAddCommGroup
attribute [local instance] globalAdeleFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterModule
attribute [local instance] globalAdeleFilterModule
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    {D M N : Divisor (GlobalPlace k F)} (hDM : D ≤ M) (hMN : M ≤ N) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D N =
      globalAdeleFilterDiffDimension (k := k) (F := F) D M +
        globalAdeleFilterDiffDimension (k := k) (F := F) M N := by
  let p := globalAdeleFilter (k := k) (F := F) N
  let q := Submodule.comap p.subtype (globalAdeleFilter (k := k) (F := F) D)
  let r := Submodule.comap p.subtype (globalAdeleFilter (k := k) (F := F) M)
  have hqr : q ≤ r := Submodule.comap_mono (globalAdeleFilter_mono hDM)
  have hDN : D ≤ N := hDM.trans hMN
  haveI : Module.Finite k (p ⧸ q) :=
    globalAdeleFilterDiffQuotient_finite_of_le hDN
  haveI : Module.Finite k (p ⧸ r) :=
    globalAdeleFilterDiffQuotient_finite_of_le hMN
  have e := Submodule.quotientQuotientEquivQuotient q r hqr
  have hadd := Submodule.finrank_quotient_add_finrank (r.map q.mkQ)
  have hrmap : Module.finrank k (r.map q.mkQ) =
      globalAdeleFilterDiffDimension (k := k) (F := F) D M := by
    let pM := globalAdeleFilter (k := k) (F := F) M
    let qM := Submodule.comap pM.subtype (globalAdeleFilter (k := k) (F := F) D)
    let qInR : Submodule k ↑r := Submodule.comap r.subtype q
    let eR := Submodule.comapSubtypeEquivOfLe (globalAdeleFilter_mono hMN)
    have hqmap : qM.map (eR.symm : pM →ₗ[k] r) = qInR := by
      rw [Submodule.map_equiv_eq_comap_symm eR.symm qM]
      rfl
    have eM : (pM ⧸ qM) ≃ₗ[k] (r ⧸ qInR) :=
      Submodule.Quotient.equiv qM qInR eR.symm hqmap
    have hker : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).ker = qInR := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have hrange : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).range =
        r.map q.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have eQuot : (r ⧸ qInR) ≃ₗ[k] r.map q.mkQ := by
      rw [← hker, ← hrange]
      exact LinearMap.quotKerEquivRange (q.mkQ.comp (r.subtype : r →ₗ[k] p))
    dsimp only [globalAdeleFilterDiffDimension]
    rw [← eQuot.finrank_eq, eM.finrank_eq]
  calc
    Module.finrank k (p ⧸ q) =
        Module.finrank k ((p ⧸ q) ⧸ Submodule.map q.mkQ r) +
          Module.finrank k ↑(Submodule.map q.mkQ r) := hadd.symm
    _ = Module.finrank k (p ⧸ r) +
        globalAdeleFilterDiffDimension (k := k) (F := F) D M := by
      rw [e.finrank_eq, hrmap]
    _ = globalAdeleFilterDiffDimension (k := k) (F := F) D M +
        globalAdeleFilterDiffDimension (k := k) (F := F) M N := by
      dsimp only [globalAdeleFilterDiffDimension]
      rw [add_comm]
end QEC.Coding.AlgebraicGeometry.GlobalPlace
