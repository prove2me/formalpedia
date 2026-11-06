-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffQuotient_finite_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:43:46.627207+00:00
-- url     : https://prove2.me/submissions/86f2e3af-1d35-46b2-a8ef-8f51b445dec4

import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleLocalLeadingCoefficient_ker
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


section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
attribute [local instance] globalAdeleFilterAddCommGroup
attribute [local instance] globalAdeleFilterModule
private theorem globalAdeleFilterDiffQuotient_finite_add_placeDivisor
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) ⧸
        Submodule.comap
          (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField := residueField_finiteDimensional P
  let f := globalAdeleLocalLeadingCoefficient (k := k) (F := F) D P
  let p := Submodule.comap
    (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)).subtype
    (globalAdeleFilter (k := k) (F := F) D)
  haveI : Module.Finite k f.range := inferInstance
  haveI : Module.Finite k
      (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq f.ker p
    (globalAdeleLocalLeadingCoefficient_ker (k := k) (F := F) D P))
private theorem globalAdeleFilterDiffQuotient_finite_self
    (D : Divisor (GlobalPlace k F)) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) D ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) D).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  rw [show Submodule.comap
      (globalAdeleFilter (k := k) (F := F) D).subtype
      (globalAdeleFilter (k := k) (F := F) D) = ⊤ from
    Submodule.comap_subtype_self (globalAdeleFilter (k := k) (F := F) D)]
  exact Module.Finite.of_finite
private theorem globalAdeleFilterDiffQuotient_finite_mono_add
    {D M N : Divisor (GlobalPlace k F)} (hDM : D ≤ M) (hMN : M ≤ N)
    [Module.Finite k
      (globalAdeleFilter (k := k) (F := F) N ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) N).subtype
          (globalAdeleFilter (k := k) (F := F) M))]
    [Module.Finite k
      (globalAdeleFilter (k := k) (F := F) M ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) M).subtype
          (globalAdeleFilter (k := k) (F := F) D))] :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) N ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) N).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  let p := globalAdeleFilter (k := k) (F := F) N
  let q := Submodule.comap p.subtype (globalAdeleFilter (k := k) (F := F) D)
  let r := Submodule.comap p.subtype (globalAdeleFilter (k := k) (F := F) M)
  let pM := globalAdeleFilter (k := k) (F := F) M
  let qM := Submodule.comap pM.subtype (globalAdeleFilter (k := k) (F := F) D)
  have hqr : q ≤ r := Submodule.comap_mono (globalAdeleFilter_mono hDM)
  let eR := Submodule.comapSubtypeEquivOfLe (globalAdeleFilter_mono hMN)
  let qInR : Submodule k ↑r := Submodule.comap r.subtype q
  have hqmap : qM.map (eR.symm : pM →ₗ[k] r) = qInR := by
    rw [Submodule.map_equiv_eq_comap_symm eR.symm qM]
    rfl
  have eMq : (pM ⧸ qM) ≃ₗ[k] (r ⧸ qInR) :=
    Submodule.Quotient.equiv qM qInR eR.symm hqmap
  haveI : Module.Finite k (r ⧸ qInR) := Module.Finite.equiv eMq
  have hker : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).ker = qInR := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).range =
      r.map q.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eQuot : (r ⧸ qInR) ≃ₗ[k] r.map q.mkQ := by
    rw [← hker, ← hrange]
    exact LinearMap.quotKerEquivRange (q.mkQ.comp (r.subtype : r →ₗ[k] p))
  haveI : Module.Finite k (r.map q.mkQ) := Module.Finite.equiv eQuot
  have eThird := Submodule.quotientQuotientEquivQuotient q r hqr
  haveI : Module.Finite k (p ⧸ r) := by
    dsimp only [p, r]
    infer_instance
  haveI : Module.Finite k ((p ⧸ q) ⧸ Submodule.map q.mkQ r) :=
    Module.Finite.equiv eThird.symm
  exact Module.Finite.of_submodule_quotient (Submodule.map q.mkQ r)
private theorem globalAdeleFilterDiffQuotient_finite_single_nat
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (n : ℕ) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) (D + Finsupp.single P (n : ℤ)) ⧸
        Submodule.comap
          (globalAdeleFilter (k := k) (F := F)
            (D + Finsupp.single P (n : ℤ))).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  classical
  induction n with
  | zero =>
      have heq : D + Finsupp.single P ((0 : ℕ) : ℤ) = D := by simp
      rw [heq]
      exact globalAdeleFilterDiffQuotient_finite_self D
  | succ n ih =>
      have heq : D + Finsupp.single P ((n + 1 : ℕ) : ℤ) =
          D + Finsupp.single P (n : ℤ) + placeDivisor P := by
        ext Q
        simp only [Finsupp.add_apply, Finsupp.single_apply, placeDivisor]
        split <;> omega
      have hDM : D ≤ D + Finsupp.single P (n : ℤ) := by
        intro Q
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hMN : D + Finsupp.single P (n : ℤ) ≤
          D + Finsupp.single P (n : ℤ) + placeDivisor P := by
        intro Q
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [placeDivisor, Finsupp.single_apply]
          split <;> omega)
      letI := ih
      haveI := globalAdeleFilterDiffQuotient_finite_add_placeDivisor
        (D + Finsupp.single P (n : ℤ)) P
      rw [heq]
      exact globalAdeleFilterDiffQuotient_finite_mono_add hDM hMN
private theorem globalAdeleFilterDiffQuotient_finite_add_nonnegative
    (D E : Divisor (GlobalPlace k F)) (hE : Divisor.Nonnegative E) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) (D + E) ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) (D + E)).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero]
      exact globalAdeleFilterDiffQuotient_finite_self D
  | single_add P coefficient tail hPtail hcoefficient ih =>
      have htailP : tail P = 0 := Finsupp.notMem_support_iff.mp hPtail
      have htail : Divisor.Nonnegative tail := by
        intro Q
        by_cases hQP : Q = P
        · subst Q
          rw [htailP]
        · simpa [Finsupp.single_apply, hQP] using hE Q
      have hcoefficient_nonnegative : 0 ≤ coefficient := by
        simpa [Finsupp.single_apply, htailP] using hE P
      letI := ih D htail
      haveI := globalAdeleFilterDiffQuotient_finite_single_nat
        (D + tail) P coefficient.toNat
      have hcoefficient_cast : (coefficient.toNat : ℤ) = coefficient :=
        Int.toNat_of_nonneg hcoefficient_nonnegative
      have heq : D + (Finsupp.single P coefficient + tail) =
          (D + tail) + Finsupp.single P (coefficient.toNat : ℤ) := by
        rw [hcoefficient_cast]
        abel
      have hDM : D ≤ D + tail := by
        intro Q
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (htail Q)
      have hMN : D + tail ≤
          (D + tail) + Finsupp.single P (coefficient.toNat : ℤ) := by
        intro Q
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      rw [heq]
      exact globalAdeleFilterDiffQuotient_finite_mono_add hDM hMN
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

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
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) E ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) E).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have heq : E = D + (E - D) := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [heq]
  exact globalAdeleFilterDiffQuotient_finite_add_nonnegative D (E - D) hnonnegative
end QEC.Coding.AlgebraicGeometry.GlobalPlace
