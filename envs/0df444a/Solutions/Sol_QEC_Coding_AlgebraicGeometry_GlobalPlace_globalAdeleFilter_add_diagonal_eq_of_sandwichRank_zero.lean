-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_add_diagonal_eq_of_sandwichRank_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:18:48.061456+00:00
-- url     : https://prove2.me/submissions/e749f44f-9be5-4bc8-8998-a1db4c7c75bd

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffQuotient_finite_of_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_inf_diagonal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_IsFullConstantField_mem_range
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
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E)
    (hzero : globalAdeleSandwichRank (k := k) (F := F) D E hDE = 0) :
    globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) D +
        diagonalAdeleSubmodule (k := k) (F := F) := by
  let p := globalAdeleFilter (k := k) (F := F) E
  let sA := globalAdeleFilter (k := k) (F := F) D
  let r := diagonalAdeleSubmodule (k := k) (F := F)
  let l := Submodule.map (diagonalAdele (k := k) (F := F))
    (riemannRochSubmodule E)
  let t := l ⊔ sA
  let qp := Submodule.comap p.subtype sA
  let qt := Submodule.comap p.subtype t
  have hs_le_p : sA ≤ p := globalAdeleFilter_mono hDE
  have htp : t ≤ p := by
    rintro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨f, hf, rfl⟩
    exact Submodule.add_mem p
      (by exact hf)
      (hs_le_p hz)
  have hinter : p ⊓ (sA + r) = t := by
    have hmod : p ⊓ (sA + r) = sA + p ⊓ r := by
      apply le_antisymm
      · rintro x ⟨hxp, hxsr⟩
        rcases Submodule.mem_sup.mp hxsr with ⟨a, has, y, hy, rfl⟩
        obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
        refine Submodule.mem_sup.mpr ⟨a, has,
          diagonalAdele (k := k) (F := F) f, ?_, rfl⟩
        exact Submodule.mem_inf.mpr
          ⟨(by simpa only [add_sub_cancel_left] using
              Submodule.sub_mem p hxp (hs_le_p has)), hy⟩
      · rintro x hx
        rcases Submodule.mem_sup.mp hx with ⟨a, has, y, hy, rfl⟩
        rcases Submodule.mem_inf.mp hy with ⟨hyp, hyr⟩
        exact ⟨Submodule.add_mem p (hs_le_p has) hyp,
          Submodule.add_mem (sA + r) (Submodule.mem_sup_left has)
            (Submodule.mem_sup_right hyr)⟩
    have hpr : p ⊓ r = l := globalAdeleFilter_inf_diagonal E
    calc
      p ⊓ (sA + r) = sA + (p ⊓ r) := hmod
      _ = sA + l := by rw [hpr]
      _ = t := by simp only [t, Submodule.add_eq_sup, sup_comm]
  have hqp_le : qp ≤ qt := Submodule.comap_mono le_sup_right
  letI : AddCommGroup p := Submodule.addCommGroup _
  letI : Module k p := Submodule.module _
  letI : AddCommGroup (p + r) := Submodule.addCommGroup _
  letI : Module k (p + r) := Submodule.module _
  haveI : Module.Finite k (p ⧸ qp) :=
    globalAdeleFilterDiffQuotient_finite_of_le hDE
  haveI : Module.Finite k (p ⧸ qt) :=
    Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient qp qt hqp_le)
  have hfin_qt : Module.finrank k (p ⧸ qt) = 0 := by
    have hfin_sandwich :
        Module.finrank k
          ((p + r) ⧸ Submodule.comap (p + r).subtype (sA + r)) = 0 :=
      Int.ofNat_eq_zero.mp hzero
    have hinfl :
        Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype (sA + r) = qt := by
      rw [← Submodule.comap_inf, hinter]
    have hpsum : p ⊔ (sA + r) = p + r := by
      rw [← Submodule.add_eq_sup]
      apply le_antisymm
      · exact sup_le le_sup_left (add_le_add hs_le_p le_rfl)
      · intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
        have hb' : b ∈ sA + r := Submodule.mem_sup_right hb
        exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
          (Submodule.mem_sup_right hb')
    letI : AddCommGroup ↥(p ⊔ (sA + r)) := Submodule.addCommGroup _
    letI : Module k ↥(p ⊔ (sA + r)) := Submodule.module _
    have hsand := (LinearMap.quotientInfEquivSupQuotient p (sA + r)).symm.finrank_eq
    rw [hpsum, hinfl] at hsand
    exact hsand.symm.trans hfin_sandwich
  have hsub : Subsingleton (p ⧸ qt) := Module.finrank_zero_iff.mp hfin_qt
  have htopqt : qt = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub
  have hp_le_t : p ≤ t := Submodule.comap_subtype_eq_top.mp htopqt
  have hp_eq_t : p = t := le_antisymm hp_le_t htp
  have hp_le_sr : p ≤ sA + r := by
    have h := inf_le_right (a := p) (b := sA + r)
    rw [hinter] at h
    exact hp_eq_t.symm ▸ h
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨a, hap, y, hyr, rfl⟩
    rcases Submodule.mem_sup.mp (hp_le_sr hap) with ⟨b, hbs, w, hwr, hbc⟩
    exact Submodule.mem_sup.mpr
      ⟨b, hbs, w + y, Submodule.add_mem r hwr hyr, by rw [← hbc, add_assoc]⟩
  · exact add_le_add hs_le_p le_rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
