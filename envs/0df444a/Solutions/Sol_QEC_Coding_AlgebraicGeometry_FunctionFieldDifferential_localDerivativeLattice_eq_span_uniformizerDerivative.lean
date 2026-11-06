-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.localDerivativeLattice_eq_span_uniformizerDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:24:10.86742+00:00
-- url     : https://prove2.me/submissions/60d75c8c-6503-4de8-8e56-f622a905e04f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_maximalIdeal_eq_span_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
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
namespace FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
omit [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F] in
/-- The cardinality of a global place's finite residue field vanishes in the
function field. -/
private theorem residueFieldCard_cast_eq_zero (P : GlobalPlace k F)
    [Fintype P.residueField] :
    ((Fintype.card P.residueField : ℕ) : F) = 0 := by
  have hresidue : ((Fintype.card P.residueField : ℕ) : P.residueField) = 0 :=
    FiniteField.cast_card_eq_zero P.residueField
  have hconstant : ((Fintype.card P.residueField : ℕ) : k) = 0 := by
    apply (GlobalPlace.constantsToResidue P).injective
    simpa only [map_natCast, map_zero] using hresidue
  calc
    ((Fintype.card P.residueField : ℕ) : F) =
        algebraMap k F ((Fintype.card P.residueField : ℕ) : k) := by simp
    _ = algebraMap k F 0 := by rw [hconstant]
    _ = 0 := map_zero _
private theorem functionFieldDerivation_mem_uniformizerDerivative_sup
    (P : GlobalPlace k F) (x : P.valuationRing) :
    functionFieldDerivation (k := k) (F := F) (x : F) ∈
      Submodule.span P.valuationRing
          ({functionFieldDerivation (k := k) (F := F)
            (P.uniformizerInValuationRing : F)} : Set F) ⊔
        (localDerivativeLattice (k := k) (F := F) P).map
          (LinearMap.lsmul P.valuationRing F P.uniformizerInValuationRing) := by
  classical
  letI : Algebra (Polynomial k) F :=
    ((algebraMap (RatFunc k) F).comp
      (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Finite P.residueField := GlobalPlace.finite_residueField P
  letI : Fintype P.residueField := Fintype.ofFinite _
  let q : ℕ := Fintype.card P.residueField
  let D : Derivation k F F := functionFieldDerivation (k := k) (F := F)
  let pi : P.valuationRing := P.uniformizerInValuationRing
  have hresidue : P.residue (x ^ q - x) = 0 := by
    rw [map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hmaximal : x ^ q - x ∈ IsLocalRing.maximalIdeal P.valuationRing :=
    (GlobalPlace.residue_eq_zero_iff P _).mp hresidue
  rw [P.maximalIdeal_eq_span_uniformizer, Ideal.mem_span_singleton'] at hmaximal
  rcases hmaximal with ⟨r, hr⟩
  have hrF : (r : F) * (pi : F) = (x : F) ^ q - (x : F) := by
    exact congrArg (fun z : P.valuationRing => (z : F)) hr
  have hqF : (q : F) = 0 := by
    simpa only [q] using residueFieldCard_cast_eq_zero (k := k) (F := F) P
  have hderivative := congrArg D hrF
  have hxformula :
      D (x : F) = (-(r : F)) * D (pi : F) + (pi : F) * (-D (r : F)) := by
    rw [D.leibniz, map_sub, D.leibniz_pow] at hderivative
    simp only [nsmul_eq_mul, smul_eq_mul, hqF, zero_mul, zero_sub] at hderivative
    calc
      D (x : F) = -(-D (x : F)) := by ring
      _ = -((r : F) * D (pi : F) + (pi : F) * D (r : F)) := by
        rw [← hderivative]
      _ = (-(r : F)) * D (pi : F) + (pi : F) * (-D (r : F)) := by ring
  have hleft : (-(r : F)) * D (pi : F) ∈
      Submodule.span P.valuationRing ({D (pi : F)} : Set F) := by
    refine Submodule.mem_span_singleton.mpr ⟨-r, ?_⟩
    change (-(r : F)) * D (pi : F) = (-(r : F)) * D (pi : F)
    rfl
  have hDr : D (r : F) ∈ localDerivativeLattice (k := k) (F := F) P :=
    Submodule.subset_span ⟨r, rfl⟩
  have hright : (pi : F) * (-D (r : F)) ∈
      (localDerivativeLattice (k := k) (F := F) P).map
        (LinearMap.lsmul P.valuationRing F pi) := by
    refine ⟨-D (r : F),
      (localDerivativeLattice (k := k) (F := F) P).neg_mem hDr, ?_⟩
    change (pi : F) * (-D (r : F)) = (pi : F) * (-D (r : F))
    rfl
  exact Submodule.mem_sup.mpr
    ⟨_, hleft, _, hright, hxformula.symm⟩
private theorem exists_isUnit_smul_eq_uniformizerDerivative_of_principalCutoff
    (P : GlobalPlace k F) (a : F)
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    ∃ s : P.valuationRing, IsUnit s ∧
      s • a = functionFieldDerivation (k := k) (F := F)
        (P.uniformizerInValuationRing : F) := by
  classical
  let D : Derivation k F F := functionFieldDerivation (k := k) (F := F)
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let L : Submodule P.valuationRing F :=
    localDerivativeLattice (k := k) (F := F) P
  let S : Submodule P.valuationRing F :=
    Submodule.span P.valuationRing ({D (pi : F)} : Set F)
  let piL : Submodule P.valuationRing F :=
    L.map (LinearMap.lsmul P.valuationRing F pi)
  have hL_le : L ≤ S ⊔ piL := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    exact functionFieldDerivation_mem_uniformizerDerivative_sup
      (k := k) (F := F) P x
  have ha_mem : a ∈ L := by
    change a ∈ localDerivativeLattice (k := k) (F := F) P
    rw [ha.2.1]
    exact Submodule.mem_span_singleton_self a
  have ha_sup : a ∈ S ⊔ piL := hL_le ha_mem
  rcases Submodule.mem_sup.mp ha_sup with ⟨y, hy, z, hz, hyz⟩
  rcases Submodule.mem_span_singleton.mp hy with ⟨u, hu⟩
  rcases hz with ⟨b, hb, hbz⟩
  have hb' : b ∈ Submodule.span P.valuationRing ({a} : Set F) := by
    change b ∈ localDerivativeLattice (k := k) (F := F) P at hb
    rwa [ha.2.1] at hb
  rcases Submodule.mem_span_singleton.mp hb' with ⟨t, ht⟩
  have hDpi_mem : D (pi : F) ∈ L := Submodule.subset_span ⟨pi, rfl⟩
  have hDpi' : D (pi : F) ∈ Submodule.span P.valuationRing ({a} : Set F) := by
    change D (pi : F) ∈ localDerivativeLattice (k := k) (F := F) P at hDpi_mem
    rwa [ha.2.1] at hDpi_mem
  rcases Submodule.mem_span_singleton.mp hDpi' with ⟨s, hs⟩
  have huF : (u : F) * D (pi : F) = y := by
    exact hu
  have htF : (t : F) * a = b := by
    exact ht
  have hsF : (s : F) * a = D (pi : F) := by
    exact hs
  have hbzF : (pi : F) * b = z := by
    exact hbz
  have hdecomposition : (u : F) * D (pi : F) + (pi : F) * b = a := by
    calc
      (u : F) * D (pi : F) + (pi : F) * b = y + z := by rw [huF, hbzF]
      _ = a := hyz
  have hcoefficientF : (u : F) * (s : F) + (pi : F) * (t : F) = 1 := by
    apply mul_right_cancel₀ ha.1
    calc
      ((u : F) * (s : F) + (pi : F) * (t : F)) * a =
          (u : F) * ((s : F) * a) + (pi : F) * ((t : F) * a) := by ring
      _ = (u : F) * D (pi : F) + (pi : F) * b := by rw [hsF, htF]
      _ = a := hdecomposition
      _ = 1 * a := by rw [one_mul]
  have hcoefficient : u * s + pi * t = 1 := by
    apply Subtype.ext
    exact hcoefficientF
  have hs_not_maximal : s ∉ IsLocalRing.maximalIdeal P.valuationRing := by
    intro hs_maximal
    have hpi_maximal : pi ∈ IsLocalRing.maximalIdeal P.valuationRing := by
      rw [P.maximalIdeal_eq_span_uniformizer]
      exact Ideal.mem_span_singleton_self pi
    have hus : u * s ∈ IsLocalRing.maximalIdeal P.valuationRing :=
      (IsLocalRing.maximalIdeal P.valuationRing).mul_mem_left u hs_maximal
    have hpit : pi * t ∈ IsLocalRing.maximalIdeal P.valuationRing := by
      simpa only [mul_comm] using
        (IsLocalRing.maximalIdeal P.valuationRing).mul_mem_left t hpi_maximal
    have hone : (1 : P.valuationRing) ∈ IsLocalRing.maximalIdeal P.valuationRing := by
      rw [← hcoefficient]
      exact (IsLocalRing.maximalIdeal P.valuationRing).add_mem hus hpit
    simp at hone
  have hs_unit : IsUnit s := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using
      hs_not_maximal
  exact ⟨s, hs_unit, hs⟩
end FunctionFieldDifferential
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    (P : GlobalPlace k F) :
    localDerivativeLattice (k := k) (F := F) P =
      Submodule.span P.valuationRing
        ({functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F)} : Set F) := by
  obtain ⟨a, ha⟩ :=
    exists_localDerivativeLatticePrincipalCutoff (k := k) (F := F) P
  obtain ⟨s, hs_unit, hs⟩ :=
    exists_isUnit_smul_eq_uniformizerDerivative_of_principalCutoff
      (k := k) (F := F) P a ha
  calc
    localDerivativeLattice (k := k) (F := F) P =
        Submodule.span P.valuationRing ({a} : Set F) := ha.2.1
    _ = Submodule.span P.valuationRing ({s • a} : Set F) :=
      (Submodule.span_singleton_smul_eq hs_unit a).symm
    _ = Submodule.span P.valuationRing
        ({functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F)} : Set F) := by rw [hs]
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
