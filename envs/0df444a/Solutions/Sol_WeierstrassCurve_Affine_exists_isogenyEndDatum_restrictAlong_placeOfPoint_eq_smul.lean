-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e1783fc8-8056-5606-95cb-3a95cb237226

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_EllipticCurve_FunctionFieldPullback
import Definitions.Def_EllipticCurve_DivisionPolynomialOmega
import Theorems.Thm_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_y_mul_psi_cube
import Theorems.Thm_WeierstrassCurve_Affine_zsmul_genericPoint_good
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
import Theorems.Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_eval_psiSq_eq_zero_of_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point AlgebraicCurve Polynomial
open scoped Polynomial.Bivariate

universe u

namespace S13MulDatum

section Generic

variable {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A] [Algebra K B]

theorem finrankAlong_eq_finrank_fieldRange (φ : A →ₐ[K] B) :
    finrankAlong K φ = Module.finrank φ.fieldRange B := by
  show (letI := algebraAlong φ; Module.finrank A B) = Module.finrank φ.fieldRange B
  letI := algebraAlong φ
  exact Algebra.finrank_eq_of_equiv_equiv
    (AlgEquiv.ofInjectiveField φ).toRingEquiv (RingEquiv.refl B) (by ext x; rfl)

def equivFieldRange (φ : A →ₐ[K] B) : A ≃ₐ[K] φ.fieldRange :=
  (AlgEquiv.ofInjectiveField φ).trans
    (Subalgebra.equivOfEq _ _ (AlgHom.fieldRange_toSubalgebra φ).symm)

theorem coe_equivFieldRange (φ : A →ₐ[K] B) (a : A) : ((equivFieldRange φ a : φ.fieldRange) : B) = φ a :=
  rfl

theorem algebraMap_comp_equivFieldRange_symm (φ : A →ₐ[K] B) :
    (letI := algebraAlong φ; (algebraMap A B).comp ((equivFieldRange φ).symm : φ.fieldRange ≃+* A).toRingHom)
      = ((RingEquiv.refl B) : B ≃+* B).toRingHom.comp (algebraMap φ.fieldRange B) := by
  letI := algebraAlong φ
  ext z
  obtain ⟨a, rfl⟩ : ∃ a, equivFieldRange φ a = z := (equivFieldRange φ).surjective z
  show φ ((equivFieldRange φ).symm (equivFieldRange φ a)) = ((equivFieldRange φ a : φ.fieldRange) : B)
  rw [AlgEquiv.symm_apply_apply, coe_equivFieldRange]

theorem finiteAlong_of_finite_fieldRange (φ : A →ₐ[K] B) [h : FiniteDimensional φ.fieldRange B] :
    FiniteAlong K φ := by
  show (letI := algebraAlong φ; Module.Finite A B)
  letI := algebraAlong φ
  exact Module.Finite.of_equiv_equiv ((equivFieldRange φ).symm : φ.fieldRange ≃+* A) (RingEquiv.refl B)
    (algebraMap_comp_equivFieldRange_symm φ)

theorem separableAlong_of_isSeparable_fieldRange (φ : A →ₐ[K] B)
    [h : Algebra.IsSeparable φ.fieldRange B] : SeparableAlong K φ := by
  show (letI := algebraAlong φ; Algebra.IsSeparable A B)
  letI := algebraAlong φ
  exact Algebra.IsSeparable.of_equiv_equiv ((equivFieldRange φ).symm : φ.fieldRange ≃+* A) (RingEquiv.refl B)
    (algebraMap_comp_equivFieldRange_symm φ)

theorem isIntegral_of_finiteAlong (ξ : A →ₐ[K] B) (hfin : FiniteAlong K ξ) :
    ξ.toRingHom.IsIntegral := by
  letI := algebraAlong ξ
  haveI : Module.Finite A B := hfin
  have h : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  intro a
  exact h.isIntegral a

def toSubfieldEquiv {L : Type*} [Field L] [Algebra K L] (E : IntermediateField K L) : E.toSubfield ≃+* E :=
  ⟨⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩, fun _ _ => rfl, fun _ _ => rfl⟩

theorem finrank_toSubfield_eq {L : Type*} [Field L] [Algebra K L] (E : IntermediateField K L) :
    Module.finrank E.toSubfield L = Module.finrank E L :=
  Algebra.finrank_eq_of_equiv_equiv (toSubfieldEquiv E) (RingEquiv.refl L) (by ext x; rfl)

theorem isSeparable_of_toSubfield {L : Type*} [Field L] [Algebra K L] (E : IntermediateField K L)
    [Algebra.IsSeparable E.toSubfield L] : Algebra.IsSeparable E L :=
  Algebra.IsSeparable.of_equiv_equiv (toSubfieldEquiv E) (RingEquiv.refl L) (by ext x; rfl)

end Generic

section Degree

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]

theorem mulGood_of_natCast_ne_zero {n : ℕ} (hn : (n : F) ≠ 0) : MulGood W F (n : ℤ) :=
  zsmul_genericPoint_good W F (by exact_mod_cast hn)

def tors (n : ℕ) : AddSubgroup (W⁄F).Point := (Submodule.torsionBy ℤ (W⁄F).Point n).toAddSubgroup

theorem mem_tors {n : ℕ} {T : (W⁄F).Point} : T ∈ tors W n ↔ (n : ℤ) • T = 0 := by
  rw [tors, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]

theorem natCard_tors {n : ℕ} (hn : (n : F) ≠ 0) : Nat.card (tors W n) = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := F) W hn
  haveI : NeZero n := ⟨hn0⟩
  rw [tors, show Nat.card ((Submodule.torsionBy ℤ (W⁄F).Point n).toAddSubgroup)
      = Nat.card (Submodule.torsionBy ℤ (W⁄F).Point n) from rfl,
    ← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]

theorem finite_tors {n : ℕ} (hn : (n : F) ≠ 0) : Finite (tors W n) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  exact Nat.finite_of_card_ne_zero (by rw [natCard_tors W hn]; exact pow_ne_zero 2 hn0)

def torsAct (n : ℕ) : Multiplicative (tors W n) →* ((W⁄F).FunctionField ≃ₐ[F] (W⁄F).FunctionField) where
  toFun T := transEquiv W F ((Multiplicative.toAdd T : tors W n) : (W⁄F).Point)
  map_one' := by
    show transEquiv W F ((Multiplicative.toAdd 1 : tors W n) : (W⁄F).Point) = 1
    rw [toAdd_one]
    exact transEquiv_zero W F
  map_mul' S T := by
    show transEquiv W F (((Multiplicative.toAdd (S * T)) : tors W n) : (W⁄F).Point) = _
    rw [toAdd_mul, AddSubgroup.coe_add, transEquiv_add]
    rfl

theorem torsAct_injective (n : ℕ) : Function.Injective (torsAct W n) := by
  intro S T h
  have h' := transEquiv_injective W F h
  exact Multiplicative.toAdd.injective (Subtype.ext h')

scoped instance torsMulSemiringAction (n : ℕ) :
    MulSemiringAction (Multiplicative (tors W n)) (W⁄F).FunctionField :=
  MulSemiringAction.compHom _ (torsAct W n)

theorem tors_smul_def (n : ℕ) (T : Multiplicative (tors W n)) (f : (W⁄F).FunctionField) :
    T • f = torsAct W n T f := rfl

scoped instance torsFaithful (n : ℕ) : FaithfulSMul (Multiplicative (tors W n)) (W⁄F).FunctionField where
  eq_of_smul_eq_smul h := torsAct_injective W n (AlgEquiv.ext h)

theorem fieldRange_le_fixed {n : ℕ} (hn : (n : F) ≠ 0) :
    (mulPull W F n).fieldRange.toSubfield
      ≤ FixedPoints.subfield (Multiplicative (tors W n)) (W⁄F).FunctionField := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, mulPull W F n g = f := by
    simpa [AlgHom.fieldRange, IntermediateField.mem_toSubfield] using hf
  intro T
  rw [tors_smul_def]
  show transEquiv W F ((Multiplicative.toAdd T : tors W n) : (W⁄F).Point) (mulPull W F n g) = mulPull W F n g
  exact transEquiv_mulPull' W F (mulGood_of_natCast_ne_zero W hn)
    ((mem_tors W).mp (Multiplicative.toAdd T).2) g

theorem fieldRange_eq_fixed {n : ℕ} (hn : (n : F) ≠ 0) :
    (mulPull W F n).fieldRange.toSubfield
      = FixedPoints.subfield (Multiplicative (tors W n)) (W⁄F).FunctionField ∧
    Module.finrank (mulPull W F n).fieldRange (W⁄F).FunctionField = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  haveI : Finite (tors W n) := finite_tors W hn
  letI : Fintype (tors W n) := Fintype.ofFinite _
  letI : Fintype (Multiplicative (tors W n)) := Fintype.ofFinite _
  set A : Subfield (W⁄F).FunctionField := (mulPull W F n).fieldRange.toSubfield with hA
  set B : Subfield (W⁄F).FunctionField :=
    FixedPoints.subfield (Multiplicative (tors W n)) (W⁄F).FunctionField with hB
  have hAB : A ≤ B := fieldRange_le_fixed W hn
  obtain ⟨hfinA, hleA⟩ :=
    WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le (K := F) W (mulGood_of_natCast_ne_zero W hn)
  rw [Int.natAbs_natCast] at hleA
  have hfA : Module.finrank A (W⁄F).FunctionField
      = Module.finrank (mulPull W F n).fieldRange (W⁄F).FunctionField := finrank_toSubfield_eq _
  have hposA : 0 < Module.finrank A (W⁄F).FunctionField := by rw [hfA]; exact Module.finrank_pos
  have hcard : Fintype.card (Multiplicative (tors W n)) = n ^ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Multiplicative.toAdd : Multiplicative (tors W n) ≃ _),
      natCard_tors W hn]
  have hfB : Module.finrank B (W⁄F).FunctionField = n ^ 2 := by
    rw [hB, FixedPoints.finrank_eq_card, hcard]
  have htower := Subfield.relfinrank_mul_finrank_top hAB
  rw [hfB] at htower
  have hsqpos : 0 < n ^ 2 := by positivity
  have hrel_le : Subfield.relfinrank A B ≤ 1 := by
    refine Nat.le_of_mul_le_mul_right ?_ hsqpos
    rw [htower, one_mul, hfA]; exact hleA
  have hrel_pos : 0 < Subfield.relfinrank A B := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at htower
    omega
  have hrel : Subfield.relfinrank A B = 1 := le_antisymm hrel_le hrel_pos
  have hEq : A = B := le_antisymm hAB (Subfield.relfinrank_eq_one_iff.mp hrel)
  refine ⟨hEq, ?_⟩
  rw [← hfA, hEq, hfB]

theorem separable_fieldRange {n : ℕ} (hn : (n : F) ≠ 0) :
    Algebra.IsSeparable (mulPull W F n).fieldRange (W⁄F).FunctionField := by
  haveI : Finite (tors W n) := finite_tors W hn
  letI : Fintype (tors W n) := Fintype.ofFinite _
  letI : Fintype (Multiplicative (tors W n)) := Fintype.ofFinite _
  have h := (fieldRange_eq_fixed W hn).1
  have hsep : Algebra.IsSeparable (FixedPoints.subfield (Multiplicative (tors W n)) (W⁄F).FunctionField)
      (W⁄F).FunctionField := inferInstance

  let e : FixedPoints.subfield (Multiplicative (tors W n)) (W⁄F).FunctionField
      ≃+* (mulPull W F n).fieldRange.toSubfield := RingEquiv.subringCongr (by rw [h])
  haveI : Algebra.IsSeparable (mulPull W F n).fieldRange.toSubfield (W⁄F).FunctionField :=
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl _) (by ext x; rfl)
  exact isSeparable_of_toSubfield _

theorem finiteAlong_mulPull {n : ℕ} (hn : (n : F) ≠ 0) : FiniteAlong F (mulPull W F n) := by
  haveI := (WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le (K := F) W (mulGood_of_natCast_ne_zero W hn)).1
  exact finiteAlong_of_finite_fieldRange _

theorem finrankAlong_mulPull {n : ℕ} (hn : (n : F) ≠ 0) : finrankAlong F (mulPull W F n) = n ^ 2 := by
  rw [finrankAlong_eq_finrank_fieldRange, (fieldRange_eq_fixed W hn).2]

theorem separableAlong_mulPull {n : ℕ} (hn : (n : F) ≠ 0) : SeparableAlong F (mulPull W F n) := by
  haveI := separable_fieldRange W hn
  exact separableAlong_of_isSeparable_fieldRange _

end Degree

section SeamHelpers

variable {F : Type u} [Field F]

theorem mem_nonunits_comap_iff {L L' : Type*} [Field L] [Field L'] (A : ValuationSubring L') (φ : L →+* L')
    (x : L) : x ∈ (A.comap φ).nonunits ↔ φ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

theorem mem_nonunits_valuationSubring_iff {L : Type*} [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (x : L) :
    x ∈ v.valuationSubring.nonunits ↔ v x < 1 := by
  rw [ValuationSubring.mem_nonunits_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one).symm

theorem valuation_aeval_eq_pow {L : Type*} [Field L] [Algebra F L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (hc : ∀ c : F, c ≠ 0 → v (algebraMap F L c) = 1) {t : L} (ht : 1 < v t)
    (p : F[X]) (hp : p ≠ 0) : v (aeval t p) = v t ^ p.natDegree := by
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    have hdecomp := p.eraseLead_add_C_mul_X_pow
    have hlead : v (aeval t (C p.leadingCoeff * X ^ p.natDegree)) = v t ^ d := by
      rw [map_mul, aeval_C, map_pow, aeval_X, map_mul, map_pow, hc _ (leadingCoeff_ne_zero.mpr hp), one_mul, hd]
    by_cases he : p.eraseLead = 0
    · conv_lhs => rw [← hdecomp, he, zero_add]
      exact hlead
    · have hlt : p.eraseLead.natDegree < d := by
        rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
        · exact hd ▸ h
        · exact absurd h he
      have hq := ih _ hlt p.eraseLead he rfl
      have hlt' : v (aeval t p.eraseLead) < v (aeval t (C p.leadingCoeff * X ^ p.natDegree)) := by
        rw [hq, hlead]; exact pow_lt_pow_right₀ ht hlt
      conv_lhs => rw [← hdecomp]
      rw [map_add, v.map_add_eq_of_lt_right hlt', hlead]

end SeamHelpers

section GenericPoint

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]

scoped instance instIsEllipticGeneric : (W⁄(W⁄F).FunctionField).IsElliptic := by
  dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance

theorem algebraMap_mk_eq_evalEval (g : F[X][Y]) :
    algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField (CoordinateRing.mk (W⁄F) g)
      = (g.map (mapRingHom (algebraMap F (W⁄F).FunctionField))).evalEval (genericX W F) (genericY W F) := by
  have h := pointHom_mk_eq_eval₂ W F (genericPoint W F) (Point.some_ne_zero _) g
  rw [pointHom_genericPoint] at h
  rw [← eval₂_eval₂RingHom_apply]
  exact h

theorem baseChange_ψ_functionField (n : ℤ) :
    (W⁄(W⁄F).FunctionField).ψ n = ((W⁄F).ψ n).map (mapRingHom (algebraMap F (W⁄F).FunctionField)) := by
  rw [show (W⁄(W⁄F).FunctionField) = (W⁄F).map (algebraMap F (W⁄F).FunctionField) from rfl, map_ψ]

theorem baseChange_φ_functionField (n : ℤ) :
    (W⁄(W⁄F).FunctionField).φ n = ((W⁄F).φ n).map (mapRingHom (algebraMap F (W⁄F).FunctionField)) := by
  rw [show (W⁄(W⁄F).FunctionField) = (W⁄F).map (algebraMap F (W⁄F).FunctionField) from rfl, map_φ]

theorem aeval_genericX (p : F[X]) :
    aeval (genericX W F) p = algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField (CoordinateRing.mk (W⁄F) (C p)) := by
  rw [algebraMap_mk_eq_evalEval, Polynomial.map_C, evalEval_C, coe_mapRingHom, eval_map, aeval_def]

theorem mulPull_genericX_mul_ΨSq {n : ℤ} (hn : (n : F) ≠ 0) :
    mulPull W F n (genericX W F) * aeval (genericX W F) ((W⁄F).ΨSq n) = aeval (genericX W F) ((W⁄F).Φ n) := by
  have hgood : MulGood W F n := zsmul_genericPoint_good W F hn
  have h1 : n • genericPoint W F =
      .some (n • genericPoint W F).xc (n • genericPoint W F).yc (nonsingular_xc_yc hgood.1) :=
    eq_some_xc_yc hgood.1
  have key := Point.zsmul_x_mul_psi_sq (W⁄(W⁄F).FunctionField) n (generic_nonsingular W F)
    (nonsingular_xc_yc hgood.1) h1

  have hψ : ((W⁄(W⁄F).FunctionField).ψ n).evalEval (genericX W F) (genericY W F) ^ 2 = aeval (genericX W F) ((W⁄F).ΨSq n) := by
    rw [baseChange_ψ_functionField, ← algebraMap_mk_eq_evalEval, ← map_pow,
      Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq, aeval_genericX]
  have hφ : ((W⁄(W⁄F).FunctionField).φ n).evalEval (genericX W F) (genericY W F) = aeval (genericX W F) ((W⁄F).Φ n) := by
    rw [baseChange_φ_functionField, ← algebraMap_mk_eq_evalEval, Affine.CoordinateRing.mk_φ,
      aeval_genericX]
  rw [mulPull_genericX' W F hgood, ← hψ, ← hφ]
  exact key

theorem aeval_genericX_injective : Function.Injective (aeval (R := F) (genericX W F) : F[X] → (W⁄F).FunctionField) := by
  intro p q h
  rw [aeval_genericX, aeval_genericX] at h
  have h' : CoordinateRing.mk (W⁄F) (C p) = CoordinateRing.mk (W⁄F) (C q) :=
    IsFractionRing.injective (W⁄F).CoordinateRing (W⁄F).FunctionField h

  have hinj : Function.Injective (algebraMap F[X] (W⁄F).CoordinateRing) := by
    intro a b hab
    have h1 : a • (CoordinateRing.basis (W⁄F) 0) = b • (CoordinateRing.basis (W⁄F) 0) := by
      rw [CoordinateRing.basis_zero, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one]
      exact hab
    have h2 := congrArg (fun v => (CoordinateRing.basis (W⁄F)).repr v 0) h1
    simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at h2
    exact h2
  exact hinj h'

theorem aeval_genericX_ne_zero {p : F[X]} (hp : p ≠ 0) : aeval (genericX W F) p ≠ 0 := fun h =>
  hp (aeval_genericX_injective W (h.trans (_root_.map_zero _).symm))

end GenericPoint

section Seam

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
variable [GenusOnePlaceGate (W⁄F)] [GenusOnePlaceGate.IsCentred (W⁄F)]

scoped instance instIsDedekindCoordinateRing : IsDedekindDomain (W⁄F).CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain W

scoped instance instIsEllipticBaseSelf : (W⁄F).IsElliptic := by
  dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance

theorem placeOfPoint_eq_ofHeightOneSpectrum (P : (W⁄F).Point) (hP : P ≠ 0) :
    placeOfPoint P = Place.ofHeightOneSpectrum (K := F) (placeOf W F P hP) := by
  conv_lhs => rw [Point.eq_some_xc_yc hP]
  exact placeOfPoint_some_eq_ofHeightOneSpectrum (Point.nonsingular_xc_yc hP) _ rfl

theorem mem_placeOfPoint_iff (P : (W⁄F).Point) (hP : P ≠ 0) (f : (W⁄F).FunctionField) :
    f ∈ (placeOfPoint P).toValuationSubring ↔ (placeOf W F P hP).valuation (W⁄F).FunctionField f ≤ 1 := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum W P hP, Place.ofHeightOneSpectrum_toValuationSubring,
    Valuation.mem_valuationSubring_iff]

theorem mem_nonunits_placeOfPoint_iff (P : (W⁄F).Point) (hP : P ≠ 0) (f : (W⁄F).FunctionField) :
    f ∈ (placeOfPoint P).toValuationSubring.nonunits
      ↔ (placeOf W F P hP).valuation (W⁄F).FunctionField f < 1 := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum W P hP, Place.ofHeightOneSpectrum_toValuationSubring,
    mem_nonunits_valuationSubring_iff]

theorem eq_placeOfPoint_zero_of_genericX_not_mem (v : Place F (W⁄F).FunctionField)
    (hv : genericX W F ∉ v.toValuationSubring) : v = placeOfPoint (0 : (W⁄F).Point) := by
  obtain ⟨R, rfl⟩ : ∃ R : (W⁄F).Point, placeOfPoint R = v :=
    ⟨(pointEquivPlace (W := W⁄F)).symm v, (pointEquivPlace (W := W⁄F)).apply_symm_apply v⟩
  rcases R with _ | ⟨a, b, h⟩
  · rfl
  · exfalso
    apply hv
    have hX := GenusOnePlaceGate.IsCentred.algebraMap_XClass_mem_nonunits (W := W⁄F) h
    have hX' : algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField (CoordinateRing.XClass (W⁄F) a)
        ∈ (placeOfPoint (Point.some a b h)).toValuationSubring :=
      (placeOfPoint (Point.some a b h)).toValuationSubring.nonunits_le hX
    have ha : algebraMap F (W⁄F).FunctionField a ∈ (placeOfPoint (Point.some a b h)).toValuationSubring :=
      (placeOfPoint (Point.some a b h)).algebraMap_mem' a
    have hsum := (placeOfPoint (Point.some a b h)).toValuationSubring.add_mem _ _ hX' ha
    have hid : algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField (CoordinateRing.XClass (W⁄F) a)
        + algebraMap F (W⁄F).FunctionField a = genericX W F := by
      rw [IsScalarTower.algebraMap_apply F (W⁄F).CoordinateRing (W⁄F).FunctionField a, ← map_add, genericX]
      congr 1
      rw [CoordinateRing.XClass, map_sub, map_sub]
      exact sub_add_cancel _ _
    rw [← hid]; exact hsum

variable {W}

theorem restrictAlong_mulPull_of_ne {n : ℕ} (hn : (n : F) ≠ 0) (hμ : (mulPull W F n).toRingHom.IsIntegral)
    (P : (W⁄F).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P ≠ 0) :
    (placeOfPoint P).restrictAlong (mulPull W F n) hμ = placeOfPoint ((n : ℤ) • P) := by
  have hQeq : (n : ℤ) • P = Point.some ((n : ℤ) • P).xc ((n : ℤ) • P).yc (Point.nonsingular_xc_yc hnP) :=
    Point.eq_some_xc_yc hnP

  have htrans : ∀ h : (W⁄F).FunctionField,
      (placeOf W F ((n : ℤ) • P) hnP).valuation (W⁄F).FunctionField h ≤ WithZero.exp (-(1 : ℤ)) →
      mulPull W F n h ∈ (placeOfPoint P).toValuationSubring.nonunits := by
    intro h hh
    rw [mem_nonunits_placeOfPoint_iff W P hP, WithZero.lt_one_iff_le_exp_neg_one]
    exact_mod_cast valuation_mulPull_le_of_ne_zero (K := F) W hn P hP hnP h 1 (by exact_mod_cast hh)
  have hXmem : (placeOf W F ((n : ℤ) • P) hnP).valuation (W⁄F).FunctionField
      (algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField (CoordinateRing.XClass (W⁄F) ((n : ℤ) • P).xc))
        ≤ WithZero.exp (-(1 : ℤ)) := by
    rw [← WithZero.lt_one_iff_le_exp_neg_one]
    apply (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mpr
    rw [placeOf_asIdeal]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hYmem : (placeOf W F ((n : ℤ) • P) hnP).valuation (W⁄F).FunctionField
      (algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField
        (CoordinateRing.YClass (W⁄F) (C ((n : ℤ) • P).yc))) ≤ WithZero.exp (-(1 : ℤ)) := by
    rw [← WithZero.lt_one_iff_le_exp_neg_one]
    apply (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mpr
    rw [placeOf_asIdeal]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have key := eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits (W := W⁄F)
    (Point.nonsingular_xc_yc hnP) ((placeOfPoint P).restrictAlong (mulPull W F n) hμ)
    (by
      change _ ∈ ((placeOfPoint P).toValuationSubring.comap (mulPull W F n).toRingHom).nonunits
      rw [mem_nonunits_comap_iff]
      exact htrans _ hXmem)
    (by
      change _ ∈ ((placeOfPoint P).toValuationSubring.comap (mulPull W F n).toRingHom).nonunits
      rw [mem_nonunits_comap_iff]
      exact htrans _ hYmem)
  rw [key, ← hQeq]

theorem mulPull_genericX_mul_ΨSq_nat {n : ℕ} (hn : (n : F) ≠ 0) :
    mulPull W F n (genericX W F) * aeval (genericX W F) ((W⁄F).ΨSq n) = aeval (genericX W F) ((W⁄F).Φ n) :=
  mulPull_genericX_mul_ΨSq W (n := (n : ℤ)) (by exact_mod_cast hn)

theorem eval_ΨSq_eq_zero_and_eval_Φ_ne_zero {n : ℕ} (P : (W⁄F).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P = 0) :
    ((W⁄F).ΨSq n).eval P.xc = 0 ∧ ((W⁄F).Φ n).eval P.xc ≠ 0 := by
  haveI : (W⁄F).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hPeq := Point.eq_some_xc_yc hP
  have hΨ : ((W⁄F).ΨSq n).eval P.xc = 0 := by
    have := Point.eval_psiSq_eq_zero_of_smul_eq_zero (W := (W⁄F)) (n := (n : ℤ))
      (Point.nonsingular_xc_yc hP) (by rw [← hPeq]; exact hnP)
    exact this
  refine ⟨hΨ, fun hΦ => ?_⟩
  obtain ⟨a, b, hab⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq (W⁄F) (n : ℤ)
  have := congrArg (Polynomial.eval P.xc) hab
  rw [eval_add, eval_mul, eval_mul, hΦ, hΨ, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

theorem restrictAlong_mulPull_of_torsion {n : ℕ} (hn : (n : F) ≠ 0) (hμ : (mulPull W F n).toRingHom.IsIntegral)
    (P : (W⁄F).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P = 0) :
    (placeOfPoint P).restrictAlong (mulPull W F n) hμ = placeOfPoint (0 : (W⁄F).Point) := by
  apply eq_placeOfPoint_zero_of_genericX_not_mem W
  change mulPull W F n (genericX W F) ∉ (placeOfPoint P).toValuationSubring
  rw [mem_placeOfPoint_iff W P hP, not_le]
  set v := (placeOf W F P hP).valuation (W⁄F).FunctionField with hv
  obtain ⟨hΨ0, hΦ0⟩ := eval_ΨSq_eq_zero_and_eval_Φ_ne_zero P hP hnP
  have hc1 := valuation_algebraMap_le_one W F P hP
  have hX := cong_genericX W F P hP

  have hΨc := (Valuation.Cong.eval₂ (v := v) (algebraMap F _) hc1 hX (hc1 _) ((W⁄F).ΨSq n)).1
  have hΦc := (Valuation.Cong.eval₂ (v := v) (algebraMap F _) hc1 hX (hc1 _) ((W⁄F).Φ n)).1
  rw [eval₂_at_apply, ← aeval_def] at hΨc hΦc
  rw [hΨ0, _root_.map_zero] at hΨc
  have hΨlt : v (aeval (genericX W F) ((W⁄F).ΨSq n)) < 1 := by
    have := hΨc; rwa [Valuation.cong_zero_iff] at this
  have hΦone : v (aeval (genericX W F) ((W⁄F).Φ n)) = 1 :=
    hΦc.eq_of_eq_one (valuation_algebraMap_eq_one W F P hP hΦ0)
  by_contra hle
  rw [not_lt] at hle
  have hrel := congrArg v (mulPull_genericX_mul_ΨSq_nat (W := W) hn)
  rw [map_mul, hΦone] at hrel
  have : v (mulPull W F n (genericX W F)) * v (aeval (genericX W F) ((W⁄F).ΨSq n)) < 1 :=
    calc v (mulPull W F n (genericX W F)) * v (aeval (genericX W F) ((W⁄F).ΨSq n))
        ≤ 1 * v (aeval (genericX W F) ((W⁄F).ΨSq n)) := mul_le_mul_left hle _
      _ = _ := one_mul _
      _ < 1 := hΨlt
  rw [hrel] at this
  exact lt_irrefl _ this

theorem restrictAlong_mulPull_zero {n : ℕ} (hn : (n : F) ≠ 0) (hμ : (mulPull W F n).toRingHom.IsIntegral) :
    (placeOfPoint (0 : (W⁄F).Point)).restrictAlong (mulPull W F n) hμ = placeOfPoint (0 : (W⁄F).Point) := by
  apply eq_placeOfPoint_zero_of_genericX_not_mem W
  change mulPull W F n (genericX W F) ∉ (placeOfPoint (0 : (W⁄F).Point)).toValuationSubring
  set O := (placeOfPoint (0 : (W⁄F).Point)).toValuationSubring with hO
  have hXO : genericX W F ∉ O :=
    algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero (W := W⁄F)
  have hX : 1 < O.valuation (genericX W F) := by
    rw [← not_le, O.valuation_le_one_iff]; exact hXO
  have hc : ∀ c : F, c ≠ 0 → O.valuation (algebraMap F (W⁄F).FunctionField c) = 1 := by
    intro c hc0
    apply le_antisymm
    · exact (O.valuation_le_one_iff _).mpr ((placeOfPoint (0 : (W⁄F).Point)).algebraMap_mem' c)
    · have h := (O.valuation_le_one_iff _).mpr ((placeOfPoint (0 : (W⁄F).Point)).algebraMap_mem' c⁻¹)
      rw [map_inv₀, map_inv₀, inv_le_one₀] at h
      · exact h
      · rw [Valuation.pos_iff]; exact (_root_.map_ne_zero _).mpr hc0
  haveI : (W⁄F).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hnz : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have hΦ := valuation_aeval_eq_pow O.valuation hc hX ((W⁄F).Φ n) (WeierstrassCurve.Φ_ne_zero _ _)
  have hΨ := valuation_aeval_eq_pow O.valuation hc hX ((W⁄F).ΨSq n) (WeierstrassCurve.ΨSq_ne_zero (W := W⁄F) hnz)
  rw [WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast] at hΦ
  rw [WeierstrassCurve.natDegree_ΨSq (W := W⁄F) hnz, Int.natAbs_natCast] at hΨ
  intro hmem
  have hle : O.valuation (mulPull W F n (genericX W F)) ≤ 1 := (O.valuation_le_one_iff _).mpr hmem
  have hrel := congrArg O.valuation (mulPull_genericX_mul_ΨSq_nat (W := W) hn)
  rw [map_mul, hΦ, hΨ] at hrel
  have hlt : O.valuation (genericX W F) ^ (n ^ 2 - 1) < O.valuation (genericX W F) ^ (n ^ 2) :=
    pow_lt_pow_right₀ hX (Nat.sub_one_lt_of_le (by positivity) le_rfl)
  have : O.valuation (genericX W F) ^ (n ^ 2) ≤ O.valuation (genericX W F) ^ (n ^ 2 - 1) := by
    rw [← hrel]
    calc O.valuation (mulPull W F n (genericX W F)) * O.valuation (genericX W F) ^ (n ^ 2 - 1)
        ≤ 1 * O.valuation (genericX W F) ^ (n ^ 2 - 1) := mul_le_mul_left hle _
      _ = _ := one_mul _
  exact absurd hlt (not_lt.mpr this)

theorem restrictAlong_mulPull {n : ℕ} (hn : (n : F) ≠ 0) (hμ : (mulPull W F n).toRingHom.IsIntegral)
    (P : (W⁄F).Point) :
    (placeOfPoint P).restrictAlong (mulPull W F n) hμ = placeOfPoint ((n : ℤ) • P) := by
  by_cases hP : P = 0
  · subst hP; rw [smul_zero]; exact restrictAlong_mulPull_zero hn hμ
  by_cases hnP : (n : ℤ) • P = 0
  · rw [hnP]; exact restrictAlong_mulPull_of_torsion hn hμ P hP hnP
  · exact restrictAlong_mulPull_of_ne hn hμ P hP hnP

end Seam

end S13MulDatum
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul.S13MulDatum"

open S13MulDatum in
theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    {n : ℕ} (hn : (n : F) ≠ 0) :
    ∃ D : IsogenyEndDatum W,
      (∀ P : W.Point, (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint ((n : ℤ) • P)) ∧
      finrankAlong F D.ι = n ^ 2 ∧ SeparableAlong F D.ι := by
  let Wc : WeierstrassCurve F := W
  letI hWe : Wc.IsElliptic := ‹W.IsElliptic›
  letI hG : GenusOnePlaceGate (Wc⁄F) := ‹GenusOnePlaceGate W›
  letI hC : GenusOnePlaceGate.IsCentred (Wc⁄F) := ‹GenusOnePlaceGate.IsCentred W›
  have hfin : FiniteAlong F (mulPull Wc F n) := finiteAlong_mulPull Wc hn
  have hint : (mulPull Wc F n).toRingHom.IsIntegral := isIntegral_of_finiteAlong _ hfin
  exact ⟨⟨mulPull Wc F n, hint, hfin⟩, fun P => restrictAlong_mulPull (W := Wc) hn hint P,
    finrankAlong_mulPull Wc hn, separableAlong_mulPull Wc hn⟩

end
end S_WeierstrassCurve_Affine_exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul (solution)
