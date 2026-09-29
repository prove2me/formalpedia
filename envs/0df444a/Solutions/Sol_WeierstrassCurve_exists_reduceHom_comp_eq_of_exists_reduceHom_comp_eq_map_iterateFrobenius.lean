-- Prove2me | solution 1 for WeierstrassCurve.exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/78c3b184-7d33-56d4-9f7a-1d383412db77

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "IsLocalRing WeierstrassCurve P2MW.S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate Pointwise

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine VariableChange.map map_map map Affine.Point.some reduction map_id toAffine Affine.Point map_Δ Δ VariableChange map_variableChange evalEvalBC rationalHomSet reduceHom Affine.Y_mem_of_X_mem reducePoint reducePoint_some_of_mem reducePoint_some_of_notMem Affine.vcXInv Affine.vcYInv Affine.Point.vcInvFun Affine.Point.vcInvFun_zero Affine.Point.equivOfVariableChangeEq ratPointMap_some ratPointHom ratPointHom_apply pointAddEquivOfEq pointAddEquivOfEq_some"
namespace UntwistLift
p2m_open "WeierstrassCurve"

section VC

variable {K : Type*} [Field K] [DecidableEq K]

theorem equivOfVariableChangeEq_symm_some_congr (v : VariableChange K) {V₁ V₂ W : WeierstrassCurve K}
    (h12 : V₁ = V₂) (h₁ : v • V₁ = W) (h₂ : v • V₂ = W) {x y : K}
    (hn₁ : V₁.toAffine.Nonsingular x y) (hn₂ : V₂.toAffine.Nonsingular x y) :
    (Affine.Point.equivOfVariableChangeEq (W := V₁) h₁).symm (.some x y hn₁) =
      (Affine.Point.equivOfVariableChangeEq (W := V₂) h₂).symm (.some x y hn₂) := by
  subst h12
  rfl

theorem equivOfVariableChangeEq_symm_zero (v : VariableChange K) {V W : WeierstrassCurve K}
    (h : v • V = W) :
    (Affine.Point.equivOfVariableChangeEq (W := V) h).symm 0 = 0 := by
  subst h
  rfl

end VC

section RatPoint

variable {F k : Type} [Field F] [Field k] [DecidableEq F] [DecidableEq k]

@[scoped simp] theorem ratPointHom_apply_zero (f : F →+* k) (W₀ : WeierstrassCurve F) :
    ratPointHom f (W₀ := W₀) 0 = 0 := rfl

theorem ratPointHom_apply_some (f : F →+* k) {W₀ : WeierstrassCurve F} {x y : F}
    (h : W₀.toAffine.Nonsingular x y) :
    ratPointHom f (W₀ := W₀) (.some x y h) =
      .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

end RatPoint

section Transport

variable {A A' : ValuationSubring (AlgebraicClosure ℚ)}
  (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ • A' = A)

local notation "ℚbar" => AlgebraicClosure ℚ

include hτ in
theorem mem_of_mem (x : ℚbar) (hx : x ∈ A') : τ x ∈ A := by
  have h := ValuationSubring.smul_mem_pointwise_smul τ x A' hx
  rwa [hτ, AlgEquiv.smul_def] at h

include hτ in
theorem mem_iff (x : ℚbar) : τ x ∈ A ↔ x ∈ A' := by
  refine ⟨fun h => ?_, mem_of_mem τ hτ x⟩
  have h' : τ • x ∈ τ • A' := by rwa [hτ, AlgEquiv.smul_def]
  exact ValuationSubring.smul_mem_pointwise_smul_iff.mp h'

include hτ in
theorem symm_mem_of_mem (y : ℚbar) (hy : y ∈ A) : τ.symm y ∈ A' := by
  rw [← mem_iff τ hτ]
  simpa using hy

def ringEquivOfSMulEq : A' ≃+* A where
  toFun x := ⟨τ x, mem_of_mem τ hτ x x.2⟩
  invFun y := ⟨τ.symm y, symm_mem_of_mem τ hτ y y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_ringEquivOfSMulEq_apply (x : A') :
    ((ringEquivOfSMulEq τ hτ x : A) : ℚbar) = τ x := rfl

variable (E : WeierstrassCurve A')

def twist : WeierstrassCurve A := E.map (ringEquivOfSMulEq τ hτ).toRingHom

theorem twist_map_subtype :
    (twist τ hτ E).map A.subtype = (E.map A'.subtype).map (τ : ℚbar →+* ℚbar) := by
  simp only [twist, WeierstrassCurve.map_map]
  congr 1

theorem map_symm_twist_map_subtype :
    ((twist τ hτ E).map A.subtype).map (τ.symm : ℚbar →+* ℚbar) = E.map A'.subtype := by
  rw [twist_map_subtype, WeierstrassCurve.map_map]
  have : ((τ.symm : ℚbar →+* ℚbar).comp (τ : ℚbar →+* ℚbar)) = RingHom.id _ := by
    ext x; simp
  rw [this, WeierstrassCurve.map_map]
  rfl

variable (e : ResidueField A' ≃+* ResidueField A)
  (hres : ∀ x : A', residue A (ringEquivOfSMulEq τ hτ x) = e (residue A' x))

include hres in

theorem twist_map_residue :
    (twist τ hτ E).map (residue A) = (E.map (residue A')).map e.toRingHom := by
  simp only [twist, WeierstrassCurve.map_map]
  congr 1
  ext x
  exact hres x

include hres in
theorem twist_Δ_ne_zero (hΔ : (E.map (residue A')).Δ ≠ 0) :
    ((twist τ hτ E).map (residue A)).Δ ≠ 0 := by
  rw [twist_map_residue τ hτ E e hres, WeierstrassCurve.map_Δ]
  simpa using hΔ

variable [DecidableEq ℚbar]

def T : (E.map A'.subtype).toAffine.Point →+ ((twist τ hτ E).map A.subtype).toAffine.Point :=
  (pointAddEquivOfEq (twist_map_subtype τ hτ E).symm).toAddMonoidHom.comp
    (ratPointHom (τ : ℚbar →+* ℚbar))

def T' : ((twist τ hτ E).map A.subtype).toAffine.Point →+ (E.map A'.subtype).toAffine.Point :=
  (pointAddEquivOfEq (map_symm_twist_map_subtype τ hτ E)).toAddMonoidHom.comp
    (ratPointHom (τ.symm : ℚbar →+* ℚbar))

theorem T_zero : T τ hτ E 0 = 0 := map_zero _

private theorem some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem T_some {x y : ℚbar} (h : (E.map A'.subtype).toAffine.Nonsingular x y) :
    ∃ h', T τ hτ E (.some x y h) = .some (τ x) (τ y) h' := by
  have h1 : ((twist τ hτ E).map A.subtype).toAffine.Nonsingular (τ x) (τ y) := by
    rw [twist_map_subtype]
    exact ((E.map A'.subtype).toAffine.map_nonsingular (τ : ℚbar →+* ℚbar).injective x y).mpr h
  refine ⟨h1, ?_⟩
  simp only [T, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ratPointHom_apply_some]
  rw [pointAddEquivOfEq_some]
  exact some_congr rfl rfl _ _

theorem T'_some {x y : ℚbar} (h : ((twist τ hτ E).map A.subtype).toAffine.Nonsingular x y) :
    ∃ h', T' τ hτ E (.some x y h) = .some (τ.symm x) (τ.symm y) h' := by
  have h1 : (E.map A'.subtype).toAffine.Nonsingular (τ.symm x) (τ.symm y) := by
    rw [← map_symm_twist_map_subtype τ hτ E]
    exact (((twist τ hτ E).map A.subtype).toAffine.map_nonsingular
      (τ.symm : ℚbar →+* ℚbar).injective x y).mpr h
  refine ⟨h1, ?_⟩
  simp only [T', AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ratPointHom_apply_some]
  rw [pointAddEquivOfEq_some]
  exact some_congr rfl rfl _ _

theorem T_T' (P : ((twist τ hτ E).map A.subtype).toAffine.Point) : T τ hτ E (T' τ hτ E P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · show T τ hτ E (T' τ hτ E 0) = 0
    rw [map_zero, map_zero]
  · obtain ⟨h', e'⟩ := T'_some τ hτ E h
    rw [e']
    obtain ⟨h'', e''⟩ := T_some τ hτ E h'
    rw [e'']
    exact some_congr (by simp) (by simp) _ _

theorem T'_T (P : (E.map A'.subtype).toAffine.Point) : T' τ hτ E (T τ hτ E P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · show T' τ hτ E (T τ hτ E 0) = 0
    rw [map_zero, map_zero]
  · obtain ⟨h', e'⟩ := T_some τ hτ E h
    rw [e']
    obtain ⟨h'', e''⟩ := T'_some τ hτ E h'
    rw [e'']
    exact some_congr (by simp) (by simp) _ _

theorem T_surjective : Function.Surjective (T τ hτ E) :=
  fun P => ⟨T' τ hτ E P, T_T' τ hτ E P⟩

def conj (α : (E.map A'.subtype).toAffine.Point →+ (E.map A'.subtype).toAffine.Point) :
    ((twist τ hτ E).map A.subtype).toAffine.Point →+ ((twist τ hτ E).map A.subtype).toAffine.Point :=
  (T τ hτ E).comp (α.comp (T' τ hτ E))

theorem conj_apply_T (α : (E.map A'.subtype).toAffine.Point →+ (E.map A'.subtype).toAffine.Point)
    (P : (E.map A'.subtype).toAffine.Point) :
    conj τ hτ E α (T τ hτ E P) = T τ hτ E (α P) := by
  simp [conj, T'_T]

omit hτ in

theorem evalEvalBC_self (p : ℚbar[X][Y]) (x y : ℚbar) :
    evalEvalBC ℚbar p x y = p.evalEval x y := by
  simp only [evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]

omit hτ in
theorem evalEvalBC_map (p : ℚbar[X][Y]) (x y : ℚbar) :
    evalEvalBC ℚbar (p.map (mapRingHom (τ : ℚbar →+* ℚbar))) (τ x) (τ y) =
      τ (evalEvalBC ℚbar p x y) := by
  rw [evalEvalBC_self, evalEvalBC_self]
  exact Polynomial.map_mapRingHom_evalEval (τ : ℚbar →+* ℚbar) p x y

theorem conj_mem_rationalHomSet
    {α : (E.map A'.subtype).toAffine.Point →+ (E.map A'.subtype).toAffine.Point}
    (hα : α ∈ rationalHomSet ℚbar (E.map A'.subtype) (E.map A'.subtype)) :
    conj τ hτ E α ∈ rationalHomSet ℚbar ((twist τ hτ E).map A.subtype) ((twist τ hτ E).map A.subtype) := by
  rcases hα with hα | ⟨nX, dX, nY, dY, B, hB, H⟩
  · left
    subst hα
    ext P
    show T τ hτ E 0 = 0
    exact map_zero _
  right
  refine ⟨nX.map (mapRingHom (τ : ℚbar →+* ℚbar)), dX.map (mapRingHom (τ : ℚbar →+* ℚbar)),
    nY.map (mapRingHom (τ : ℚbar →+* ℚbar)), dY.map (mapRingHom (τ : ℚbar →+* ℚbar)),
    τ '' B, hB.image _, ?_⟩
  intro x' y' h' hx'

  obtain ⟨h, hT'⟩ := T'_some τ hτ E (x := x') (y := y') h'
  obtain ⟨x, hx⟩ : ∃ x, x = τ.symm x' := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = τ.symm y' := ⟨_, rfl⟩
  subst hx hy
  have hxx : τ (τ.symm x') = x' := by simp
  have hyy : τ (τ.symm y') = y' := by simp
  have hxB : τ.symm x' ∉ B := by
    intro hmem
    exact hx' ⟨τ.symm x', hmem, hxx⟩
  obtain ⟨hdX, hdY, h'', hαP⟩ := H (τ.symm x') (τ.symm y') h hxB
  have key0 : conj τ hτ E α (.some x' y' h') = T τ hτ E (α (.some (τ.symm x') (τ.symm y') h)) := by
    simp only [conj, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hT']
  obtain ⟨h3, hT⟩ := T_some τ hτ E h''
  have key : conj τ hτ E α (.some x' y' h') = _ := (key0.trans (congrArg (T τ hτ E) hαP)).trans hT
  have edX : evalEvalBC ℚbar (dX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' = τ (evalEvalBC ℚbar dX (τ.symm x') (τ.symm y')) := by
    have hh := evalEvalBC_map τ dX (τ.symm x') (τ.symm y')
    rwa [hxx, hyy] at hh
  have edY : evalEvalBC ℚbar (dY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' = τ (evalEvalBC ℚbar dY (τ.symm x') (τ.symm y')) := by
    have hh := evalEvalBC_map τ dY (τ.symm x') (τ.symm y')
    rwa [hxx, hyy] at hh
  have enX : evalEvalBC ℚbar (nX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' = τ (evalEvalBC ℚbar nX (τ.symm x') (τ.symm y')) := by
    have hh := evalEvalBC_map τ nX (τ.symm x') (τ.symm y')
    rwa [hxx, hyy] at hh
  have enY : evalEvalBC ℚbar (nY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' = τ (evalEvalBC ℚbar nY (τ.symm x') (τ.symm y')) := by
    have hh := evalEvalBC_map τ nY (τ.symm x') (τ.symm y')
    rwa [hxx, hyy] at hh
  refine ⟨by rw [edX]; simpa using hdX, by rw [edY]; simpa using hdY, ?_⟩
  have hcoordX : τ (evalEvalBC ℚbar nX (τ.symm x') (τ.symm y') / evalEvalBC ℚbar dX (τ.symm x') (τ.symm y')) =
      evalEvalBC ℚbar (nX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' / evalEvalBC ℚbar (dX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' := by
    rw [map_div₀, enX, edX]
  have hcoordY : τ (evalEvalBC ℚbar nY (τ.symm x') (τ.symm y') / evalEvalBC ℚbar dY (τ.symm x') (τ.symm y')) =
      evalEvalBC ℚbar (nY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' / evalEvalBC ℚbar (dY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' := by
    rw [map_div₀, enY, edY]
  have h4 : ((twist τ hτ E).map A.subtype).toAffine.Nonsingular
      (evalEvalBC ℚbar (nX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' / evalEvalBC ℚbar (dX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y')
      (evalEvalBC ℚbar (nY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' / evalEvalBC ℚbar (dY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y') := by
    rw [← hcoordX, ← hcoordY]; exact h3
  refine ⟨h4, key.trans ?_⟩
  exact some_congr hcoordX hcoordY _ _

variable [DecidableEq (ResidueField A)] [DecidableEq (ResidueField A')]

include hres in

theorem reduce_T {W : WeierstrassCurve (ResidueField A)} (v : VariableChange (ResidueField A))
    (hΔ : (E.map (residue A')).Δ ≠ 0)
    (hΔ' : ((twist τ hτ E).map (residue A)).Δ ≠ 0)
    (hv : v • (E.map (residue A')).map e.toRingHom = W)
    (hv' : v • (twist τ hτ E).map (residue A) = W)
    (Q : (E.map A'.subtype).toAffine.Point) :
    (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (T τ hτ E Q)) =
      (Affine.Point.equivOfVariableChangeEq hv).symm (ratPointHom e.toRingHom (reduceHom hΔ Q)) := by
  have hcurve := twist_map_residue τ hτ E e hres
  rcases Q with _ | ⟨x, y, h⟩
  · show (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (T τ hτ E 0)) =
      (Affine.Point.equivOfVariableChangeEq hv).symm (ratPointHom e.toRingHom (reduceHom hΔ 0))
    rw [T_zero, map_zero (reduceHom hΔ'), map_zero (reduceHom hΔ), map_zero (ratPointHom e.toRingHom),
      equivOfVariableChangeEq_symm_zero, equivOfVariableChangeEq_symm_zero]
  · obtain ⟨h', hT⟩ := T_some τ hτ E h
    rw [hT]
    have e1 : reduceHom hΔ' (.some (τ x) (τ y) h') = reducePoint hΔ' (.some (τ x) (τ y) h') := rfl
    have e2 : reduceHom hΔ (.some x y h) = reducePoint hΔ (.some x y h) := rfl
    rw [e1, e2]
    by_cases hx : x ∈ A'
    · have hτx : τ x ∈ A := mem_of_mem τ hτ x hx
      rw [reducePoint_some_of_mem hΔ' h' hτx, reducePoint_some_of_mem hΔ h hx, ratPointHom_apply_some]
      have hy : y ∈ A' := Affine.Y_mem_of_X_mem E h.1 hx
      have hτy : τ y ∈ A := mem_of_mem τ hτ y hy
      have ex : residue A ⟨τ x, hτx⟩ = e.toRingHom (residue A' ⟨x, hx⟩) := hres ⟨x, hx⟩
      have ey : residue A ⟨τ y, hτy⟩ = e.toRingHom (residue A' ⟨y, hy⟩) := hres ⟨y, hy⟩
      have step : ∀ (a b : ResidueField A)
          (h₁ : ((twist τ hτ E).map (residue A)).toAffine.Nonsingular a b)
          (a' b' : ResidueField A) (ha : a = a') (hb : b = b')
          (h₂ : ((E.map (residue A')).map e.toRingHom).toAffine.Nonsingular a' b'),
          (Affine.Point.equivOfVariableChangeEq hv').symm (.some a b h₁) =
            (Affine.Point.equivOfVariableChangeEq hv).symm (.some a' b' h₂) := by
        intro a b h₁ a' b' ha hb h₂
        subst ha hb
        exact equivOfVariableChangeEq_symm_some_congr v hcurve hv' hv h₁ h₂
      exact step _ _ _ _ _ ex ey _
    · have hτx : τ x ∉ A := fun hmem => hx ((mem_iff τ hτ x).mp hmem)
      rw [reducePoint_some_of_notMem hΔ' h' hτx, reducePoint_some_of_notMem hΔ h hx,
        map_zero (ratPointHom e.toRingHom), equivOfVariableChangeEq_symm_zero,
        equivOfVariableChangeEq_symm_zero]

end Transport

section FrobPoints

variable {F k : Type} [Field F] [Field k] [DecidableEq F] [DecidableEq k]

private theorem some_congr' {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem equivOfVariableChangeEq_symm_ratPointHom (f : F →+* k) (C : VariableChange F)
    {X V : WeierstrassCurve F} {V' : WeierstrassCurve k} (h : C • X = V)
    (h' : C.map f • X.map f = V') (hVV' : V.map f = V') (R : X.toAffine.Point) :
    (Affine.Point.equivOfVariableChangeEq h').symm (ratPointHom f R) =
      pointAddEquivOfEq hVV' (ratPointHom f ((Affine.Point.equivOfVariableChangeEq h).symm R)) := by
  subst h h'
  rcases R with _ | ⟨x, y, hR⟩
  · show Affine.Point.vcInvFun (C.map f) (X.map f) (ratPointHom f 0) =
      pointAddEquivOfEq hVV' (ratPointHom f (Affine.Point.vcInvFun C X 0))
    rw [Affine.Point.vcInvFun_zero, map_zero, map_zero, map_zero, Affine.Point.vcInvFun_zero]
  · show Affine.Point.vcInvFun (C.map f) (X.map f)
        (.some (f x) (f y) ((X.toAffine.map_nonsingular f.injective x y).mpr hR)) =
      pointAddEquivOfEq hVV' (ratPointHom f (Affine.Point.vcInvFun C X (.some x y hR)))
    simp only [Affine.Point.vcInvFun, ratPointHom_apply, ratPointMap_some]
    rw [pointAddEquivOfEq_some]
    refine some_congr' ?_ ?_ _ _
    · simp [Affine.vcXInv, VariableChange.map]
    · simp [Affine.vcYInv, VariableChange.map]

end FrobPoints

section Main

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (ResidueField A)] [CharP (ResidueField A) p]
  (n : ℕ)

local notation "ℚbar" => AlgebraicClosure ℚ

theorem main (W : WeierstrassCurve (ResidueField A)) [W.IsElliptic]
    (β : W.toAffine.Point →+ W.toAffine.Point)
    {β' : (W.map (iterateFrobenius (ResidueField A) p n)).toAffine.Point →+
      (W.map (iterateFrobenius (ResidueField A) p n)).toAffine.Point}
    (hβ' : β'.comp (ratPointHom (iterateFrobenius (ResidueField A) p n)) =
      (ratPointHom (iterateFrobenius (ResidueField A) p n)).comp β)
    (hlift : ∃ (E' : WeierstrassCurve A) (hΔ' : (E'.map (residue A)).Δ ≠ 0)
      (v' : VariableChange (ResidueField A))
      (hv' : v' • E'.map (residue A) = W.map (iterateFrobenius (ResidueField A) p n)),
      ∃ α' ∈ rationalHomSet ℚbar (E'.map A.subtype) (E'.map A.subtype),
        ∀ P : (E'.map A.subtype).toAffine.Point,
          (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (α' P)) =
            β' ((Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' P))) :
    ∃ (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) (v : VariableChange (ResidueField A))
      (hv : v • E.map (residue A) = W),
      ∃ α ∈ rationalHomSet ℚbar (E.map A.subtype) (E.map A.subtype),
        ∀ P : (E.map A.subtype).toAffine.Point,
          (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ (α P)) =
            β ((Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ P)) := by
  obtain ⟨E', hΔ', v', hv', α'₀, hα'₀, hcompat'₀⟩ := hlift
  obtain ⟨α', hα', hcompat'⟩ :
      ∃ α' : (E'.map A.subtype).toAffine.Point →+ (E'.map A.subtype).toAffine.Point,
        α' ∈ rationalHomSet ℚbar (E'.map A.subtype) (E'.map A.subtype) ∧
          ∀ P : (E'.map A.subtype).toAffine.Point,
            (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (α' P)) =
              β' ((Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' P)) :=
    ⟨α'₀, hα'₀, hcompat'₀⟩
  haveI : IsAlgClosed (ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  set e₀ : ResidueField A ≃+* ResidueField A := iterateFrobeniusEquiv (ResidueField A) p n with he₀
  have he₀σ : ∀ x, e₀ x = iterateFrobenius (ResidueField A) p n x := fun x => by
    rw [he₀, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  set e : ResidueField A ≃+* ResidueField A := e₀.symm with he
  have heσ : ∀ x, e (iterateFrobenius (ResidueField A) p n x) = x := fun x => by
    rw [← he₀σ, he]; exact e₀.symm_apply_apply x
  have hσe : ∀ x, iterateFrobenius (ResidueField A) p n (e x) = x := fun x => by
    rw [← he₀σ, he]; exact e₀.apply_symm_apply x
  have hcomp : e.toRingHom.comp (iterateFrobenius (ResidueField A) p n) = RingHom.id _ :=
    RingHom.ext heσ

  obtain ⟨τ, hτ, hτres⟩ :=
    ValuationSubring.exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField p A A e
  have hres : ∀ x : A, residue A (ringEquivOfSMulEq τ hτ x) = e (residue A x) :=
    fun x => hτres x (ringEquivOfSMulEq τ hτ x) rfl

  have hΔ : ((twist τ hτ E').map (residue A)).Δ ≠ 0 := twist_Δ_ne_zero τ hτ E' e hres hΔ'
  have hWid : (W.map (iterateFrobenius (ResidueField A) p n)).map e.toRingHom = W := by
    rw [WeierstrassCurve.map_map, hcomp, WeierstrassCurve.map_id]
  have hv₁ : v'.map e.toRingHom • (E'.map (residue A)).map e.toRingHom = W := by
    rw [WeierstrassCurve.map_variableChange, hv', hWid]
  have hv₂ : v'.map e.toRingHom • (twist τ hτ E').map (residue A) = W := by
    rw [twist_map_residue τ hτ E' e hres]; exact hv₁
  refine ⟨twist τ hτ E', hΔ, v'.map e.toRingHom, hv₂, conj τ hτ E' α',
    conj_mem_rationalHomSet τ hτ E' hα', fun P => ?_⟩

  set G : (W.map (iterateFrobenius (ResidueField A) p n)).toAffine.Point →+ W.toAffine.Point :=
    (pointAddEquivOfEq hWid).toAddMonoidHom.comp (ratPointHom e.toRingHom) with hG
  have hGF : ∀ X : W.toAffine.Point, G (ratPointHom (iterateFrobenius (ResidueField A) p n) X) = X := by
    rintro (_ | ⟨x, y, hX⟩)
    · show G (ratPointHom (iterateFrobenius (ResidueField A) p n) 0) = 0
      rw [map_zero, map_zero]
    · simp only [hG, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
        ratPointHom_apply, ratPointMap_some]
      rw [pointAddEquivOfEq_some]
      exact some_congr (heσ x) (heσ y) _ _
  have hFG : ∀ Y₁ : (W.map (iterateFrobenius (ResidueField A) p n)).toAffine.Point,
      ratPointHom (iterateFrobenius (ResidueField A) p n) (G Y₁) = Y₁ := by
    rintro (_ | ⟨x, y, hY⟩)
    · show ratPointHom (iterateFrobenius (ResidueField A) p n) (G 0) = 0
      rw [map_zero, map_zero]
    · simp only [hG, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
        ratPointHom_apply, ratPointMap_some]
      rw [pointAddEquivOfEq_some, ratPointMap_some]
      exact some_congr (hσe x) (hσe y) _ _
  have hGβ : ∀ Y₁, G (β' Y₁) = β (G Y₁) := fun Y₁ => by
    have h1 := DFunLike.congr_fun hβ' (G Y₁)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, hFG] at h1
    rw [h1, hGF]

  obtain ⟨Q, rfl⟩ := T_surjective τ hτ E' P
  have goal' : (Affine.Point.equivOfVariableChangeEq hv₂).symm
      (reduceHom hΔ (conj τ hτ E' α' (T τ hτ E' Q))) =
      β ((Affine.Point.equivOfVariableChangeEq hv₂).symm (reduceHom hΔ (T τ hτ E' Q))) := by
    rw [conj_apply_T, reduce_T τ hτ E' e hres (v'.map e.toRingHom) hΔ' hΔ hv₁ hv₂ (α' Q),
      reduce_T τ hτ E' e hres (v'.map e.toRingHom) hΔ' hΔ hv₁ hv₂ Q,
      equivOfVariableChangeEq_symm_ratPointHom e.toRingHom v' hv' hv₁ hWid,
      equivOfVariableChangeEq_symm_ratPointHom e.toRingHom v' hv' hv₁ hWid, hcompat' Q]
    exact hGβ _
  exact goal'

end Main

end WeierstrassCurve.UntwistLift
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius.WeierstrassCurve.UntwistLift"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius.WeierstrassCurve.UntwistLift"

open IsLocalRing in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p] (n : ℕ) (W : WeierstrassCurve (IsLocalRing.ResidueField A)) [W.IsElliptic] (β : W.toAffine.Point →+ W.toAffine.Point) {β' : (W.map (iterateFrobenius (IsLocalRing.ResidueField A) p n)).toAffine.Point →+ (W.map (iterateFrobenius (IsLocalRing.ResidueField A) p n)).toAffine.Point} (hβ' : β'.comp (WeierstrassCurve.ratPointHom (iterateFrobenius (IsLocalRing.ResidueField A) p n)) = (WeierstrassCurve.ratPointHom (iterateFrobenius (IsLocalRing.ResidueField A) p n)).comp β) (hlift : ∃ (E' : WeierstrassCurve A) (hΔ' : (E'.map (IsLocalRing.residue A)).Δ ≠ 0) (v' : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv' : v' • E'.map (IsLocalRing.residue A) = W.map (iterateFrobenius (IsLocalRing.ResidueField A) p n)), ∃ α' ∈ WeierstrassCurve.rationalHomSet (AlgebraicClosure ℚ) (E'.map A.subtype) (E'.map A.subtype), ∀ P : (E'.map A.subtype).toAffine.Point, (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm (WeierstrassCurve.reduceHom hΔ' (α' P)) = β' ((WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm (WeierstrassCurve.reduceHom hΔ' P))) : ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv : v • E.map (IsLocalRing.residue A) = W), ∃ α ∈ WeierstrassCurve.rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype), ∀ P : (E.map A.subtype).toAffine.Point, (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ (α P)) = β ((WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ P)) :=
  WeierstrassCurve.UntwistLift.main p A n W β hβ' hlift

end S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius
end P2MW
export P2MW.S_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius (solution)
