-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_heq_vcInvFun_iff_exists_dualPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c5acdaaf-bfa7-58f8-9200-3b07547575ea

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_nsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair.WeierstrassCurve WeierstrassCurve.Affine"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map Affine.Point.some map_id toAffine Affine.Point VariableChange baseChange evalEvalBC rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet Affine.vcX Affine.vcY Affine.vcXInv Affine.vcYInv Affine.vcX_vcXInv Affine.vcY_vcYInv Affine.nonsingular_variableChange_iff Affine.Point.vcInvFun exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet exists_nsmul_eq_of_isAlgClosed"
namespace VeluUniversalLevel
p2m_open "WeierstrassCurve"

section VC

variable {κ : Type*} [Field κ] [DecidableEq κ]

open Polynomial
open scoped Polynomial.Bivariate

theorem some_eq_some {V : WeierstrassCurve.Affine κ} {x₁ y₁ x₂ y₂ : κ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem heq_equivOfVariableChangeEq_symm (γ : VariableChange κ) (W : WeierstrassCurve.Affine κ)
    {V : WeierstrassCurve.Affine κ} (h : γ • W = V) (T : W.Point) :
    HEq ((Point.equivOfVariableChangeEq h).symm T) (Point.vcInvFun γ W T) := by
  subst h; rfl

theorem equivOfVariableChangeEq_symm_add (γ : VariableChange κ) (W : WeierstrassCurve.Affine κ)
    {V : WeierstrassCurve.Affine κ} (h : γ • W = V) (T₁ T₂ : W.Point) :
    (Point.equivOfVariableChangeEq h).symm (T₁ + T₂) =
      (Point.equivOfVariableChangeEq h).symm T₁ + (Point.equivOfVariableChangeEq h).symm T₂ := by
  subst h
  exact Point.vcInvFun_add γ W T₁ T₂

def vcMap {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E') :
    E.toAffine.Point ≃+ E'.toAffine.Point :=
  AddEquiv.mk' (Point.equivOfVariableChangeEq (W := E.toAffine) (V := E'.toAffine) h).symm
    (equivOfVariableChangeEq_symm_add γ E.toAffine h)

theorem vcMap_apply {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E') (T : E.toAffine.Point) :
    vcMap h T = (Point.equivOfVariableChangeEq (W := E.toAffine) (V := E'.toAffine) h).symm T := rfl

theorem heq_vcMap {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E') (T : E.toAffine.Point) :
    HEq (vcMap h T) (Point.vcInvFun γ E.toAffine T) :=
  heq_equivOfVariableChangeEq_symm γ E.toAffine h T

theorem forall_heq_iff {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E')
    (A : Set E.toAffine.Point) (B : Set E'.toAffine.Point) :
    (∀ T ∈ A, ∃ T' ∈ B, HEq (Point.vcInvFun γ E.toAffine T) T') ↔ ∀ T ∈ A, vcMap h T ∈ B := by
  subst h
  constructor
  · intro H T hT
    obtain ⟨T', hT', hh⟩ := H T hT
    have : vcMap (rfl : γ • E = γ • E) T = T' := eq_of_heq ((heq_vcMap rfl T).trans hh)
    rw [this]; exact hT'
  · intro H T hT
    exact ⟨_, H T hT, (heq_vcMap rfl T).symm⟩

theorem evalEvalBC_self (p : κ[X][Y]) (x y : κ) : evalEvalBC κ p x y = p.evalEval x y := by
  simp [evalEvalBC, Polynomial.map_id, Algebra.algebraMap_self]

theorem vcMap_mem_rationalHomSet {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E') :
    ((vcMap h).toAddMonoidHom : (E.baseChange κ).toAffine.Point →+ (E'.baseChange κ).toAffine.Point) ∈
        rationalHomSet κ E E' ∧
      ((vcMap h).symm.toAddMonoidHom : (E'.baseChange κ).toAffine.Point →+ (E.baseChange κ).toAffine.Point) ∈
        rationalHomSet κ E' E := by
  subst h
  have e1 : ∀ x y : κ, evalEvalBC κ (1 : κ[X][Y]) x y = 1 := fun x y => by
    rw [evalEvalBC_self]; simp only [evalEval_one]
  refine ⟨Or.inr ?_, Or.inr ?_⟩
  ·
    refine ⟨C (C (((γ.u⁻¹ : κˣ) : κ) ^ 2) * (X - C γ.r)), 1,
      C (C (((γ.u⁻¹ : κˣ) : κ) ^ 3)) * (Polynomial.X - C (C γ.t) - C (C γ.s * (X - C γ.r))), 1,
      ∅, Set.finite_empty, fun x y hxy _ => ?_⟩
    have ex : evalEvalBC κ (C (C (((γ.u⁻¹ : κˣ) : κ) ^ 2) * (X - C γ.r)) : κ[X][Y]) x y / evalEvalBC κ (1 : κ[X][Y]) x y =
        Affine.vcXInv γ x := by
      rw [e1, div_one, evalEvalBC_self, Affine.vcXInv]
      simp only [evalEval_C, eval_C, eval_X, eval_mul, eval_sub]
    have ey : evalEvalBC κ (C (C (((γ.u⁻¹ : κˣ) : κ) ^ 3)) * (Polynomial.X - C (C γ.t) - C (C γ.s * (X - C γ.r))) :
          κ[X][Y]) x y / evalEvalBC κ (1 : κ[X][Y]) x y = Affine.vcYInv γ x y := by
      rw [e1, div_one, evalEvalBC_self, Affine.vcYInv]
      simp only [evalEval_C, evalEval_X, evalEval_mul, evalEval_sub, eval_C, eval_X, eval_mul, eval_sub]
    have hns : (γ • E).toAffine.Nonsingular (Affine.vcXInv γ x) (Affine.vcYInv γ x y) :=
      (Affine.nonsingular_variableChange_iff _ _).mpr (by rwa [Affine.vcX_vcXInv, Affine.vcY_vcYInv])
    refine ⟨by rw [e1]; exact one_ne_zero, by rw [e1]; exact one_ne_zero, (by rw [ex, ey]; exact hns), ?_⟩
    show Point.vcInvFun γ E.toAffine (Affine.Point.some x y hxy) = _
    exact some_eq_some ex.symm ey.symm
  ·
    refine ⟨C (C (((γ.u : κˣ) : κ) ^ 2) * X + C γ.r), 1,
      C (C (((γ.u : κˣ) : κ) ^ 3)) * Polynomial.X + C (C (((γ.u : κˣ) : κ) ^ 2 * γ.s) * X + C γ.t), 1,
      ∅, Set.finite_empty, fun x' y' h' _ => ?_⟩
    have ex : evalEvalBC κ (C (C (((γ.u : κˣ) : κ) ^ 2) * X + C γ.r) : κ[X][Y]) x' y' / evalEvalBC κ (1 : κ[X][Y]) x' y' =
        Affine.vcX γ x' := by
      rw [e1, div_one, evalEvalBC_self, Affine.vcX]
      simp only [evalEval_C, eval_C, eval_X, eval_mul, eval_add]
    have ey : evalEvalBC κ (C (C (((γ.u : κˣ) : κ) ^ 3)) * Polynomial.X + C (C (((γ.u : κˣ) : κ) ^ 2 * γ.s) * X + C γ.t) :
          κ[X][Y]) x' y' / evalEvalBC κ (1 : κ[X][Y]) x' y' = Affine.vcY γ x' y' := by
      rw [e1, div_one, evalEvalBC_self, Affine.vcY]
      simp only [evalEval_C, evalEval_X, evalEval_mul, evalEval_add, eval_C, eval_X, eval_mul, eval_add]
      ring
    refine ⟨by rw [e1]; exact one_ne_zero, by rw [e1]; exact one_ne_zero,
      (by rw [ex, ey]; exact (Affine.nonsingular_variableChange_iff x' y').mp h'), ?_⟩
    show Point.vcFun γ E.toAffine (Affine.Point.some x' y' h') = _
    exact some_eq_some ex.symm ey.symm

end VC

section Isogeny

variable {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem nsmul_id_mem_rationalHomSet (W : WeierstrassCurve κ) [W.IsElliptic] (n : ℕ) :
    (n • AddMonoidHom.id _ : (W.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point) ∈
      rationalHomSet κ W W := by
  induction n with
  | zero => rw [zero_nsmul]; exact zero_mem_rationalHomSet κ W W
  | succ n ih => rw [succ_nsmul]; exact add_mem_rationalHomSet κ W W ih (id_mem_rationalHomSet κ W)

theorem surjective_and_exists_dual_of_universal (E A : WeierstrassCurve κ) [E.IsElliptic] [A.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point) (hφ : φ ∈ rationalHomSet κ E A)
    (hker : φ.ker = AddSubgroup.zmultiples Q)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
      (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ rationalHomSet κ E V → α Q = 0 → ∃ β ∈ rationalHomSet κ A V, α = β.comp φ) :
    Function.Surjective φ ∧
      ∃ φ' ∈ rationalHomSet κ A E, φ'.comp φ = ℓ • AddMonoidHom.id _ ∧ φ.comp φ' = ℓ • AddMonoidHom.id _ := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hQ
    exact hℓ.one_lt.ne hQ
  have hℓQ : ℓ • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hφ0 : φ ≠ 0 := by
    intro h0
    obtain ⟨T₀, hT₀⟩ := exists_nsmul_eq_of_isAlgClosed E ℓ hℓ0 Q
    let T : (E.baseChange κ).toAffine.Point := T₀
    have hT : ℓ • T = Q := hT₀
    have hTker : T ∈ φ.ker := by rw [h0]; trivial
    rw [hker] at hTker
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hTker
    apply hQ0
    have hkQ : ℓ • (k • Q) = 0 := by rw [smul_comm, hℓQ, smul_zero]
    have hk' : (k • Q : (E.baseChange κ).toAffine.Point) = T := hk
    rw [← hT]
    show ℓ • T = 0
    rw [← hk']
    exact hkQ
  have hsurj : Function.Surjective φ := surjective_of_mem_rationalHomSet κ hφ hφ0
  have hℓQ' : (ℓ • AddMonoidHom.id (E.baseChange κ).toAffine.Point) Q = 0 := hℓQ
  obtain ⟨φ', hφ', hcomp⟩ := huniv E (ℓ • AddMonoidHom.id _) (nsmul_id_mem_rationalHomSet E ℓ) hℓQ'
  refine ⟨hsurj, φ', hφ', hcomp.symm, ?_⟩
  have L : ∀ R : (E.baseChange κ).toAffine.Point, φ' (φ R) = ℓ • R := fun R => (DFunLike.congr_fun hcomp R).symm
  ext P
  obtain ⟨R, rfl⟩ := hsurj P
  show φ (φ' (φ R)) = ℓ • φ R
  rw [L, map_nsmul]

theorem exists_variableChange_iff_exists_dualPair (E A E' : WeierstrassCurve κ) [E.IsElliptic] [A.IsElliptic]
    [E'.IsElliptic] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point) (hφ : φ ∈ rationalHomSet κ E A)
    (hker : φ.ker = AddSubgroup.zmultiples Q)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
      (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ rationalHomSet κ E V → α Q = 0 → ∃ β ∈ rationalHomSet κ A V, α = β.comp φ)
    (C : Set E.toAffine.Point) (C' : Set E'.toAffine.Point) :
    (∃ γ : VariableChange κ, γ • A = E' ∧
        ∀ T ∈ C, ∃ T' ∈ C', HEq (Point.vcInvFun γ A.toAffine (φ T)) T') ↔
      ∃ ψ ∈ rationalHomSet κ E E', ∃ ψ' ∈ rationalHomSet κ E' E,
        ψ.ker = AddSubgroup.zmultiples Q ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
        ∀ T ∈ C, ψ T ∈ C' := by
  obtain ⟨hsurj, φ', hφ', h1, h2⟩ := surjective_and_exists_dual_of_universal E A hℓ hℓ0 Q hQ φ hφ hker huniv
  have L1 : ∀ R : (E.baseChange κ).toAffine.Point, φ' (φ R) = ℓ • R := fun R => DFunLike.congr_fun h1 R
  have L2 : ∀ P : (A.baseChange κ).toAffine.Point, φ (φ' P) = ℓ • P := fun P => DFunLike.congr_fun h2 P
  constructor
  · rintro ⟨γ, hγ, hC⟩
    subst hγ
    have hγ0 : γ • A = γ • A := rfl
    obtain ⟨he, hes⟩ := vcMap_mem_rationalHomSet hγ0
    let eb : (A.baseChange κ).toAffine.Point →+ ((γ • A).baseChange κ).toAffine.Point := (vcMap hγ0).toAddMonoidHom
    let eb' : ((γ • A).baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point := (vcMap hγ0).symm.toAddMonoidHom
    have heb : eb ∈ rationalHomSet κ A (γ • A) := he
    have heb' : eb' ∈ rationalHomSet κ (γ • A) A := hes
    have K1 : ∀ R, eb' (eb R) = R := fun R => (vcMap hγ0).symm_apply_apply R
    have K2 : ∀ P, eb (eb' P) = P := fun P => (vcMap hγ0).apply_symm_apply P
    have K3 : ∀ R, eb R = 0 ↔ R = 0 := fun R => (vcMap hγ0).map_eq_zero_iff
    refine ⟨eb.comp φ, comp_mem_rationalHomSet κ _ _ _ hφ heb, φ'.comp eb', comp_mem_rationalHomSet κ _ _ _ heb' hφ',
      ?_, ?_, ?_, ?_⟩
    · rw [← hker]
      ext P
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
      exact K3 (φ P)
    · ext P
      show φ' (eb' (eb (φ P))) = ℓ • P
      rw [K1, L1]
    · ext P
      show eb (φ (φ' (eb' P))) = ℓ • P
      rw [L2, map_nsmul, K2]
    · intro T hT
      obtain ⟨T', hT', hh⟩ := hC T hT
      have : eb (φ T) = T' := eq_of_heq ((heq_vcMap hγ0 (φ T)).trans hh)
      show eb (φ T) ∈ C'
      rw [this]; exact hT'
  · rintro ⟨ψ, hψ, ψ', hψ', hkerψ, hψ'ψ, hψψ', hC⟩
    have Lψ'ψ : ∀ P : (E.baseChange κ).toAffine.Point, ψ' (ψ P) = ℓ • P := fun P => DFunLike.congr_fun hψ'ψ P
    have Lψψ' : ∀ P' : (E'.baseChange κ).toAffine.Point, ψ (ψ' P') = ℓ • P' := fun P' => DFunLike.congr_fun hψψ' P'
    have hψQ : ψ Q = 0 := by
      rw [← AddMonoidHom.mem_ker, hkerψ]; exact AddSubgroup.mem_zmultiples _
    obtain ⟨β, hβ, hψβ⟩ := huniv E' ψ hψ hψQ
    have Lψ : ∀ P, ψ P = β (φ P) := fun P => by rw [hψβ]; rfl

    have hβd : φ.comp ψ' ∈ rationalHomSet κ E' A := comp_mem_rationalHomSet κ _ _ _ hψ' hφ
    have hkill : ∀ P' : (E'.baseChange κ).toAffine.Point, (ℓ : ℤ) • P' = 0 → (φ.comp ψ') P' = 0 := by
      intro P' hP'
      show φ (ψ' P') = 0
      rw [← AddMonoidHom.mem_ker, hker, ← hkerψ, AddMonoidHom.mem_ker, Lψψ', ← natCast_zsmul, hP']
    obtain ⟨ε, hε, hεeq⟩ := exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ E' A hℓ0 hβd hkill
    have Lε : ∀ P' : (E'.baseChange κ).toAffine.Point, φ (ψ' P') = ℓ • ε P' := fun P' => by
      rw [← natCast_zsmul]; exact hεeq P'

    have hεβ : ε.comp β = AddMonoidHom.id _ := by
      ext P₀
      show ε (β P₀) = P₀
      obtain ⟨R₁, hR₁⟩ := exists_nsmul_eq_of_isAlgClosed A ℓ hℓ0 P₀
      obtain ⟨R₀, hR₀⟩ := hsurj R₁
      have hR : ℓ • φ R₀ = P₀ := by rw [hR₀]; exact hR₁
      rw [← hR, map_nsmul, map_nsmul, ← Lε, ← Lψ, Lψ'ψ, map_nsmul]

    have hβε : β.comp ε = AddMonoidHom.id _ := by
      ext P'
      show β (ε P') = P'
      obtain ⟨R₁, hR₁⟩ := exists_nsmul_eq_of_isAlgClosed E' ℓ hℓ0 P'
      let R' : (E'.baseChange κ).toAffine.Point := R₁
      have hR : ℓ • R' = P' := hR₁
      rw [← hR, map_nsmul, ← Lε, ← Lψ, Lψψ']

    obtain ⟨γ, hγ, hγε⟩ :=
      exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id E' A ε hε β hβ hβε hεβ
    refine ⟨γ, hγ, fun T hT => ⟨ψ T, hC T hT, ?_⟩⟩
    have hβT : β (φ T) = (Point.equivOfVariableChangeEq hγ).symm (φ T) := by
      apply (Point.equivOfVariableChangeEq hγ).injective
      rw [Equiv.apply_symm_apply, ← hγε]
      exact DFunLike.congr_fun hεβ (φ T)
    rw [Lψ, hβT]
    exact (heq_equivOfVariableChangeEq_symm γ A.toAffine hγ (φ T)).symm

end Isogeny

end WeierstrassCurve.VeluUniversalLevel

open WeierstrassCurve.VeluUniversalLevel in

theorem solution
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (E A E' : WeierstrassCurve κ) [E.IsElliptic] [A.IsElliptic] [E'.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point)
    (hφ : φ ∈ WeierstrassCurve.rationalHomSet κ E A) (hker : φ.ker = AddSubgroup.zmultiples Q)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
      (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ E V → α Q = 0 →
          ∃ β ∈ WeierstrassCurve.rationalHomSet κ A V, α = β.comp φ)
    (C : Set E.toAffine.Point) (C' : Set E'.toAffine.Point) :
    (∃ γ : WeierstrassCurve.VariableChange κ, γ • A = E' ∧
        ∀ T ∈ C, ∃ T' ∈ C', HEq (WeierstrassCurve.Affine.Point.vcInvFun γ A.toAffine (φ T)) T') ↔
      ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E E', ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E' E,
        ψ.ker = AddSubgroup.zmultiples Q ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧
          ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ C, ψ T ∈ C' :=
  exists_variableChange_iff_exists_dualPair E A E' hℓ hℓ0 Q hQ φ hφ hker huniv C C'

end

end S_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair (solution)
