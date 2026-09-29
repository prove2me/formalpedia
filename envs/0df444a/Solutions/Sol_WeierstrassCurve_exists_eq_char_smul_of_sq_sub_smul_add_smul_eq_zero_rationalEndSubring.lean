-- Prove2me | solution 1 for WeierstrassCurve.exists_eq_char_smul_of_sq_sub_smul_add_smul_eq_zero_rationalEndSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/54d1f2f1-ba03-53b3-ba89-dbe04a302809

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_eq_char_smul_of_sq_sub_smul_add_smul_eq_zero_rationalEndSubring
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open scoped Quaternion TensorProduct
open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map Affine.Point.some toAffine Affine.Point map_a₁ Affine.Point.neg_some baseChange map_a₃ evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring zero_mem_rationalHomSet isRationallyRepresented_id exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd add_mem_rationalHomSet comp_mem_rationalHomSet"
p2m_open "WeierstrassCurve"

section neg

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]

private lemma some_congr_y {W : WeierstrassCurve k} {x y₁ y₂ : k}
    (h₁ : W.toAffine.Nonsingular x y₁) (e : y₁ = y₂) :
    ∃ h₂ : W.toAffine.Nonsingular x y₂, Affine.Point.some x y₁ h₁ = Affine.Point.some x y₂ h₂ := by
  subst e
  exact ⟨h₁, rfl⟩

theorem isRationallyRepresented_neg (W₁ W₂ : WeierstrassCurve F)
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : IsRationallyRepresented k W₁ W₂ α) :
    IsRationallyRepresented k W₁ W₂ (-α) := by
  obtain ⟨nX, dX, nY, dY, B, hB, h⟩ := hα
  refine ⟨nX, dX, -(nY * dX) - C (C W₂.a₁) * nX * dY - C (C W₂.a₃) * dX * dY, dY * dX,
    B, hB, ?_⟩
  intro x y hxy hxB
  obtain ⟨hdX, hdY, h', heq⟩ := h x y hxy hxB
  refine ⟨hdX, ?_, ?_⟩
  · simpa [evalEvalBC, Polynomial.map_mul, evalEval_mul] using mul_ne_zero hdY hdX
  · rw [AddMonoidHom.neg_apply, heq, Affine.Point.neg_some]
    apply some_congr_y
    simp only [Affine.negY, evalEvalBC, Polynomial.map_sub, Polynomial.map_neg,
      Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom, evalEval_sub, evalEval_neg,
      evalEval_mul, evalEval_C, eval_C, baseChange, map_a₁, map_a₃] at hdX hdY ⊢
    field_simp

theorem neg_mem_rationalHomSet (W₁ W₂ : WeierstrassCurve F)
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) : -α ∈ rationalHomSet k W₁ W₂ := by
  rcases hα with rfl | hα
  · exact Or.inl (neg_zero)
  · exact Or.inr (isRationallyRepresented_neg k W₁ W₂ hα)

theorem mem_rationalHomSet_of_mem_rationalEndSubring [IsAlgClosed k] (W : WeierstrassCurve F)
    [W.IsElliptic] {α : AddMonoid.End (W.baseChange k).toAffine.Point}
    (hα : α ∈ rationalEndSubring k W) : α ∈ rationalHomSet k W W := by
  induction hα using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_rationalHomSet k W W
  | one => exact Or.inr (isRationallyRepresented_id k W)
  | add x y _ _ hx hy => exact add_mem_rationalHomSet k W W hx hy
  | neg x _ hx => exact neg_mem_rationalHomSet k W W hx
  | mul x y _ _ hx hy => exact comp_mem_rationalHomSet k W W W hy hx

end neg

end WeierstrassCurve

theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0)
    (φ : ↥(WeierstrassCurve.rationalEndSubring k X))
    (hφ : ∃ t n : ℤ, φ * φ - t • φ + n • (1 : ↥(WeierstrassCurve.rationalEndSubring k X)) = 0 ∧
      (p : ℤ) ∣ t ∧ (p : ℤ) ^ 2 ∣ n) :
    ∃ ψ : ↥(WeierstrassCurve.rationalEndSubring k X), φ = (p : ℤ) • ψ := by
  obtain ⟨t, n, hrel, ht, hn⟩ := hφ

  have e_mul : ∀ (f g : AddMonoid.End (X.baseChange k).toAffine.Point) (P),
      (f * g) P = f (g P) := fun _ _ _ => rfl
  have e_add : ∀ (f g : AddMonoid.End (X.baseChange k).toAffine.Point) (P),
      (f + g) P = f P + g P := fun _ _ _ => rfl
  have e_sub : ∀ (f g : AddMonoid.End (X.baseChange k).toAffine.Point) (P),
      (f - g) P = f P - g P := fun _ _ _ => rfl
  have e_one : ∀ (P : (X.baseChange k).toAffine.Point),
      (1 : AddMonoid.End (X.baseChange k).toAffine.Point) P = P := fun _ => rfl
  have e_zero : ∀ (P : (X.baseChange k).toAffine.Point),
      (0 : AddMonoid.End (X.baseChange k).toAffine.Point) P = 0 := fun _ => rfl
  have e_int : ∀ (z : ℤ) (P : (X.baseChange k).toAffine.Point),
      (z : AddMonoid.End (X.baseChange k).toAffine.Point) P = z • P :=
    fun z P => AddMonoid.End.intCast_apply z P
  have hmem : (φ : AddMonoid.End (X.baseChange k).toAffine.Point) ∈
      WeierstrassCurve.rationalHomSet k X X :=
    WeierstrassCurve.mem_rationalHomSet_of_mem_rationalEndSubring k X φ.2

  have hpt : ∀ P, (φ : AddMonoid.End (X.baseChange k).toAffine.Point)
      ((φ : AddMonoid.End (X.baseChange k).toAffine.Point) P) + n • P =
      t • (φ : AddMonoid.End (X.baseChange k).toAffine.Point) P := by
    intro P
    have hrel2 := hrel
    rw [zsmul_eq_mul, zsmul_eq_mul] at hrel2
    have h1 := congrArg
      (fun ψ : ↥(WeierstrassCurve.rationalEndSubring k X) =>
        (ψ : AddMonoid.End (X.baseChange k).toAffine.Point) P) hrel2
    simp only [Subring.coe_add, AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_one,
      Subring.coe_zero, Subring.coe_intCast, e_mul, e_add, e_sub, e_one, e_zero, e_int] at h1

    rw [← sub_eq_zero, ← h1]
    abel
  have hrel' : (φ : AddMonoid.End (X.baseChange k).toAffine.Point).comp φ +
      n • AddMonoidHom.id _ = t • (φ : AddMonoid.End (X.baseChange k).toAffine.Point) := by
    ext P
    have h__af := hpt P
    simp at h__af ⊢
    exact h__af
  obtain ⟨γ, hγ, hγeq⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
      (k := k) p X hmem t n hrel' 0 (by simpa using ht) (by simpa using hn)
  refine ⟨⟨γ, Subring.subset_closure hγ⟩, Subtype.ext ?_⟩

  ext P

  have h3 : (φ : AddMonoid.End (X.baseChange k).toAffine.Point) P - (0 : ℤ) • P = (p : ℤ) • γ P :=
    DFunLike.congr_fun hγeq P
  rw [zero_zsmul, sub_zero] at h3
  simp only [zsmul_eq_mul, Subring.coe_mul, Subring.coe_intCast, e_mul, e_int]
  exact h3

end S_WeierstrassCurve_exists_eq_char_smul_of_sq_sub_smul_add_smul_eq_zero_rationalEndSubring
end P2MW
export P2MW.S_WeierstrassCurve_exists_eq_char_smul_of_sq_sub_smul_add_smul_eq_zero_rationalEndSubring (solution)
