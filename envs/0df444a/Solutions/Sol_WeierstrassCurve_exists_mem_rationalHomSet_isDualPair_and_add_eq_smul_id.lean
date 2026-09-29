-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b9c6da8f-bd8b-59d3-a677-3791bf707c9f

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map toAffine Affine.nonsingular_neg baseChange evalEvalBC rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet dualIsogenyExistence_rationalEndSubring surjective_of_mem_rationalHomSet add_mem_rationalHomSet comp_mem_rationalHomSet"
namespace DualTrace
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
  (W : WeierstrassCurve F) [W.IsElliptic]

abbrev Pt := (W.baseChange k).toAffine.Point

variable {k} in

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

omit [IsAlgClosed k] [DecidableEq k] in
theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) : evalEvalBC k p x y = bc x y p := rfl

omit [IsAlgClosed k] [DecidableEq k] in
@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by simp [bc]

omit [IsAlgClosed k] [DecidableEq k] [W.IsElliptic] in
theorem exists_some_of_eq {Q : Pt k W} {x₁ y₁ : k}
    {h₁ : (W.baseChange k).toAffine.Nonsingular x₁ y₁} (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂ : (W.baseChange k).toAffine.Nonsingular x₂ y₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

omit [IsAlgClosed k] [W.IsElliptic] in

theorem neg_mem_rationalHomSet {α : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W) :
    -α ∈ rationalHomSet k W W := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · rw [neg_zero]; exact zero_mem_rationalHomSet k W W
  refine Or.inr ⟨nX, dX, -(nY * dX) - C (C W.a₁) * nX * dY - C (C W.a₃) * dX * dY, dY * dX,
    B, hB, ?_⟩
  intro x y h hx
  obtain ⟨hdX, hdY, h', hP⟩ := hrep x y h hx
  simp only [evalEvalBC_eq] at hdX hdY hP ⊢
  refine ⟨hdX, by rw [map_mul]; exact mul_ne_zero hdY hdX, ?_⟩
  have hneg : (-α) (.some x y h) =
      .some (bc x y nX / bc x y dX)
        ((W.baseChange k).toAffine.negY (bc x y nX / bc x y dX) (bc x y nY / bc x y dY))
        ((Affine.nonsingular_neg ..).mpr h') := by
    rw [AddMonoidHom.neg_apply, hP]; rfl
  refine exists_some_of_eq k W hneg rfl ?_
  simp only [Affine.negY, map_sub, map_neg, map_mul, bc_CC]
  change -(bc x y nY / bc x y dY) - algebraMap F k W.a₁ * (bc x y nX / bc x y dX)
      - algebraMap F k W.a₃ = _
  field_simp

theorem mem_rationalHomSet_of_mem {φ : AddMonoid.End (Pt k W)} (hφ : φ ∈ rationalEndSubring k W) :
    (φ : Pt k W →+ Pt k W) ∈ rationalHomSet k W W := by
  induction hφ using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_rationalHomSet k W W
  | one => exact id_mem_rationalHomSet k W
  | add x y _ _ hx hy => exact WeierstrassCurve.add_mem_rationalHomSet k W W hx hy
  | neg x _ hx => exact neg_mem_rationalHomSet k W hx
  | mul x y _ _ hx hy => exact WeierstrassCurve.comp_mem_rationalHomSet k W W W hy hx

theorem exists_dual {α : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W) (hα0 : α ≠ 0) :
    ∃ σ ∈ rationalHomSet k W W, ∃ t n : ℤ, 0 < n ∧ AddMonoidHom.IsDualPair α σ n ∧
      α + σ = t • AddMonoidHom.id _ := by

  have hmem : (α : AddMonoid.End (Pt k W)) ∈ rationalEndSubring k W := Subring.subset_closure hα

  obtain ⟨D, hDmem, hDnorm⟩ :=
    WeierstrassCurve.dualIsogenyExistence_rationalEndSubring k W (α : AddMonoid.End (Pt k W)) hmem
  rcases hDnorm.lt_or_eq with hpos | hzero
  ·
    refine ⟨D.dual, mem_rationalHomSet_of_mem k W hDmem, D.trace, D.norm, hpos, D.isDualPair, ?_⟩
    ext P
    rw [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply]
    exact D.add_dual_apply P
  ·
    have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hα hα0
    have hdual0 : ∀ Q : Pt k W, D.dual Q = 0 := by
      intro Q
      obtain ⟨P, rfl⟩ := hsurj Q
      have h := D.isDualPair.comp_left P
      rw [← hzero, zero_zsmul] at h
      exact h
    have hαt : ∀ P : Pt k W, α P = D.trace • P := by
      intro P
      have h := D.add_dual_apply P
      rw [hdual0, add_zero] at h
      exact h
    have ht0 : D.trace ≠ 0 := by
      intro ht
      apply hα0
      ext P
      rw [hαt, ht, zero_zsmul, AddMonoidHom.zero_apply]

    refine ⟨α, hα, 2 * D.trace, D.trace ^ 2, by positivity, ⟨fun P => ?_, fun P => ?_⟩, ?_⟩
    · rw [hαt P, map_zsmul, hαt P, smul_smul, sq]
    · rw [hαt P, map_zsmul, hαt P, smul_smul, sq]
    · ext P
      rw [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, hαt P,
        ← add_zsmul, two_mul]

end WeierstrassCurve.DualTrace
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id.WeierstrassCurve.DualTrace"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id.WeierstrassCurve"

theorem solution {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve F) [W.IsElliptic] {α : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W W) (hα0 : α ≠ 0) : ∃ σ ∈ WeierstrassCurve.rationalHomSet k W W, ∃ t n : ℤ, 0 < n ∧ AddMonoidHom.IsDualPair α σ n ∧ α + σ = t • AddMonoidHom.id _ :=
  WeierstrassCurve.DualTrace.exists_dual k W hα hα0

end S_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id (solution)
