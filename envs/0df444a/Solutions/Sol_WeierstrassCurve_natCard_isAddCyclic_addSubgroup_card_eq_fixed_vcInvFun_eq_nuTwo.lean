-- Prove2me | solution 1 for WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/601c2bf5-1646-5b3d-ad24-c12bc96ab4d6

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_sq_eq_neg_one
import Theorems.Thm_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

namespace L3aSketch

variable {L : Type*} [Field L] [DecidableEq L]

def xy {W : WeierstrassCurve L} : W.toAffine.Point → Option (L × L)
  | 0 => none
  | .some x y _ => some (x, y)

theorem xy_injective {W : WeierstrassCurve L} : Function.Injective (xy (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hh
  · rfl
  · exact absurd hh (by simp [xy])
  · exact absurd hh (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl

theorem xy_neg {W : WeierstrassCurve L} (P : W.toAffine.Point) :
    xy (-P) = (xy P).map (fun q => (q.1, W.toAffine.negY q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

theorem xy_vcInvFun (γ : VariableChange L) {W : WeierstrassCurve L} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem heq_castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) := by subst e; exact HEq.rfl

theorem xy_castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P := by subst e; rfl

noncomputable def vcHom (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hW).toAddMonoidHom.comp
    { toFun := Point.vcInvFun γ W.toAffine
      map_zero' := Point.vcInvFun_zero
      map_add' := Point.vcInvFun_add γ W.toAffine }

theorem vcHom_apply (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W) (P : W.toAffine.Point) :
    vcHom γ W hW P = castPt hW (Point.vcInvFun γ W.toAffine P) := rfl

theorem heq_vcHom (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W) (P : W.toAffine.Point) :
    HEq (Point.vcInvFun γ W.toAffine P) (vcHom γ W hW P) := heq_castPt hW _

theorem xy_vcHom (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W) (P : W.toAffine.Point) :
    xy (vcHom γ W hW P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rw [vcHom_apply, xy_castPt, xy_vcInvFun]

theorem forall_exists_heq_iff_map_eq (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W)
    (hinj : Function.Injective (vcHom γ W hW)) (H : AddSubgroup W.toAffine.Point) [Finite H] :
    (∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ W.toAffine T) T') ↔ H.map (vcHom γ W hW) = H := by
  constructor
  · intro hH
    have hle : H.map (vcHom γ W hW) ≤ H := by
      intro y hy
      rw [AddSubgroup.mem_map] at hy
      obtain ⟨T, hT, rfl⟩ := hy
      obtain ⟨T', hT', hheq⟩ := hH T hT
      rwa [eq_of_heq ((heq_vcHom γ W hW T).symm.trans hheq)]
    exact AddSubgroup.eq_of_le_of_card_ge hle
      (Nat.card_congr (H.equivMapOfInjective _ hinj).toEquiv).le
  · intro hH T hT
    exact ⟨vcHom γ W hW T, by rw [← hH]; exact AddSubgroup.mem_map_of_mem _ hT, heq_vcHom γ W hW T⟩

end L3aSketch

open L3aSketch

theorem solution
    {L : Type*} [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L]
    (A : L) (hA : A ≠ 0) (u : Lˣ) (hu : (u : L) ^ 2 = -1) (N : ℕ) (hN : N ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L)
          (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuTwo N := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : NeZero N := ⟨hN⟩
  set W : WeierstrassCurve L := ⟨0, 0, 0, A, 0⟩ with hWdef
  set γ : VariableChange L := ⟨u, 0, 0, 0⟩ with hγdef

  have hΔ : W.Δ = -64 * A ^ 3 := by
    simp only [hWdef, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]; ring
  haveI hE : W.IsElliptic := ⟨by rw [hΔ]; exact isUnit_iff_ne_zero.mpr (by simp [hA])⟩

  have hW : γ • W = W := WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one u hu A
  let σ : W.toAffine.Point →+ W.toAffine.Point := vcHom γ W hW
  have hi2 : ((u⁻¹ : Lˣ) : L) ^ 2 = -1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_neg, inv_one]

  have hσ : ∀ P : W.toAffine.Point, σ (σ P) = -P := by
    intro P
    apply xy_injective
    rw [xy_vcHom, xy_vcHom, xy_neg]
    rcases xy P with _ | ⟨x, y⟩
    · rfl
    · simp only [Option.map_some, hγdef, hWdef, vcXInv, vcYInv, Affine.negY, sub_zero, zero_mul, mul_zero,
        Option.some.injEq, Prod.mk.injEq]
      constructor
      · linear_combination (((u⁻¹ : Lˣ) : L) ^ 2 * x - x) * hi2
      · linear_combination (((u⁻¹ : Lˣ) : L) ^ 4 * y - ((u⁻¹ : Lˣ) : L) ^ 2 * y + y) * hi2
  have σinj : Function.Injective σ := fun a b h => by
    have h2 := congrArg σ h; rwa [hσ, hσ, neg_inj] at h2

  have hns : ∀ p : ℕ, p.Prime → p ∣ N → ∃ a : W.toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a := by
    intro p hp _
    obtain ⟨T, hT, hk⟩ :=
      WeierstrassCurve.exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_sq_eq_neg_one A hA u hu p hp
    refine ⟨T, hT, fun k hk' => hk k ?_⟩
    exact (heq_vcHom γ W hW T).trans (heq_of_eq hk')

  have hNL : ((N : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr hN
  obtain ⟨e⟩ : Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ W.toAffine.Point N) := by
    have h := W.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := L) hNL
    have hb : (W⁄L) = W.toAffine := by
      show (W.baseChange L).toAffine = W.toAffine
      rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
    rw [hb] at h
    exact h

  rw [← AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo N e σ hσ hns]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun H => ?_)
  refine ⟨fun ⟨hc, hcard, hst⟩ => ⟨hc, hcard, ?_⟩, fun ⟨hc, hcard, hst⟩ => ⟨hc, hcard, ?_⟩⟩
  · haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
    exact (forall_exists_heq_iff_map_eq γ W hW σinj H).mp hst
  · haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
    exact (forall_exists_heq_iff_map_eq γ W hW σinj H).mpr hst

end S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo
end P2MW
export P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo (solution)
