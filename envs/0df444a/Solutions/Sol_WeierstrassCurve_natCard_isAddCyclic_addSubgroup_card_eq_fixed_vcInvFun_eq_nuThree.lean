-- Prove2me | solution 1 for WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ff0762e0-45f8-51a8-af41-a0027a911d5a

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_pow_three_eq_one
import Theorems.Thm_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one
import Theorems.Thm_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

namespace L3bSketch

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

theorem exists_eq_some_of_xy_eq {W : WeierstrassCurve L} {Q : W.toAffine.Point} {x y : L}
    (h : xy Q = some (x, y)) : ∃ h', Q = Point.some x y h' := by
  rcases Q with _ | ⟨x', y', h'⟩
  · exact absurd h (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h', rfl⟩

end L3bSketch

open L3bSketch

theorem solution
    {L : Type*} [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L]
    (B : L) (hB : B ≠ 0) (u : Lˣ) (hu : (u : L) ^ 3 = 1) (hu1 : (u : L) ≠ 1) (N : ℕ) (hN : N ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L)
          (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuThree N := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : NeZero N := ⟨hN⟩
  set W : WeierstrassCurve L := ⟨0, 0, 0, 0, B⟩ with hWdef
  set γ : VariableChange L := ⟨u, 0, 0, 0⟩ with hγdef
  have h2 : (2 : L) ≠ 0 := two_ne_zero

  have hΔ : W.Δ = -432 * B ^ 2 := by
    simp only [hWdef, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]; ring
  haveI hE : W.IsElliptic := ⟨by rw [hΔ]; exact isUnit_iff_ne_zero.mpr (by simp [hB])⟩

  have hW : γ • W = W := WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one u hu B
  let σ : W.toAffine.Point →+ W.toAffine.Point := vcHom γ W hW
  have hi3 : ((u⁻¹ : Lˣ) : L) ^ 3 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_one]
  have hi2 : ((u⁻¹ : Lˣ) : L) ^ 2 = u := by
    rw [Units.val_inv_eq_inv_val, inv_pow]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hu])

  have σ_some : ∀ (x y : L) (h : W.toAffine.Nonsingular x y),
      ∃ h', σ (Point.some x y h) = Point.some ((u : L) * x) y h' := by
    intro x y h
    apply exists_eq_some_of_xy_eq
    rw [xy_vcHom]
    simp only [xy, Option.map_some, hγdef, vcXInv, vcYInv, sub_zero, zero_mul, mul_zero, hi2, hi3, one_mul]

  have hσ : ∀ P : W.toAffine.Point, σ (σ P) + σ P + P = 0 := by
    rintro (_ | ⟨x, y, h⟩)
    · simp only [← WeierstrassCurve.Affine.Point.zero_def, map_zero, add_zero]
    · obtain ⟨h1, e1⟩ := σ_some x y h
      obtain ⟨h2', e2⟩ := σ_some ((u : L) * x) y h1
      rw [e1, e2]
      by_cases hx : x = 0
      · subst hx
        have hy0 : y ≠ 0 := by
          have heq := h.left
          rw [WeierstrassCurve.Affine.equation_iff] at heq
          simp only [hWdef, zero_mul, mul_zero, add_zero, zero_add, ne_eq] at heq
          rintro rfl
          apply hB
          simpa using heq.symm
        have e0 : ∀ (h' : W.toAffine.Nonsingular ((u : L) * 0) y),
            Point.some ((u : L) * 0) y h' = Point.some 0 y h := by
          intro h'; apply xy_injective; simp [xy]
        have e00 : ∀ (h' : W.toAffine.Nonsingular ((u : L) * ((u : L) * 0)) y),
            Point.some ((u : L) * ((u : L) * 0)) y h' = Point.some 0 y h := by
          intro h'; apply xy_injective; simp [xy]
        rw [e0, e00, WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model B h2 hy0 h,
          neg_add_cancel]
      · have hw2x : W.toAffine.Nonsingular ((u : L) ^ 2 * x) y := by
          have : (u : L) ^ 2 * x = (u : L) * ((u : L) * x) := by ring
          rw [this]; exact h2'
        have e3 : Point.some ((u : L) * ((u : L) * x)) y h2' = Point.some ((u : L) ^ 2 * x) y hw2x := by
          apply xy_injective; simp only [xy, Option.some.injEq, Prod.mk.injEq, and_true]; ring
        rw [e3, add_assoc, add_comm (Point.some ((u : L) * x) y h1),
          WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one B (u : L) hu hu1 h h1 hw2x hx,
          add_neg_cancel]

  have σinj : Function.Injective σ := fun a b h => by
    have ha : a = -(σ (σ a) + σ a) := eq_neg_of_add_eq_zero_right (hσ a)
    have hb : b = -(σ (σ b) + σ b) := eq_neg_of_add_eq_zero_right (hσ b)
    rw [ha, hb, h]

  have hns : ∀ p : ℕ, p.Prime → p ∣ N → ∃ a : W.toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a := by
    intro p hp _
    obtain ⟨T, hT, hk⟩ :=
      WeierstrassCurve.exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_pow_three_eq_one B hB u hu hu1 p hp
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

  rw [← AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree
    N e σ hσ hns]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun H => ?_)
  refine ⟨fun ⟨hc, hcard, hst⟩ => ⟨hc, hcard, ?_⟩, fun ⟨hc, hcard, hst⟩ => ⟨hc, hcard, ?_⟩⟩
  · haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
    exact (forall_exists_heq_iff_map_eq γ W hW σinj H).mp hst
  · haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
    exact (forall_exists_heq_iff_map_eq γ W hW σinj H).mpr hst

end S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree
end P2MW
export P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree (solution)
