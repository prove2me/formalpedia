-- Prove2me | solution 1 for WeierstrassCurve.natCard_cycSub_eq_prime_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3005ace8-569f-5fc0-ab4f-9b1731938944

import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Logic.Equiv.Sum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_cycSub_eq_prime_add_one
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

section Generic

open AddSubgroup

namespace WeierstrassCurve p2m_export "WeierstrassCurve" "toAffine card_torsionBy_eq_sq_of_isAlgClosed" end WeierstrassCurve
p2m_open_scoped "WeierstrassCurve" in

private theorem WeierstrassCurve.natCard_cycSub_eq_prime_add_one {F : Type*} [Field F] [DecidableEq F]
    [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime]
    (hp : (p : F) ≠ 0) (h2 : (2 : F) ≠ 0) :
    Nat.card {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g} = p + 1 := by
  have hpr : p.Prime := Fact.out

  have hT : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p) = p ^ 2 :=
    WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W hp h2
  haveI hTfin : Finite (Submodule.torsionBy ℤ W.toAffine.Point p) :=
    Nat.finite_of_card_ne_zero (by rw [hT]; exact pow_ne_zero 2 hpr.ne_zero)

  have hmem : ∀ g : W.toAffine.Point, g ∈ Submodule.torsionBy ℤ W.toAffine.Point p ↔ p • g = 0 := by
    intro g
    rw [Submodule.mem_torsionBy_iff]
    exact Iff.of_eq (congrArg (· = 0) (natCast_zsmul g p))
  let e₁ : {g : W.toAffine.Point // addOrderOf g = p} ≃
      {x : Submodule.torsionBy ℤ W.toAffine.Point p // x ≠ 0} :=
    { toFun := fun g => ⟨⟨g.1, (hmem g.1).mpr (addOrderOf_eq_prime_iff.mp g.2).1⟩, fun h =>
        (addOrderOf_eq_prime_iff.mp g.2).2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨x.1.1, addOrderOf_eq_prime_iff.mpr ⟨(hmem x.1.1).mp x.1.2, fun h =>
        x.2 (Subtype.ext h)⟩⟩
      left_inv := fun g => rfl
      right_inv := fun x => rfl }
  have hS1 : Nat.card {g : W.toAffine.Point // addOrderOf g = p} + 1 = p ^ 2 := by
    rw [Nat.card_congr e₁, ← Finite.card_option,
      Nat.card_congr (Equiv.optionSubtypeNe (0 : Submodule.torsionBy ℤ W.toAffine.Point p)), hT]
  haveI hS1fin : Finite {g : W.toAffine.Point // addOrderOf g = p} :=
    Finite.of_equiv _ e₁.symm

  have hcardG : ∀ G : {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g},
      Nat.card G.1 = p := by
    rintro ⟨G, g, hg, rfl⟩
    rw [Nat.card_zmultiples, hg]
  have hfinG : ∀ G : {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g},
      Finite G.1 := fun G => Nat.finite_of_card_ne_zero (by rw [hcardG G]; exact hpr.ne_zero)
  have hordG : ∀ (G : {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g})
      (x : W.toAffine.Point), x ∈ G.1 → x ≠ 0 → addOrderOf x = p := by
    rintro ⟨G, g, hg, rfl⟩ x hx hx0
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    refine addOrderOf_eq_prime_iff.mpr ⟨?_, hx0⟩
    rw [← natCast_zsmul, smul_smul, mul_comm, mul_smul, natCast_zsmul, ← hg, addOrderOf_nsmul_eq_zero,
      smul_zero]
  have hgenG : ∀ (G : {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g})
      (x : W.toAffine.Point), x ∈ G.1 → x ≠ 0 → AddSubgroup.zmultiples x = G.1 := by
    intro G x hx hx0
    haveI := hfinG G
    refine AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr hx) (le_of_eq ?_)
    rw [hcardG G, Nat.card_zmultiples, hordG G x hx hx0]

  let π : {g : W.toAffine.Point // addOrderOf g = p} →
      {G : AddSubgroup W.toAffine.Point //
        ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g} :=
    fun g => ⟨AddSubgroup.zmultiples g.1, g.1, g.2, rfl⟩
  have hfib : ∀ G : {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g},
      Nat.card {g : {g : W.toAffine.Point // addOrderOf g = p} // π g = G} = p - 1 := by
    intro G
    haveI := hfinG G
    let eG : {g : {g : W.toAffine.Point // addOrderOf g = p} // π g = G} ≃
        {x : G.1 // x ≠ 0} :=
      { toFun := fun g => ⟨⟨g.1.1, by
            have h : AddSubgroup.zmultiples g.1.1 = G.1 := congrArg Subtype.val g.2
            rw [← h]
            exact AddSubgroup.mem_zmultiples g.1.1⟩, fun h =>
            (addOrderOf_eq_prime_iff.mp g.1.2).2 (congrArg Subtype.val h)⟩
        invFun := fun x => ⟨⟨x.1.1, hordG G x.1.1 x.1.2 fun h => x.2 (Subtype.ext h)⟩,
          Subtype.ext (hgenG G x.1.1 x.1.2 fun h => x.2 (Subtype.ext h))⟩
        left_inv := fun g => rfl
        right_inv := fun x => rfl }
    have h1 : Nat.card {x : G.1 // x ≠ 0} + 1 = p := by
      rw [← Finite.card_option, Nat.card_congr (Equiv.optionSubtypeNe (0 : G.1)), hcardG G]
    rw [Nat.card_congr eG]
    omega

  have hprod : Nat.card {g : W.toAffine.Point // addOrderOf g = p} =
      Nat.card {G : AddSubgroup W.toAffine.Point //
        ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g} * (p - 1) := by
    have e₂ : {g : W.toAffine.Point // addOrderOf g = p} ≃
        {G : AddSubgroup W.toAffine.Point //
          ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g} × Fin (p - 1) :=
      (Equiv.sigmaFiberEquiv π).symm.trans
        ((Equiv.sigmaCongrRight fun G =>
          @Finite.equivFinOfCardEq _ (Finite.of_injective (fun g => g.1) Subtype.val_injective) _
            (hfib G)).trans
          (Equiv.sigmaEquivProd _ _))
    rw [Nat.card_congr e₂, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (p - 1)),
      Fintype.card_fin]

  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hpr.two_le; omega⟩
  subst hm
  have h := hS1
  rw [hprod, show m + 2 - 1 = m + 1 from rfl] at h
  have h' : Nat.card {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = m + 2 ∧ G = AddSubgroup.zmultiples g} * (m + 1) =
      (m + 2 + 1) * (m + 1) := by
    have : (m + 2 + 1) * (m + 1) + 1 = (m + 2) ^ 2 := by ring
    omega
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) h'

end Generic

theorem solution {F : Type*} [Field F] [DecidableEq F]
    [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime]
    (hp : (p : F) ≠ 0) (h2 : (2 : F) ≠ 0) :
    Nat.card {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g} = p + 1 :=
  WeierstrassCurve.natCard_cycSub_eq_prime_add_one W p hp h2

#print axioms solution

end S_WeierstrassCurve_natCard_cycSub_eq_prime_add_one
end P2MW
export P2MW.S_WeierstrassCurve_natCard_cycSub_eq_prime_add_one (solution)
