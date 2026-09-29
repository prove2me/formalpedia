-- Prove2me | solution 1 for Rep.finiteDimensional_coind_and_finrank_eq_index_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/669e4348-40da-5445-95f6-d6ae3008c161

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_finiteDimensional_coind_and_finrank_eq_index_mul

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical TensorProduct

namespace CycBaseDimCoind

open Representation

variable {k : Type} [Field k] {G : Type} [Group G] (H : Subgroup G)
  {V : Type} [AddCommGroup V] [Module k V] (σ : Representation k H V)

noncomputable def sec (q : Quotient (QuotientGroup.rightRel H)) : G := q.out

lemma mk_sec (q : Quotient (QuotientGroup.rightRel H)) :
    Quotient.mk (QuotientGroup.rightRel H) (sec H q) = q :=
  Quotient.out_eq q

lemma sec_spec (g : G) : g * (sec H (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹ ∈ H := by
  have h := Quotient.mk_out (s := QuotientGroup.rightRel H) g
  exact QuotientGroup.rightRel_apply.mp h

omit [AddCommGroup V] [Module k V] in
lemma aux {W : Type} [AddCommGroup W] [Module k W] (τ : Representation k H W)
    (f : Quotient (QuotientGroup.rightRel H) → W)
    {q q' : Quotient (QuotientGroup.rightRel H)} (hq : q = q') (x : G)
    (hx : x * (sec H q)⁻¹ ∈ H) (hx' : x * (sec H q')⁻¹ ∈ H) :
    τ ⟨x * (sec H q)⁻¹, hx⟩ (f q) = τ ⟨x * (sec H q')⁻¹, hx'⟩ (f q') := by
  subst hq; rfl

noncomputable def coindVEquivFun :
    coindV H.subtype σ ≃ₗ[k] (Quotient (QuotientGroup.rightRel H) → V) where
  toFun F q := (F : G → V) (sec H q)
  invFun f := ⟨fun g => σ ⟨g * (sec H (Quotient.mk _ g))⁻¹, sec_spec H g⟩ (f (Quotient.mk _ g)), by
    rw [mem_coindV]
    intro h g
    have hq : Quotient.mk (QuotientGroup.rightRel H) ((h : G) * g) = Quotient.mk _ g :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))
    simp only [Subgroup.coe_subtype]
    rw [aux H σ f hq ((h : G) * g) (sec_spec H _)
      (by simpa only [mul_assoc] using H.mul_mem h.2 (sec_spec H g))]
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    exact Subtype.ext (mul_assoc _ _ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by
    apply Subtype.ext; funext g
    have hF := (mem_coindV _ _ _).mp F.2 ⟨g * (sec H (Quotient.mk _ g))⁻¹, sec_spec H g⟩
      (sec H (Quotient.mk _ g))
    simp only [Subgroup.coe_subtype, inv_mul_cancel_right] at hF
    exact hF.symm
  right_inv f := by
    funext q
    show σ ⟨sec H q * (sec H (Quotient.mk _ (sec H q)))⁻¹, _⟩ (f (Quotient.mk _ (sec H q))) = f q
    rw [aux H σ f (mk_sec H q) (sec H q) (sec_spec H (sec H q)) (by simp)]
    simp only [mul_inv_cancel]
    rw [show (⟨1, H.one_mem⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]

end CycBaseDimCoind

theorem solution
    {k : Type} [Field k] {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (N : Rep.{0} k H) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind H.subtype N) ∧
      Module.finrank k (Rep.coind H.subtype N) = H.index * Module.finrank k N := by
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  haveI : Fintype (Quotient (QuotientGroup.rightRel H)) := Fintype.ofFinite _
  let e : (Rep.coind H.subtype N) ≃ₗ[k] (Quotient (QuotientGroup.rightRel H) → N) :=
    CycBaseDimCoind.coindVEquivFun H N.ρ
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Subgroup.index,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H),
    Nat.card_eq_fintype_card]

end S_Rep_finiteDimensional_coind_and_finrank_eq_index_mul
end P2MW
export P2MW.S_Rep_finiteDimensional_coind_and_finrank_eq_index_mul (solution)
