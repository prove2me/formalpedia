-- Prove2me | solution 1 for Subgroup.finsum_card_mul_card_fixedBy_quotient_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3febb65a-83ec-51f9-bbd4-018c0d535f5f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_finsum_card_mul_card_fixedBy_quotient_eq_card

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

namespace ArtIndCount

variable {G : Type} [Group G]

lemma mem_preimage_fixedBy_iff (D : Subgroup G) (g x : G) :
    x ∈ QuotientGroup.mk ⁻¹' MulAction.fixedBy (G ⧸ D) g ↔ x⁻¹ * g * x ∈ D := by
  rw [Set.mem_preimage, MulAction.mem_fixedBy, MulAction.Quotient.smul_mk, smul_eq_mul,
    QuotientGroup.eq, ← inv_mem_iff]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

lemma card_mul_card_fixedBy_eq_sum [Fintype G] (D : Subgroup G) (g : G) :
    (Nat.card D : ℤ) * Nat.card (MulAction.fixedBy (G ⧸ D) g)
      = ∑ x : G, if x⁻¹ * g * x ∈ D then (1 : ℤ) else 0 := by
  have h1 : Nat.card D * Nat.card (MulAction.fixedBy (G ⧸ D) g)
      = Nat.card {x : G // x⁻¹ * g * x ∈ D} := by
    rw [← QuotientGroup.card_preimage_mk]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_preimage_fixedBy_iff D g x)
  have h2 : (Nat.card {x : G // x⁻¹ * g * x ∈ D} : ℤ)
      = ∑ x : G, if x⁻¹ * g * x ∈ D then (1 : ℤ) else 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast
    rfl
  rw [← h2, ← h1, Nat.cast_mul]

lemma orderOf_inv_mul_mul (x g : G) : orderOf (x⁻¹ * g * x) = orderOf g := by
  have h := orderOf_injective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective g
  simpa [MulAut.conj_apply] using h

omit [Group G] in

lemma ite_mul_sum_ite [Fintype G] (P : Prop) [Decidable P] (c : ℤ) (q : G → Prop)
    [DecidablePred q] :
    (if P then c * ∑ x : G, (if q x then (1 : ℤ) else 0) else 0)
      = ∑ x : G, if P ∧ q x then c else 0 := by
  by_cases hP : P
  · simp only [hP, if_true, true_and, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  · simp [hP]

end ArtIndCount

theorem solution (p : ℕ) {G : Type} [Group G] [Finite G]
    (b : Subgroup G → ℤ)
    (hb : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D then b D else 0) = 1)
    (g : G) (hg : (orderOf g).Coprime p) :
    ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p
      then (Nat.card D : ℤ) * b D * Nat.card (MulAction.fixedBy (G ⧸ D) g) else 0) = Nat.card G := by
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  haveI : Fintype G := Fintype.ofFinite _

  have hinner : ∀ x : G, ∑ D : Subgroup G,
      (if (IsCyclic D ∧ (Nat.card D).Coprime p) ∧ x⁻¹ * g * x ∈ D then b D else 0) = 1 := by
    intro x
    have hcyc : IsCyclic (Subgroup.zpowers (x⁻¹ * g * x)) := inferInstance
    have hcop : (Nat.card (Subgroup.zpowers (x⁻¹ * g * x))).Coprime p := by
      rw [Nat.card_zpowers, ArtIndCount.orderOf_inv_mul_mul]; exact hg
    have h := hb _ hcyc hcop
    rw [finsum_eq_sum_of_fintype] at h
    rw [← h]
    refine Finset.sum_congr rfl fun D _ => if_congr ?_ rfl rfl
    rw [Subgroup.zpowers_le, and_assoc]
  rw [finsum_eq_sum_of_fintype]
  calc ∑ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p
          then (Nat.card D : ℤ) * b D * Nat.card (MulAction.fixedBy (G ⧸ D) g) else 0)
      = ∑ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p
          then b D * ∑ x : G, (if x⁻¹ * g * x ∈ D then (1 : ℤ) else 0) else 0) := by
        refine Finset.sum_congr rfl fun D _ => ?_
        rw [← ArtIndCount.card_mul_card_fixedBy_eq_sum]
        split_ifs <;> ring
    _ = ∑ D : Subgroup G, ∑ x : G,
          (if (IsCyclic D ∧ (Nat.card D).Coprime p) ∧ x⁻¹ * g * x ∈ D then b D else 0) :=
        Finset.sum_congr rfl fun D _ => ArtIndCount.ite_mul_sum_ite _ _ _
    _ = ∑ x : G, ∑ D : Subgroup G,
          (if (IsCyclic D ∧ (Nat.card D).Coprime p) ∧ x⁻¹ * g * x ∈ D then b D else 0) :=
        Finset.sum_comm
    _ = ∑ x : G, (1 : ℤ) := Finset.sum_congr rfl fun x _ => hinner x
    _ = Nat.card G := by simp [Nat.card_eq_fintype_card]

end S_Subgroup_finsum_card_mul_card_fixedBy_quotient_eq_card
end P2MW
export P2MW.S_Subgroup_finsum_card_mul_card_fixedBy_quotient_eq_card (solution)
