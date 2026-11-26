-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.exists_sylow_pretransitive_of_index_primePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:04.874797+00:00
-- url     : https://prove2.me/submissions/c5f137d5-26d8-4c92-a8d8-b7176fe72034

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hindex : H.index = p ^ a) :
    ∃ P : Sylow p G,
      MulAction.IsPretransitive P (G ⧸ H) ∧ H.relIndex (P : Subgroup G) = p ^ a := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p H := Sylow.nonempty.some
  obtain ⟨P, hPcomap⟩ := S.exists_comap_subtype_eq
  obtain ⟨b, hScard⟩ := S.2.exists_card_eq
  let e : H.subgroupOf (P : Subgroup G) ≃ S :=
    { toFun := fun x ↦ by
        let y : H := ⟨(x.1 : G), x.2⟩
        refine ⟨y, ?_⟩
        rw [← hPcomap]
        exact x.1.2
      invFun := fun y ↦ by
        have hyP : (y.1 : G) ∈ (P : Subgroup G) := by
          have : y.1 ∈ P.comap H.subtype := by simpa [hPcomap] using y.2
          exact this
        exact ⟨⟨(y.1 : G), hyP⟩, y.1.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; ext; rfl }
  have hinterCard : Nat.card (H.subgroupOf (P : Subgroup G)) = p ^ b := by
    rw [Nat.card_congr e, hScard]
  have hPcard_tower :
      Nat.card (H.subgroupOf (P : Subgroup G)) * H.relIndex (P : Subgroup G) = Nat.card P := by
    exact (H.subgroupOf (P : Subgroup G)).card_mul_index
  have hrel_le : H.relIndex (P : Subgroup G) ≤ H.index := by
    simpa using H.relIndex_le_of_le_right (K := (P : Subgroup G)) (L := ⊤) le_top
      Subgroup.index_ne_zero_of_finite
  have hPcard_le : Nat.card P ≤ p ^ (b + a) := by
    rw [← hPcard_tower, hinterCard, pow_add]
    exact Nat.mul_le_mul_left _ (hrel_le.trans_eq hindex)
  have hpow_dvd_cardG : p ^ (b + a) ∣ Nat.card G := by
    refine ⟨S.index, ?_⟩
    calc
      Nat.card G = Nat.card H * H.index := H.card_mul_index.symm
      _ = (Nat.card S * S.index) * p ^ a := by rw [hindex, S.card_mul_index]
      _ = p ^ (b + a) * S.index := by rw [hScard, pow_add]; ac_rfl
  have hpow_dvd_cardP : p ^ (b + a) ∣ Nat.card P :=
    P.pow_dvd_card_of_pow_dvd_card hpow_dvd_cardG
  have hPcard : Nat.card P = p ^ (b + a) := by
    apply le_antisymm hPcard_le
    exact Nat.le_of_dvd Nat.card_pos hpow_dvd_cardP
  have hrel : H.relIndex (P : Subgroup G) = p ^ a := by
    apply Nat.mul_left_cancel (pow_pos hp.pos _)
    calc
      p ^ b * H.relIndex (P : Subgroup G) = Nat.card P := by
        rw [← hinterCard]
        exact hPcard_tower
      _ = p ^ b * p ^ a := by rw [hPcard, pow_add]
  have hstab :
      MulAction.stabilizer P ((1 : G) : G ⧸ H) = H.subgroupOf (P : Subgroup G) := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    have hsmul : g • ((1 : G) : G ⧸ H) = (((g : G) * 1 : G) : G ⧸ H) := rfl
    rw [hsmul, mul_one, QuotientGroup.eq]
    simp only [mul_one, Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]
  have horbit : MulAction.orbit P ((1 : G) : G ⧸ H) = Set.univ :=
    (Set.eq_univ_iff_ncard (MulAction.orbit P ((1 : G) : G ⧸ H))).2 <| by
        calc
          (MulAction.orbit P ((1 : G) : G ⧸ H)).ncard =
              (MulAction.stabilizer P ((1 : G) : G ⧸ H)).index :=
            (MulAction.index_stabilizer P ((1 : G) : G ⧸ H)).symm
          _ = H.relIndex (P : Subgroup G) := by rw [hstab]; rfl
          _ = p ^ a := hrel
          _ = Nat.card (G ⧸ H) := by rw [← H.index_eq_card, hindex]
  have hpre : MulAction.IsPretransitive P (G ⧸ H) := ⟨by
    intro y z
    have hy : y ∈ MulAction.orbit P ((1 : G) : G ⧸ H) := by rw [horbit]; trivial
    have hz : z ∈ MulAction.orbit P ((1 : G) : G ⧸ H) := by rw [horbit]; trivial
    obtain ⟨r, hr⟩ := hy
    obtain ⟨s, hs⟩ := hz
    refine ⟨s * r⁻¹, ?_⟩
    rw [← hr, ← hs]
    simp [smul_smul]⟩
  exact ⟨P, hpre, hrel⟩
end SharpIntermediateSubgroupBounds
