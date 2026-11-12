-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.hasNormalPComplement_of_quotient_of_isPiGroup_compl
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:43.423169+00:00
-- url     : https://prove2.me/submissions/49533e71-9c1e-4ddc-8f80-0f2f607b570d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepThree

/-- A normal `p`-complement lifts across a normal `p′`-kernel.

The inverse image of the quotient complement is again a `p′`-group: its normal
kernel and quotient are both `p′`-groups.  Its index is the order of every Sylow
`p`-subgroup, because the quotient map is injective on such a subgroup. -/
theorem _root_.solution
    [Finite G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} N)
    (hQ : OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ N)) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  classical
  obtain ⟨Nbar, hNbar_normal, hNbar_complement⟩ := hQ
  let : Nbar.Normal := hNbar_normal
  obtain ⟨Qbar⟩ := (inferInstance : Nonempty (Sylow p (G ⧸ N)))
  have hNbar_card : Nat.card Nbar = (Qbar : Subgroup (G ⧸ N)).index :=
    ((hNbar_complement Qbar).index_eq_card).symm
  have hNbar_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Nbar := by
    intro q hq
    rw [hNbar_card] at hq
    intro hqp
    subst q
    exact Qbar.not_dvd_index (Nat.dvd_of_mem_primeFactors hq)
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  let K : Subgroup G := Nbar.comap q
  have hK_normal : K.Normal := hNbar_normal.comap q
  have hN_le_K : N ≤ K := by
    dsimp [K, q]
    exact QuotientGroup.le_comap_mk' N Nbar
  have hK_map : K.map q = Nbar := by
    dsimp [K, q]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) Nbar
  have hK_map_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} (K.map q) := by
    rw [hK_map]
    exact hNbar_pi'
  have hN_sub_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} (N.subgroupOf K) :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hN_le_K hN_pi'
  have hK_quotient_pi' :
      ∀ r ∈ (Nat.card (↥K ⧸ N.subgroupOf K)).primeFactors, r ≠ p :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.primeFactors_quotient_subgroupOf
      hK_map_pi'
  have hK_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} K :=
    OddOrder.Isaacs.Ch03.IsPiGroup.of_normal_quotient
      (N.subgroupOf K) hN_sub_pi' hK_quotient_pi'
  refine ⟨K, hK_normal, fun P => ?_⟩
  have hP_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
        (P : Subgroup G) :=
    Subgroup.isPiSubgroup_of_isPGroup_of_mem
      P.isPGroup' (by simp)
  have hPN_coprime :
      Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card N) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hP_pi (by
        intro r hr
        simpa using hN_pi' r hr)
  have hP_inf_N : (P : Subgroup G) ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hPN_coprime).eq_bot
  let qP : ↥(P : Subgroup G) →* G ⧸ N := q.comp (P : Subgroup G).subtype
  have hqP_injective : Function.Injective qP := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_N : (x : G) ∈ N := by
      have hx' : (x : G) ∈ (QuotientGroup.mk' N).ker := hx
      rwa [QuotientGroup.ker_mk'] at hx'
    have hx_inf : (x : G) ∈ (P : Subgroup G) ⊓ N := ⟨x.property, hx_N⟩
    rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
    exact Subtype.ext hx_inf
  have hqP_range : qP.range = (P : Subgroup G).map q := by
    simp [qP, q, MonoidHom.range_comp, Subgroup.range_subtype]
  have hP_map_card :
      Nat.card ↥((P : Subgroup G).map q) = Nat.card ↥(P : Subgroup G) := by
    have hEquiv : ↥(P : Subgroup G) ≃* ↥qP.range :=
      MonoidHom.ofInjective hqP_injective
    have hcard : Nat.card ↥qP.range = Nat.card ↥(P : Subgroup G) :=
      (Nat.card_congr hEquiv.toEquiv).symm
    rwa [hqP_range] at hcard
  set Pbar : Sylow p (G ⧸ N) := P.mapSurjective hq with hPbar_def
  have hPbar_coe :
      (Pbar : Subgroup (G ⧸ N)) = (P : Subgroup G).map q := by
    rw [hPbar_def, Sylow.coe_mapSurjective]
  have hK_index : K.index = Nat.card (P : Subgroup G) := by
    calc
      K.index = Nbar.index := by
        dsimp [K]
        exact Nbar.index_comap_of_surjective hq
      _ = Nat.card (Pbar : Subgroup (G ⧸ N)) :=
        (hNbar_complement Pbar).symm.index_eq_card
      _ = Nat.card ↥((P : Subgroup G).map q) := by rw [hPbar_coe]
      _ = Nat.card ↥(P : Subgroup G) := hP_map_card
  have hcard :
      Nat.card K * Nat.card (P : Subgroup G) = Nat.card G := by
    rw [← hK_index]
    exact K.card_mul_index
  have hKP_coprime :
      Nat.Coprime (Nat.card K) (Nat.card (P : Subgroup G)) :=
    (OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hP_pi (by
        intro r hr
        simpa using hK_pi' r hr)).symm
  exact Subgroup.isComplement'_of_coprime hcard hKP_coprime

end MinimalCounterexampleStepThree

end OddOrder.Isaacs.Ch07
