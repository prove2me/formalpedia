-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.twoSubgroups_commutative_of_minimal_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:03:08.250194+00:00
-- url     : https://prove2.me/submissions/d7b140e9-1954-4525-bd12-c8a60eebd151

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_AbelianQuotientComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Theorems.Thm_OddOrder_Isaacs_Ch07_quotientComplement_isMulCommutative_of_sylow_isCoatom
import Theorems.Thm_OddOrder_Isaacs_Ch07_sylow_isCoatom_of_minimal_counterexample

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_AbelianQuotientComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped IsMulCommutative

section MinimalCounterexampleStepSix

/-- **Isaacs Theorem 7.1, Step 6.**

In a minimal counterexample with `p ≠ 2`, every `2`-subgroup is abelian.  The
preceding theorem makes the normal `p`-complement `Nbar` of `G/O_p(G)` abelian.
The quotient map is injective on a `2`-subgroup because its kernel is a
`p`-group, and the image lies in `Nbar` because its order is coprime to the
index of that normal complement. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp2 : p ≠ 2)
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :
    ∀ S : Subgroup G, IsPGroup 2 S →
      ∀ x y : ↥S, x * y = y * x := by
  classical
  obtain ⟨Nbar, hNbar_normal, hNbar_complement⟩ := hQuotient
  let : Nbar.Normal := hNbar_normal
  have hP_max : IsCoatom (P : Subgroup G) :=
    sylow_isCoatom_of_minimal_counterexample P hHyp ih hG
      ⟨Nbar, hNbar_normal, hNbar_complement⟩
  have hNbar_comm : IsMulCommutative ↥Nbar :=
    quotientComplement_isMulCommutative_of_sylow_isCoatom
      P hP_max hNbar_normal hNbar_complement
  let : IsMulCommutative ↥Nbar := hNbar_comm
  let q : G →* G ⧸ OddOrder.Isaacs.Ch01.opCore p G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch01.opCore p G)
  have hq : Function.Surjective q :=
    QuotientGroup.mk'_surjective (OddOrder.Isaacs.Ch01.opCore p G)
  have hker : q.ker = OddOrder.Isaacs.Ch01.opCore p G := by
    dsimp [q]
    exact QuotientGroup.ker_mk' _
  set Pbar : Sylow p (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
    P.mapSurjective hq with hPbar_def
  have hcomp := hNbar_complement Pbar
  intro S hS_two x y
  have hU_p : IsPGroup p (OddOrder.Isaacs.Ch01.opCore p G) :=
    OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hS_U_coprime : Nat.Coprime (Nat.card ↥S)
      (Nat.card ↥(OddOrder.Isaacs.Ch01.opCore p G)) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS_two
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hU_p
    rw [ha, hb]
    exact ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
      hp2.symm).pow a b
  have hS_inf_U : S ⊓ OddOrder.Isaacs.Ch01.opCore p G = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hS_U_coprime).eq_bot
  have hqS_injective : Function.Injective (q.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz_U : (z : G) ∈ OddOrder.Isaacs.Ch01.opCore p G := by
      have hz_ker : (z : G) ∈ q.ker := hz
      rw [hker] at hz_ker
      exact hz_ker
    have hz_inf : (z : G) ∈ S ⊓ OddOrder.Isaacs.Ch01.opCore p G :=
      ⟨z.2, hz_U⟩
    rw [hS_inf_U, Subgroup.mem_bot] at hz_inf
    exact Subtype.ext hz_inf
  set Sbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
    S.map q with hSbar_def
  have hSbar_two : IsPGroup 2 Sbar := by
    rw [hSbar_def]
    exact hS_two.map q
  have hSbar_index_coprime : Nat.Coprime (Nat.card ↥Sbar) Nbar.index := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hSbar_two
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp Pbar.isPGroup'
    rw [hcomp.symm.index_eq_card, ha, hb]
    exact ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
      hp2.symm).pow a b
  have hSbar_le_Nbar : Sbar ≤ Nbar :=
    Subgroup.le_of_coprime_card_index_of_normal hSbar_index_coprime
  have hx_Nbar : q (x : G) ∈ Nbar := by
    apply hSbar_le_Nbar
    rw [hSbar_def]
    exact ⟨x, x.2, rfl⟩
  have hy_Nbar : q (y : G) ∈ Nbar := by
    apply hSbar_le_Nbar
    rw [hSbar_def]
    exact ⟨y, y.2, rfl⟩
  apply hqS_injective
  have hcomm :
      (⟨q (x : G), hx_Nbar⟩ : ↥Nbar) *
          ⟨q (y : G), hy_Nbar⟩ =
        (⟨q (y : G), hy_Nbar⟩ : ↥Nbar) *
          ⟨q (x : G), hx_Nbar⟩ :=
    mul_comm _ _
  simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
    map_mul] using
    congrArg Subtype.val hcomm

end MinimalCounterexampleStepSix

end OddOrder.Isaacs.Ch07
