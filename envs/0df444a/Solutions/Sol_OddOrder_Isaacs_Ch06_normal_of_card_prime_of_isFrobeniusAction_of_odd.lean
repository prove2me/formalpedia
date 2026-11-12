-- Prove2me | solution 1 for OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusAction_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:54.461253+00:00
-- url     : https://prove2.me/submissions/14b2147a-a066-453b-a6d7-d2ee2abb977d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Theorems.Thm_OddOrder_Isaacs_Ch06_centralizes_commutator_of_card_prime_coprime

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- **Huppert, *Endliche Gruppen I*, Kapitel V, Satz 8.18 b):** in a Frobenius complement of
odd order, every subgroup of prime order is normal.

The complement `A` is a Z-group (Step 1), so `N := commutator A` is cyclic, normal, with
`A ⧸ N` cyclic and `(|N|, [A : N]) = 1`.  Let `R ≤ A` have prime order `r`.

*If `r ∣ |N|`:* every order-`r` subgroup lies in `N` (its image in the coprime quotient `A ⧸ N`
is trivial), and order-`r` subgroups of the cyclic `N` are unique, so every conjugate of `R`
equals `R`.

*If `r ∤ |N|`:* `R` centralizes `N` (Step 2).  For a conjugate `R^g` and `k = g r₀ g⁻¹ ∈ R^g`
(`r₀ ∈ R`), the element `ν := k r₀⁻¹ = ⁅g, r₀⁆` lies in `N`; as `r₀` centralizes `ν` and
`k^r = 1 = r₀^r`, we get `ν^r = 1`, so `ν = 1` by coprimality and `k = r₀ ∈ R`. -/
theorem _root_.solution
    (hFrob : IsFrobeniusAction A U) (hodd : Odd (Nat.card A))
    {R : Subgroup A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r) :
    R.Normal := by
  have hZ : IsZGroup A := isZGroup_of_isFrobeniusAction_of_odd hFrob hodd
  have hNcyc : IsCyclic ↥(commutator A) := IsZGroup.isCyclic_commutator (G := A)
  have hNnorm : (commutator A).Normal := inferInstance
  refine ⟨fun n hn g => ?_⟩
  -- it suffices to show the conjugate `R^g` is contained in `R`
  suffices hle : R.map (MulAut.conj g).toMonoidHom ≤ R by
    apply hle
    rw [Subgroup.mem_map]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  set Rg : Subgroup A := R.map (MulAut.conj g).toMonoidHom with hRgdef
  have hRgcard : Nat.card ↥Rg = r := by
    rw [hRgdef, Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv.symm]
    exact hRcard
  by_cases hrN : r ∣ Nat.card ↥(commutator A)
  · -- `r ∣ |N|`: both subgroups lie in the cyclic `N`, where order-`r` subgroups are unique
    have hcont : ∀ K : Subgroup A, Nat.card ↥K = r → K ≤ commutator A := by
      intro K hK
      have hcop : Nat.Coprime r (commutator A).index :=
        Nat.Coprime.coprime_dvd_left hrN (IsZGroup.coprime_commutator_index A)
      have hdvd1 : Nat.card ↥(K.map (QuotientGroup.mk' (commutator A))) ∣ r := by
        rw [← hK]
        exact @Subgroup.card_map_dvd A (A ⧸ commutator A) _ _ K
          (QuotientGroup.mk' (commutator A))
      have hdvd2 : Nat.card ↥(K.map (QuotientGroup.mk' (commutator A))) ∣ (commutator A).index := by
        have h := Subgroup.card_subgroup_dvd_card (K.map (QuotientGroup.mk' (commutator A)))
        rwa [← Subgroup.index_eq_card] at h
      have h1 : Nat.card ↥(K.map (QuotientGroup.mk' (commutator A))) = 1 :=
        Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd1 hdvd2)
      have hbot : K.map (QuotientGroup.mk' (commutator A)) = ⊥ := Subgroup.card_eq_one.mp h1
      intro x hx
      have hxmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (commutator A)) hx
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxmem
      exact hxmem
    have hRle : R ≤ commutator A := hcont R hRcard
    have hRgle : Rg ≤ commutator A := hcont Rg hRgcard
    have hRsub : Nat.card ↥(R.subgroupOf (commutator A)) = r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv]; exact hRcard
    have hRgsub : Nat.card ↥(Rg.subgroupOf (commutator A)) = r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRgle).toEquiv]; exact hRgcard
    have heq : R.subgroupOf (commutator A) = Rg.subgroupOf (commutator A) :=
      eq_of_card_eq_prime_of_isCyclic hr hRsub hRgsub
    have hRRg : R = Rg := by
      have h := Subgroup.subgroupOf_inj.mp heq
      rwa [inf_of_le_left hRle, inf_of_le_left hRgle] at h
    exact hRRg.ge
  · -- `r ∤ |N|`: `R` centralizes `N`; the commutator/coprimality argument forces `R^g ≤ R`
    have hRcent : R ≤ Subgroup.centralizer ((commutator A : Subgroup A) : Set A) :=
      centralizes_commutator_of_card_prime_coprime hFrob hodd hr hRcard hrN
    have hcoprN : Nat.Coprime r (Nat.card ↥(commutator A)) := (hr.coprime_iff_not_dvd).mpr hrN
    intro k hk
    have hkr : k ^ r = 1 := by
      have h : (⟨k, hk⟩ : ↥Rg) ^ r = 1 := by rw [← hRgcard]; exact pow_card_eq_one'
      have := congrArg (Subgroup.subtype Rg) h
      rwa [map_pow, map_one, Subgroup.coe_subtype] at this
    rw [hRgdef, Subgroup.mem_map] at hk
    obtain ⟨r₀, hr₀, hkval⟩ := hk
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at hkval
    have hr₀r : r₀ ^ r = 1 := by
      have h : (⟨r₀, hr₀⟩ : ↥R) ^ r = 1 := by rw [← hRcard]; exact pow_card_eq_one'
      have := congrArg (Subgroup.subtype R) h
      rwa [map_pow, map_one, Subgroup.coe_subtype] at this
    set ν : A := k * r₀⁻¹ with hνdef
    have hνN : ν ∈ commutator A := by
      have hνe : ν = ⁅g, r₀⁆ := by rw [hνdef, ← hkval, commutatorElement_def]
      rw [hνe]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top r₀)
    have hcomm : Commute ν r₀ := by
      have h := hRcent hr₀
      rw [Subgroup.mem_centralizer_iff] at h
      exact h ν hνN
    have hk_eq : k = ν * r₀ := by rw [hνdef]; group
    have hνr : ν ^ r = 1 := by
      have h := hcomm.mul_pow r
      rw [← hk_eq, hkr, hr₀r, mul_one] at h
      exact h.symm
    have hνord_r : orderOf ν ∣ r := orderOf_dvd_of_pow_eq_one hνr
    have hνord_N : orderOf ν ∣ Nat.card ↥(commutator A) := by
      have heq : orderOf ν = orderOf (⟨ν, hνN⟩ : ↥(commutator A)) :=
        orderOf_injective (commutator A).subtype Subtype.coe_injective ⟨ν, hνN⟩
      rw [heq]; exact orderOf_dvd_natCard _
    have hν1 : ν = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcoprN ▸ Nat.dvd_gcd hνord_r hνord_N))
    have : k = r₀ := by rw [hk_eq, hν1, one_mul]
    rw [this]; exact hr₀

end OddOrder.Isaacs.Ch06
