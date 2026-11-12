-- Prove2me | solution 1 for OddOrder.Isaacs.Ch06.false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:35:32.395133+00:00
-- url     : https://prove2.me/submissions/9ed06927-c2e3-4bff-a74b-a476b6d1751a

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch01_Sylow/Basic.lean
--   OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ChermakDelgado
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Basic
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Sylow

-- ===== OddOrder/Isaacs/Ch01_Sylow/Basic.lean =====
namespace OddOrder.Isaacs.Ch01

open scoped IsMulCommutative

section

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 1.30** (前半, uniqueness form).  `|G| = p · q` で `q < p` が
ともに素数ならば, `G` の Sylow `p`-部分群は一意. -/
theorem sylow_p_subsingleton_of_card_eq_mul_prime_lt
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q < p) (hcard : Nat.card G = p * q) :
    Subsingleton (Sylow p G) := by
  have : Finite (Sylow p G) := inferInstance
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hPcard : Nat.card P = p := by
    have hmul := P.card_eq_multiplicity (G := G)
    rw [hcard, Nat.factorization_mul (Fact.out (p := p.Prime)).ne_zero
        (Fact.out (p := q.Prime)).ne_zero] at hmul
    simp only [Finsupp.coe_add, Pi.add_apply,
               Nat.Prime.factorization_self (Fact.out (p := p.Prime)),
               (Fact.out (p := q.Prime)).factorization,
               Finsupp.single_apply, if_neg hqp.ne] at hmul
    simpa using hmul
  have hPindex : (P : Subgroup G).index = q := by
    have h1 : Nat.card (P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
      Subgroup.card_mul_index _
    rw [hcard, hPcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (Fact.out (p := p.Prime)).pos h1
  have hdvd : Nat.card (Sylow p G) ∣ q := hPindex ▸ P.card_dvd_index
  have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  rcases (Nat.dvd_prime (Fact.out (p := q.Prime))).mp hdvd with hn1 | hnq
  · exact (Nat.card_eq_one_iff_unique.mp hn1).1
  · exfalso
    rw [hnq] at hmod
    have hge : 1 ≤ q := (Fact.out (p := q.Prime)).pos
    have hdvd' : p ∣ q - 1 := (Nat.modEq_iff_dvd' hge).mp hmod.symm
    have hlt : q - 1 < p := by omega
    have hq1 : q - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' hlt
    have hq_eq : q = 1 := by omega
    exact (Fact.out (p := q.Prime)).one_lt.ne' hq_eq

/-- **Isaacs Thm 1.30** (前半).  `|G| = p·q` で `q < p` がともに素数なら,
`G` の Sylow `p`-部分群は正規 (一意). -/
theorem sylow_normal_of_card_eq_mul_prime_lt
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q < p) (hcard : Nat.card G = p * q) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  have : Subsingleton (Sylow p G) :=
    sylow_p_subsingleton_of_card_eq_mul_prime_lt hqp hcard
  exact Sylow.normal_of_subsingleton P

end

end OddOrder.Isaacs.Ch01

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

section

/-- **Isaacs Thm 6.9** (Frobenius-group branch, abelian target): a Frobenius actor cannot
itself be a Frobenius group.  The proof uses the §6B partition by the kernel and conjugates of
the complement, whose part count is `1 + |N|`. -/
theorem false_of_frobeniusAction_isFrobeniusGroup_on_abelian
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U] (hFrob : IsFrobeniusAction A U)
    {N C : Subgroup A} (hGroup : IsFrobeniusGroup A N C) :
    False := by
  let partn := SubgroupPartition.frobeniusGroup hGroup
  have hparts :
      partn.parts.card = Nat.card N + 1 :=
    SubgroupPartition.frobeniusGroup_parts_card hGroup
  have hdvd : Nat.card N ∣ Nat.card A := by
    have htop : Nat.card N ∣ Nat.card (⊤ : Subgroup A) :=
      Subgroup.card_dvd_of_le (show N ≤ (⊤ : Subgroup A) from le_top)
    simpa [Subgroup.card_top] using htop
  exact false_of_frobeniusAction_partition_of_card_eq_succ_and_dvd_actor_card
    hFrob partn hparts hdvd

/-- **Isaacs Thm 6.9** reduction hook: if a subgroup `B` of the Frobenius actor is itself a
Frobenius group and the target contains a nontrivial `B`-invariant abelian subgroup, then the
Frobenius action is impossible.  The remaining textbook step is to obtain such a subgroup as
`Z(R)` from an invariant Sylow subgroup `R` via Isaacs Thm 3.23. -/
theorem false_of_frobeniusAction_actorSubgroup_isFrobeniusGroup_on_invariant_abelian_subgroup
    {A U : Type*} [Group A] [Group U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {N C : Subgroup B} (hGroup : IsFrobeniusGroup B N C)
    (M : Subgroup U) [Finite M] [Nontrivial M] [IsMulCommutative M]
    (hM : ∀ b : B, ∀ m ∈ M, (b : A) • m ∈ M) :
    False := by
  let : CommGroup M := inferInstance
  let : MulDistribMulAction B M := by
    letI : SMul B M := ⟨fun b m => ⟨(b : A) • (m : U), hM b m m.2⟩⟩
    exact Subtype.coe_injective.mulDistribMulAction M.subtype (fun _ _ => rfl)
  have hFrobM : IsFrobeniusAction B M := by
    intro b hb m hm hfix
    have hbA : (b : A) ≠ 1 := fun hbA => hb (Subtype.ext hbA)
    have hmU : (m : U) ≠ 1 := fun hmU => hm (Subtype.ext hmU)
    exact hFrob (b : A) hbA (m : U) hmU (Subtype.ext_iff.mp hfix)
  exact false_of_frobeniusAction_isFrobeniusGroup_on_abelian hFrobM hGroup

/-- **Isaacs Thm 6.9** (solvable Frobenius-group branch): a Frobenius actor cannot contain a
solvable Frobenius group.  This is the full reduction in L3495: choose an invariant Sylow
subgroup `R` of the target by Isaacs Thm 3.23, pass to the nontrivial invariant abelian subgroup
`Z(R)`, and apply the abelian-target Frobenius-group contradiction. -/
theorem false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U] (hFrob : IsFrobeniusAction A U)
    (B : Subgroup A) [Finite B] [Group.IsSolvable B]
    {N C : Subgroup B} (hGroup : IsFrobeniusGroup B N C) :
    False := by
  obtain ⟨M, hM_nontrivial, hM_comm, hM_inv⟩ :=
    exists_actorSubgroup_invariant_nontrivial_abelian_subgroup_of_isSolvable hFrob B
  have : Nontrivial M := hM_nontrivial
  have : IsMulCommutative M := hM_comm
  exact
    false_of_frobeniusAction_actorSubgroup_isFrobeniusGroup_on_invariant_abelian_subgroup
      hFrob B hGroup M hM_inv

private lemma orderOf_eq_prime_of_mem_subgroup_card_prime
    {G : Type*} [Group G] {H : Subgroup G} [Finite H] {p : ℕ}
    (hp : p.Prime) (hH_card : Nat.card H = p)
    {x : G} (hxH : x ∈ H) (hx : x ≠ 1) :
    orderOf x = p := by
  let xH : H := ⟨x, hxH⟩
  have hxH_ne : xH ≠ 1 := fun hxH_one => hx (Subtype.ext_iff.mp hxH_one)
  have h_dvd : orderOf xH ∣ p := by
    simpa [hH_card] using orderOf_dvd_natCard xH
  have h_order : orderOf xH = p := by
    rcases (Nat.dvd_prime hp).mp h_dvd with h_one | h_prime
    · exact False.elim (hxH_ne (orderOf_eq_one_iff.mp h_one))
    · exact h_prime
  exact (Subgroup.orderOf_coe xH).trans h_order

/-- **Isaacs Thm 6.9** (`p > q` branch for subgroups of order `pq`): a Frobenius actor cannot
contain a noncyclic subgroup of order `p*q` with `q < p`.  Such a subgroup would be a solvable
Frobenius group: its Sylow `p`-subgroup is normal, a Sylow `q`-subgroup is a complement, and any
fixed nonidentity pair would generate the whole group cyclically. -/
theorem _root_.solution
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hqp : q < p) (hCard : Nat.card B = p * q)
    (hNotCyclic : ¬ IsCyclic B) :
    False := by
  classical
  have hpq_ne : p ≠ q := fun hpq => (Nat.lt_irrefl q (hpq ▸ hqp))
  have hcop_qp : Nat.Coprime q p := (Nat.coprime_primes hq.out hp.out).mpr hpq_ne.symm
  have hcop_pq : Nat.Coprime p q := hcop_qp.symm
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := B)
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := B)
  have hCard' : Nat.card B = q * p := by rw [hCard, mul_comm]
  have hfact_p : (Nat.card B).factorization p = 1 := by
    rw [hCard, Nat.factorization_mul_apply_of_coprime hcop_pq,
        hp.out.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd
          (fun hd => hpq_ne ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hd))]
  have hfact_q : (Nat.card B).factorization q = 1 := by
    rw [hCard', Nat.factorization_mul_apply_of_coprime hcop_qp,
        hq.out.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd
          (fun hd => hpq_ne.symm ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hd))]
  have hP_card : Nat.card (P : Subgroup B) = p := by
    rw [P.card_eq_multiplicity, hfact_p, pow_one]
  have hQ_card : Nat.card (Q : Subgroup B) = q := by
    rw [Q.card_eq_multiplicity, hfact_q, pow_one]
  have hP_normal : (P : Subgroup B).Normal :=
    OddOrder.Isaacs.Ch01.sylow_normal_of_card_eq_mul_prime_lt
      (G := B) hqp hCard P
  have h_disjoint : Disjoint (P : Subgroup B) (Q : Subgroup B) :=
    IsPGroup.disjoint_of_ne p q hpq_ne _ _ P.isPGroup' Q.isPGroup'
  have h_compl : Subgroup.IsComplement' (P : Subgroup B) (Q : Subgroup B) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint
      (by rw [hP_card, hQ_card, hCard]) h_disjoint
  have hP_ne_bot : (P : Subgroup B) ≠ ⊥ := by
    intro hbot
    have hp_eq_one : p = 1 := by
      rw [← hP_card, hbot]
      simp
    exact hp.out.ne_one hp_eq_one
  have hQ_ne_bot : (Q : Subgroup B) ≠ ⊥ := by
    intro hbot
    have hq_eq_one : q = 1 := by
      rw [← hQ_card, hbot]
      simp
    exact hq.out.ne_one hq_eq_one
  let : (P : Subgroup B).Normal := hP_normal
  have hFrobGroup : IsFrobeniusGroup B (P : Subgroup B) (Q : Subgroup B) := by
    refine
      { isNormal := hP_normal
        isComplement := h_compl
        ne_bot_kernel := hP_ne_bot
        ne_bot_complement := hQ_ne_bot
        conj_frobenius := ?_ }
    intro a haQ ha_ne n hnP hn_ne h_conj
    have h_an : a * n = n * a := by
      have := congrArg (fun x => x * a) h_conj
      simpa [mul_assoc] using this
    have hcomm : Commute n a := h_an.symm
    have hn_order : orderOf n = p :=
      orderOf_eq_prime_of_mem_subgroup_card_prime hp.out hP_card hnP hn_ne
    have ha_order : orderOf a = q :=
      orderOf_eq_prime_of_mem_subgroup_card_prime hq.out hQ_card haQ ha_ne
    have hcop_orders : Nat.Coprime (orderOf n) (orderOf a) := by
      rw [hn_order, ha_order]
      exact hcop_pq
    have horder : orderOf (n * a) = p * q := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders,
        hn_order, ha_order]
    exact hNotCyclic (isCyclic_of_orderOf_eq_card (n * a) (by rw [horder, hCard]))
  have : Group.IsSolvable B := by
    have : IsCyclic (P : Subgroup B) := isCyclic_of_prime_card hP_card
    have hP_index : (P : Subgroup B).index = q := by
      have hmul := (P : Subgroup B).card_mul_index
      rw [hP_card, hCard] at hmul
      exact Nat.eq_of_mul_eq_mul_left hp.out.pos hmul
    have hquot_card : Nat.card (B ⧸ (P : Subgroup B)) = q := by
      rw [← Subgroup.index_eq_card, hP_index]
    have : IsCyclic (B ⧸ (P : Subgroup B)) := isCyclic_of_prime_card hquot_card
    let : CommGroup (P : Subgroup B) := IsCyclic.commGroup
    let : CommGroup (B ⧸ (P : Subgroup B)) := IsCyclic.commGroup
    exact Group.isSolvable_of_ker_le_range (P : Subgroup B).subtype
      (QuotientGroup.mk' (P : Subgroup B)) (by
        rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact
    false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup
      hFrob B hFrobGroup

end

end OddOrder.Isaacs.Ch06
