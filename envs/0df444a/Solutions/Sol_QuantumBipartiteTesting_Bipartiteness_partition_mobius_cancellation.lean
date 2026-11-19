-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.partition_mobius_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:06:05.602181+00:00
-- url     : https://prove2.me/submissions/91d9681f-ada5-4a4d-9083-d05204c39db1

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness.PartitionProof
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private def Chain {α : Type*} [LE α] (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≤ y ∨ y ≤ x

private lemma chain_insert {α : Type*} [PartialOrder α] (S : Finset α) (a : α)
    (h : ∀ x ∈ S, a ≤ x) : Chain (insert a S) ↔ Chain S := by
  constructor
  · intro hc x hx y hy
    exact hc x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)
  · intro hc x hx y hy
    simp only [mem_insert] at hx hy
    rcases hx with rfl | hx
    · exact Or.inl (by rcases hy with rfl | hy; exact le_rfl; exact h y hy)
    · rcases hy with rfl | hy
      · exact Or.inr (h x hx)
      · exact hc x hx y hy

private lemma chain_sum_cone {α : Type*} [PartialOrder α] (s : Finset α) (a : α)
    (ha : a ∈ s) (hmin : ∀ x ∈ s, a ≤ x) :
    (∑ S ∈ s.powerset, if Chain S then (-1:ℤ)^S.card else 0) = 0 := by
  have hs : s = insert a (s.erase a) := (insert_erase ha).symm
  rw [hs,Finset.sum_powerset_insert (by simp : a ∉ s.erase a),← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro S hS
  have hsub := mem_powerset.mp hS
  have haS : a ∉ S := fun h => (mem_erase.mp (hsub h)).1 rfl
  have hmins : ∀ x ∈ S, a ≤ x := fun x hx => hmin x (mem_of_mem_erase (hsub hx))
  rw [chain_insert S a hmins,card_insert_of_notMem haS]
  split_ifs <;> simp [pow_succ]

private lemma chain_least {α : Type*} [PartialOrder α] {T : Finset α}
    (hT : T.Nonempty) (hc : Chain T) : ∃ a ∈ T, ∀ x ∈ T, a ≤ x := by
  obtain ⟨a,ha,hmin⟩ := T.exists_minimal hT
  refine ⟨a,ha,?_⟩
  intro x hx
  rcases hc a ha x hx with h | h
  · exact h
  · exact hmin hx h

private def ChainMobius {α : Type*} [Fintype α] [PartialOrder α] (a b : α) : ℤ :=
  if a = b then 1 else if a ≤ b then
    ∑ S ∈ (Finset.univ.filter fun x => a < x ∧ x < b).powerset,
      if Chain S then (-1:ℤ)^(S.card+1) else 0
  else 0

private def Interval {α : Type*} [Fintype α] [PartialOrder α] (a b : α) : Finset α :=
  univ.filter fun x => a ≤ x ∧ x < b

private def ChainDomain {α : Type*} [Fintype α] [PartialOrder α] (a b : α) : Finset (α × Finset α) :=
  ((Interval a b).product (univ : Finset (Finset α))).filter fun rS =>
    rS.2 ⊆ (univ.filter fun x => rS.1 < x ∧ x < b) ∧ Chain rS.2

private lemma chain_decompose {α : Type*} [Fintype α] [PartialOrder α] (a b : α) :
    (∑ rS ∈ ChainDomain a b, (-1:ℤ)^(rS.2.card+1)) =
      ∑ T ∈ (Interval a b).powerset.filter (fun T => T.Nonempty ∧ Chain T), (-1:ℤ)^T.card := by
  apply Finset.sum_bij (fun rS _ => insert rS.1 rS.2)
  · intro rS hrS
    have hd := mem_filter.mp hrS
    obtain ⟨hrS,_⟩ := mem_product.mp hd.1
    obtain ⟨hsub,hchain⟩ := hd.2
    obtain ⟨ha,hrb⟩ := (mem_filter.mp hrS).2
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_,⟨insert_nonempty _ _,?_⟩⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hrS
      · obtain ⟨hrx,hxb⟩ := (mem_filter.mp (hsub hx)).2
        exact mem_filter.mpr ⟨mem_univ _,ha.trans hrx.le,hxb⟩
    · exact (chain_insert rS.2 rS.1 (fun x hx => ((mem_filter.mp (hsub hx)).2.1).le)).mpr hchain
  · intro rS hrS tS htS heq
    have hd := mem_filter.mp hrS
    obtain ⟨hrS,_⟩ := mem_product.mp hd.1
    obtain ⟨hsub,hchain⟩ := hd.2
    have htd := mem_filter.mp htS
    obtain ⟨htS,_⟩ := mem_product.mp htd.1
    obtain ⟨tsub,tchain⟩ := htd.2
    have hrt : rS.1 ≤ tS.1 := by
      have hh : tS.1 ∈ insert rS.1 rS.2 := heq.symm ▸ mem_insert_self _ _
      rcases mem_insert.mp hh with h | h
      · exact h.symm.le
      · exact ((mem_filter.mp (hsub h)).2.1).le
    have htr : tS.1 ≤ rS.1 := by
      have hh : rS.1 ∈ insert tS.1 tS.2 := heq ▸ mem_insert_self _ _
      rcases mem_insert.mp hh with h | h
      · exact h.symm.le
      · exact ((mem_filter.mp (tsub h)).2.1).le
    have hr : rS.1 = tS.1 := le_antisymm hrt htr
    have hrnot : rS.1 ∉ rS.2 := by
      intro hh
      exact (lt_irrefl _) ((mem_filter.mp (hsub hh)).2.1)
    have htnot : tS.1 ∉ tS.2 := by
      intro hh
      exact (lt_irrefl _) ((mem_filter.mp (tsub hh)).2.1)
    apply Prod.ext hr
    have hErase := congrArg (fun S : Finset α => S.erase rS.1) heq
    have hrnot' : tS.1 ∉ rS.2 := hr ▸ hrnot
    simpa [hr,hrnot',htnot] using hErase
  · intro T hT
    obtain ⟨hTsub,hTne,hTchain⟩ := mem_filter.mp hT
    obtain ⟨r,hr,hmin⟩ := chain_least hTne hTchain
    refine ⟨(r,T.erase r),?_,insert_erase hr⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨(mem_powerset.mp hTsub) hr,mem_univ _⟩,?_,?_⟩
    · intro x hx
      have hTx := mem_of_mem_erase hx
      have hrx : r < x := lt_of_le_of_ne (hmin x hTx) (mem_erase.mp hx).1.symm
      exact mem_filter.mpr ⟨mem_univ _,hrx,((mem_filter.mp ((mem_powerset.mp hTsub) hTx)).2.2)⟩
    · exact fun x hx y hy => hTchain x (mem_of_mem_erase hx) y (mem_of_mem_erase hy)
  · intro rS hrS
    obtain ⟨_,hsub,_⟩ := mem_filter.mp hrS
    have hnot : rS.1 ∉ rS.2 := by
      intro hh
      exact (lt_irrefl _) ((mem_filter.mp (hsub hh)).2.1)
    rw [card_insert_of_notMem hnot]

private lemma mobius_chain_domain {α : Type*} [Fintype α] [PartialOrder α] (a b : α) :
    (∑ r ∈ Interval a b, ChainMobius r b) =
      ∑ rS ∈ ChainDomain a b, (-1:ℤ)^(rS.2.card+1) := by
  unfold ChainDomain
  rw [Finset.sum_filter]
  calc
    _ = ∑ r ∈ Interval a b, ∑ S : Finset α,
        if S ⊆ (univ.filter fun x => r < x ∧ x < b) ∧ Chain S then (-1:ℤ)^(S.card+1) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hlt := (mem_filter.mp hr).2.2
      rw [ChainMobius,if_neg hlt.ne,if_pos hlt.le]
      simp only [← Finset.mem_powerset,ite_and]
      exact (Finset.sum_ite_mem_eq _ _).symm
    _ = _ := (Finset.sum_product (Interval a b) (univ : Finset (Finset α))
      (fun rS : α × Finset α => if rS.2 ⊆ (univ.filter fun x => rS.1 < x ∧ x < b) ∧
        Chain rS.2 then (-1:ℤ)^(rS.2.card+1) else 0)).symm

private lemma chain_sum_empty_split {α : Type*} [PartialOrder α] (s : Finset α) :
    (∑ T ∈ s.powerset, if Chain T then (-1:ℤ)^T.card else 0) =
      1 + ∑ T ∈ s.powerset.filter (fun T => T.Nonempty ∧ Chain T), (-1:ℤ)^T.card := by
  rw [← Finset.sum_filter]
  have hempty : ∅ ∈ s.powerset.filter Chain := by simp [Chain]
  rw [← Finset.sum_erase_add _ _ hempty]
  have heq : (s.powerset.filter Chain).erase ∅ =
      s.powerset.filter (fun T => T.Nonempty ∧ Chain T) := by
    ext T
    simp only [mem_erase,mem_filter,Finset.nonempty_iff_ne_empty]
    tauto
  rw [heq]
  simp [add_comm]

private lemma chainMobius_upper_sum {α : Type*} [Fintype α] [PartialOrder α]
    (a b : α) (hab : a < b) :
    (∑ r ∈ (univ.filter fun r => a ≤ r ∧ r ≤ b), ChainMobius r b) = 0 := by
  have ha : a ∈ Interval a b := mem_filter.mpr ⟨mem_univ _,le_rfl,hab⟩
  have hmin : ∀ x ∈ Interval a b, a ≤ x := fun x hx => (mem_filter.mp hx).2.1
  have hcone := chain_sum_cone (Interval a b) a ha hmin
  rw [chain_sum_empty_split,← chain_decompose,← mobius_chain_domain] at hcone
  have hinterval : (univ.filter fun r => a ≤ r ∧ r ≤ b) = insert b (Interval a b) := by
    ext r
    simp only [Interval,mem_filter,mem_univ,true_and,mem_insert]
    constructor
    · rintro ⟨har,hrb⟩
      rcases hrb.eq_or_lt with h | h
      · exact Or.inl h
      · exact Or.inr ⟨har,h⟩
    · rintro (rfl | ⟨har,hrb⟩)
      · exact ⟨hab.le,le_rfl⟩
      · exact ⟨har,hrb.le⟩
  rw [hinterval,Finset.sum_insert (by simp [Interval]),ChainMobius,if_pos rfl]
  linarith

private lemma partition_le_iff {k : ℕ} (p r : Partition k) : p ≤ r ↔ Refines p r := by
  change (∀ i j, p.val i j ≤ r.val i j) ↔ (∀ i j, p.val i j = true → r.val i j = true)
  simp only [Bool.le_iff_imp]


private lemma chainMobius_eq {k : ℕ} (p r : Partition k) : ChainMobius p r = Mobius p r := by
  have hset : (univ.filter fun t : Partition k => p < t ∧ t < r) =
      (univ.filter fun t : Partition k => Refines p t ∧ Refines t r ∧ p ≠ t ∧ t ≠ r) := by
    ext t
    simp only [mem_filter,mem_univ,true_and,lt_iff_le_and_ne,partition_le_iff]
    tauto
  unfold ChainMobius
  rw [hset]
  unfold Mobius
  simp only [partition_le_iff]
  split_ifs <;> try rfl
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Chain,partition_le_iff]

private lemma partition_mobius_upper {k : ℕ} (p r : Partition k) (hpr : Refines p r) (hne : p ≠ r) :
    (∑ t : Partition k, if Refines p t ∧ Refines t r then Mobius t r else 0) = 0 := by
  have hlt : p < r := lt_of_le_of_ne ((partition_le_iff p r).mpr hpr) hne
  have hh := chainMobius_upper_sum p r hlt
  simp only [chainMobius_eq,Finset.sum_filter,partition_le_iff] at hh
  exact hh

end
end QuantumBipartiteTesting.Bipartiteness.PartitionProof


open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.PartitionProof
attribute [local instance] Classical.propDecidable

theorem solution {k : ℕ} (p r : Partition k) (hpr : Refines p r) (hne : p ≠ r) :
    (∑ t : Partition k, if Refines p t ∧ Refines t r then Mobius t r else 0) = 0 :=
  partition_mobius_upper p r hpr hne
