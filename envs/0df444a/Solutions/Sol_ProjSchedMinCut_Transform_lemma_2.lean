-- Prove2me | solution 1 for ProjSchedMinCut.Transform.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:56:46.924367+00:00
-- url     : https://prove2.me/submissions/2279c028-f010-4572-a310-eafad15c050b

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_ProjSchedMinCut_Transform_Setting

open ProjSchedMinCut.Transform
open ProjSchedMinCut.Transform.Instance
open scoped ENNReal

private lemma earliest_latest_bounds {n : ℕ} (I : Instance n)
    (hfeas : ∃ S, I.Feasible S) (j : Fin (n + 1)) :
    0 ≤ I.earliest j ∧ I.earliest j ≤ I.latest j ∧ I.latest j ≤ I.T := by
  obtain ⟨S, hS⟩ := hfeas
  have hbddBelow : BddBelow (I.startTimes j) := by
    refine ⟨0, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    exact (hS'.2 j).1
  have hbddAbove : BddAbove (I.startTimes j) := by
    refine ⟨I.T, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    have h1 := (hS'.2 j).2
    have h2 : (0 : ℤ) ≤ I.p j := Nat.cast_nonneg _
    omega
  have hmem : S j ∈ I.startTimes j := ⟨S, hS, rfl⟩
  have he : I.earliest j ≤ S j := csInf_le hbddBelow hmem
  have hl : S j ≤ I.latest j := le_csSup hbddAbove hmem
  have h0 : 0 ≤ I.earliest j := by
    refine le_csInf ⟨S j, hmem⟩ ?_
    rintro t ⟨S', hS', rfl⟩
    exact (hS'.2 j).1
  have hT : I.latest j ≤ I.T := by
    refine csSup_le ⟨S j, hmem⟩ ?_
    rintro t ⟨S', hS', rfl⟩
    have h1 := (hS'.2 j).2
    have h2 : (0 : ℤ) ≤ I.p j := Nat.cast_nonneg _
    omega
  exact ⟨h0, le_trans he hl, hT⟩

private lemma finset_sum_ite_eq {α : Type*} [DecidableEq α] (A : Finset α) (a : α) (c : α → ℝ) :
    (∑ s ∈ A, (if s = a then c s else 0)) = if a ∈ A then c a else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    rw [Finset.sum_insert hbs, ih]
    by_cases hba : b = a
    · subst hba
      simp [hbs]
    · have hab : a ≠ b := Ne.symm hba
      simp [hba, hab]

private lemma finset_sum_ite_eq_int (A : Finset ℕ) (a : ℕ) :
    (∑ s ∈ A, (if s = a then (1 : ℤ) else 0)) = if a ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    rw [Finset.sum_insert hbs, ih]
    by_cases hba : b = a
    · subst hba
      simp [hbs]
    · have hab : a ≠ b := Ne.symm hba
      simp [hba, hab]

private lemma sum_eq_one_of_nonneg {S : Finset ℕ} {f : ℕ → ℤ}
    (hnonneg : ∀ a ∈ S, 0 ≤ f a) (hsum : ∑ a ∈ S, f a = 1) :
    ∃ a₀ ∈ S, ∀ a ∈ S, f a = if a = a₀ then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    simp at hsum
  | @insert b s hbs ih =>
    rw [Finset.sum_insert hbs] at hsum
    have hb : 0 ≤ f b := hnonneg b (Finset.mem_insert_self b s)
    have hs_nonneg : ∀ a ∈ s, 0 ≤ f a := fun a ha => hnonneg a (Finset.mem_insert_of_mem ha)
    have hs_sum : 0 ≤ ∑ a ∈ s, f a := Finset.sum_nonneg hs_nonneg
    rcases ( by omega : (f b = 1 ∧ ∑ a ∈ s, f a = 0) ∨ (f b = 0 ∧ ∑ a ∈ s, f a = 1) ) with
      ⟨hb1, hs0⟩ | ⟨hb0, hs1⟩
    · refine ⟨b, Finset.mem_insert_self b s, ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | has
      · simp [hb1]
      · have hab : a ≠ b := fun h => hbs (h ▸ has)
        rw [if_neg hab]
        have hle : f a ≤ ∑ x ∈ s, f x := Finset.single_le_sum hs_nonneg has
        have hge : 0 ≤ f a := hs_nonneg a has
        omega
    · obtain ⟨a₀, ha₀, hfa⟩ := ih hs_nonneg hs1
      refine ⟨a₀, Finset.mem_insert_of_mem ha₀, ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | has
      · have hba : a ≠ a₀ := fun h => hbs (h ▸ ha₀)
        rw [if_neg hba, hb0]
      · exact hfa a has

private lemma ofReal_sum_of_nonneg {α : Type*} {S : Finset α} {f : α → ℝ}
    (hf : ∀ a ∈ S, 0 ≤ f a) :
    ENNReal.ofReal (∑ a ∈ S, f a) = ∑ a ∈ S, ENNReal.ofReal (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    have hb : 0 ≤ f b := hf b (Finset.mem_insert_self b s)
    have hs : ∀ a ∈ s, 0 ≤ f a := fun a ha => hf a (Finset.mem_insert_of_mem ha)
    rw [Finset.sum_insert hbs, Finset.sum_insert hbs,
        ENNReal.ofReal_add hb (Finset.sum_nonneg hs), ih hs]

private def cutOfThreshold {n : ℕ} (I : Instance n) (τ : Fin (n + 1) → ℤ) : Set (Node n) :=
  {Node.a} ∪ {u | ∃ j t, u = Node.v j t ∧ I.earliest j ≤ t ∧ t ≤ τ j}

private lemma node_v_mem_cutOfThreshold {n : ℕ} (I : Instance n) (τ : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) (t : ℤ) :
    Node.v j t ∈ cutOfThreshold I τ ↔ I.earliest j ≤ t ∧ t ≤ τ j := by
  unfold cutOfThreshold
  simp only [Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, Set.mem_ofPred,
    Node.v.injEq, false_or]
  constructor
  · rintro ⟨j', t', ⟨rfl, rfl⟩, h⟩
    exact h
  · intro h
    exact ⟨j, t, ⟨rfl, rfl⟩, h⟩

private lemma assign_mem_A_iff {n : ℕ} (I : Instance n) (j : Fin (n + 1)) (t : ℤ) :
    Arc.assign j t ∈ I.A ↔ I.earliest j ≤ t ∧ t ≤ I.latest j := by
  unfold Instance.A
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, Arc.assign.injEq,
    reduceCtorEq, and_false, exists_false, or_false]
  constructor
  · rintro ⟨j', t', ht', rfl, rfl⟩
    exact ht'
  · intro ht
    exact ⟨j, t, ht, rfl, rfl⟩

private lemma assign_inCut_cutOfThreshold_iff {n : ℕ} (I : Instance n)
    {τ : Fin (n + 1) → ℤ} (hτ : ∀ j, I.earliest j ≤ τ j ∧ τ j ≤ I.latest j)
    (j : Fin (n + 1)) (t : ℤ) :
    (Arc.assign j t ∈ I.A ∧ I.InCut (cutOfThreshold I τ) (Arc.assign j t)) ↔ t = τ j := by
  have ⟨he_τ, hl_τ⟩ := hτ j
  rw [assign_mem_A_iff]
  unfold Instance.InCut Instance.tail Instance.head
  rw [node_v_mem_cutOfThreshold]
  constructor
  · rintro ⟨⟨he_t, hl_t⟩, ⟨_, ht_le⟩, ⟨_, hnot_mem⟩⟩
    rw [node_v_mem_cutOfThreshold] at hnot_mem
    omega
  · rintro rfl
    refine ⟨⟨he_τ, hl_τ⟩, ⟨he_τ, le_rfl⟩, ⟨?_, ?_⟩⟩
    · exact Or.inr ⟨j, τ j + 1, rfl, by omega, by omega⟩
    · rw [node_v_mem_cutOfThreshold]
      omega

private lemma isNCut_cutOfThreshold {n : ℕ} (I : Instance n)
    {τ : Fin (n + 1) → ℤ} (hτ : ∀ j, I.earliest j ≤ τ j ∧ τ j ≤ I.latest j) :
    I.IsNCut (cutOfThreshold I τ) := by
  refine ⟨⟨?_, Or.inl rfl, ?_⟩, ?_⟩
  · rintro u (rfl | ⟨j, t, rfl, he, ht⟩)
    · exact Or.inl (Or.inl rfl)
    · have ⟨_, hl_τ⟩ := hτ j
      exact Or.inr ⟨j, t, rfl, he, by omega⟩
  · unfold cutOfThreshold
    simp
  · intro j
    refine ⟨τ j, (assign_inCut_cutOfThreshold_iff I hτ j (τ j)).mpr rfl, ?_⟩
    intro t ht
    exact (assign_inCut_cutOfThreshold_iff I hτ j t).mp ht

theorem solution {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    ∀ x, I.IPFeasible x →
      ∃ X, I.IsNCut X ∧ I.cutCap X < ⊤ ∧ I.xOfCut X = x ∧
        I.cutCap X = ENNReal.ofReal (I.cost x) := by
  classical
  intro x hx
  have hex : ∀ j, ∃ t₀ ∈ Finset.range (I.T + 1),
      (I.earliest j ≤ (t₀ : ℤ) ∧ (t₀ : ℤ) ≤ I.latest j) ∧
      ∀ t : ℕ, x j t = if t = t₀ then 1 else 0 := by
    intro j
    obtain ⟨t₀, ht₀_mem, ht₀_eq⟩ := sum_eq_one_of_nonneg (hx.2.2.1 j) (hx.1 j)
    have hbounds : I.earliest j ≤ (t₀ : ℤ) ∧ (t₀ : ℤ) ≤ I.latest j := by
      by_contra hnot
      have hx0 : x j t₀ = 0 := hx.2.2.2 j t₀ (by omega)
      have hx1 : x j t₀ = 1 := by
        simpa using ht₀_eq t₀ ht₀_mem
      omega
    refine ⟨t₀, ht₀_mem, hbounds, ?_⟩
    intro t
    by_cases ht : t ∈ Finset.range (I.T + 1)
    · exact ht₀_eq t ht
    · have ⟨_, _, hl_T⟩ := earliest_latest_bounds I hfeas j
      rw [Finset.mem_range] at ht ht₀_mem
      have hne : t ≠ t₀ := by omega
      rw [if_neg hne]
      exact hx.2.2.2 j t (Or.inr (by omega))
  choose t₀ ht₀_range ht₀_bounds hx_eq using hex
  let X := cutOfThreshold I (fun j => (t₀ j : ℤ))
  have hncut : I.IsNCut X := isNCut_cutOfThreshold I ht₀_bounds
  have hxOfCut : I.xOfCut X = x := by
    ext j t
    unfold Instance.xOfCut
    rw [hx_eq j t]
    have hiff : (Arc.assign j (t : ℤ) ∈ I.A ∧ I.InCut X (Arc.assign j (t : ℤ))) ↔ t = t₀ j := by
      rw [assign_inCut_cutOfThreshold_iff I ht₀_bounds j (t : ℤ)]
      omega
    by_cases h : t = t₀ j
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (mt hiff.mp h), if_neg h]
  have hfilter_eq :
      I.A.filter (fun α => I.InCut X α) = Finset.univ.image (fun j => Arc.assign j (t₀ j : ℤ)) := by
    ext α
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hαA, hin⟩
      rcases α with ⟨j, t⟩ | ⟨ij₀, t_arc⟩ | ⟨j⟩ | ⟨j⟩
      · have ht : t = (t₀ j : ℤ) := (assign_inCut_cutOfThreshold_iff I ht₀_bounds j t).mp ⟨hαA, hin⟩
        exact ⟨j, Finset.mem_univ j, by rw [ht]⟩
      · exfalso
        unfold Instance.A at hαA
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
          Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, reduceCtorEq,
          Arc.temporal.injEq, and_false, exists_false, or_false, false_or] at hαA
        obtain ⟨ij, hij, t, ⟨⟨he1, hl1⟩, he2, hl2⟩, rfl, rfl⟩ := hαA
        unfold Instance.InCut Instance.tail Instance.head at hin
        rw [node_v_mem_cutOfThreshold] at hin
        have ht_le_t₀ : t ≤ (t₀ ij.1 : ℤ) := hin.1.2
        have hnot_head : ¬ (I.earliest ij.2 ≤ t + I.d ij.1 ij.2 ∧ t + I.d ij.1 ij.2 ≤ (t₀ ij.2 : ℤ)) := by
          intro hmem
          exact hin.2.2 ((node_v_mem_cutOfThreshold I (fun j => (t₀ j : ℤ)) ij.2 (t + I.d ij.1 ij.2)).mpr hmem)
        have ⟨he0_1, _, hlT_1⟩ := earliest_latest_bounds I hfeas ij.1
        have ht_nonneg : 0 ≤ t := by omega
        have ht_nat_range : t.toNat ∈ Finset.range (I.T + 1) := by
          rw [Finset.mem_range]
          omega
        have hlag := hx.2.1 ij hij t.toNat ht_nat_range
        have hsum1 : ∑ s ∈ Finset.Icc t.toNat I.T, x ij.1 s = 1 := by
          simp_rw [hx_eq ij.1]
          rw [finset_sum_ite_eq_int, if_pos]
          rw [Finset.mem_Icc]
          have ht₀_r := Finset.mem_range.mp (ht₀_range ij.1)
          omega
        have hsum2 : ∑ s ∈ Finset.range ((t.toNat : ℤ) + I.d ij.1 ij.2).toNat, x ij.2 s =
            if t₀ ij.2 ∈ Finset.range ((t.toNat : ℤ) + I.d ij.1 ij.2).toNat then 1 else 0 := by
          simp_rw [hx_eq ij.2]
          exact finset_sum_ite_eq_int _ _
        rw [hsum1, hsum2] at hlag
        have ht₀_not_range : t₀ ij.2 ∉ Finset.range ((t.toNat : ℤ) + I.d ij.1 ij.2).toNat := by
          intro hmem
          rw [if_pos hmem] at hlag
          omega
        rw [Finset.mem_range] at ht₀_not_range
        have ht_cast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht_nonneg
        rw [ht_cast] at ht₀_not_range
        apply hnot_head
        omega
      · exfalso
        unfold Instance.InCut Instance.head at hin
        apply hin.2.2
        rw [node_v_mem_cutOfThreshold]
        exact ⟨le_rfl, (ht₀_bounds j).1⟩
      · exfalso
        unfold Instance.InCut Instance.tail at hin
        rw [node_v_mem_cutOfThreshold] at hin
        have ⟨_, hl_τ⟩ := ht₀_bounds j
        omega
    · rintro ⟨j, _, rfl⟩
      exact (assign_inCut_cutOfThreshold_iff I ht₀_bounds j (t₀ j : ℤ)).mpr rfl
  have hcap_eq : I.cutCap X = ENNReal.ofReal (I.cost x) := by
    unfold Instance.cutCap
    rw [hfilter_eq, Finset.sum_image]
    · have hcost_eq : I.cost x = ∑ j : Fin (n + 1), I.w j (t₀ j) := by
        unfold Instance.cost
        refine Finset.sum_congr rfl fun j _ => ?_
        have hterm : ∀ t : ℕ, I.w j t * (x j t : ℝ) = if t = t₀ j then I.w j t else 0 := by
          intro t
          rw [hx_eq j t]
          split_ifs <;> simp
        simp_rw [hterm]
        rw [finset_sum_ite_eq, if_pos (ht₀_range j)]
      rw [hcost_eq, ofReal_sum_of_nonneg (fun j _ => hw j (t₀ j))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Instance.cap]
    · intro j₁ _ j₂ _ h
      exact (Arc.assign.injEq _ _ _ _ ▸ h).1
  refine ⟨X, hncut, ?_, hxOfCut, hcap_eq⟩
  rw [hcap_eq]
  exact ENNReal.ofReal_lt_top
