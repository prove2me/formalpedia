-- Prove2me | solution 1 for SatiationFisherNSW.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:34:58.963588+00:00
-- url     : https://prove2.me/submissions/6fb30f10-fa7a-4686-a226-671810516eb2

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
import Definitions.Def_SatiationFisherNSW_RoundingRun
open scoped Classical

open SatiationFisherNSW in
theorem solution
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p)
    (R : RoundingRun B G) (hR : R.IsValid I.market x p)
    (T : (R.ppGraph I.market x p).ConnectedComponent) (hT : R.IsZeroPriceTree I.market x p T) :
    (R.agentsOf I.market x p T).card = (R.remainingGoodsOf I.market x p T).card + 1 := by
  obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8⟩ := hR
  obtain ⟨rk, hrk1, hrk2⟩ := hv4
  -- kept children are children
  have hkc : ∀ j a, R.keptChild I.market x p j = some a → R.parentGood a = some j := by
    intro j a h
    unfold RoundingRun.keptChild at h
    rcases hlc : R.largestChild j with _ | a'
    · rw [hlc] at h; simp at h
    · rw [hlc] at h
      simp only at h
      split_ifs at h with hk
      all_goals (first | (cases h; exact (hv5 j _ hlc).1) | (cases h))
  -- the parent map of the rooted forest
  obtain ⟨par, hpar⟩ : ∃ par : B ⊕ G → Option (B ⊕ G), par = fun v => Sum.elim
      (fun a => match R.parentGood a with
        | none => none
        | some j => if R.keptChild I.market x p j = some a then some (Sum.inr j) else none)
      (fun j => (R.parentAgent j).map Sum.inl) v := ⟨_, rfl⟩
  have hpar_l : ∀ a v, par (Sum.inl a) = some v ↔
      ∃ j, R.parentGood a = some j ∧ R.keptChild I.market x p j = some a ∧ v = Sum.inr j := by
    intro a v
    rw [hpar]
    simp only [Sum.elim_inl]
    rcases h : R.parentGood a with _ | j
    · simp
    · simp only
      by_cases hk : R.keptChild I.market x p j = some a
      · rw [if_pos hk]
        constructor
        · intro h'; exact ⟨j, rfl, hk, (Option.some_injective _ h').symm⟩
        · rintro ⟨j', hj', -, rfl⟩
          cases Option.some_injective _ hj'
          rfl
      · rw [if_neg hk]
        constructor
        · intro h'; simp at h'
        · rintro ⟨j', hj', hk', -⟩
          cases Option.some_injective _ hj'
          exact absurd hk' hk
  have hpar_r : ∀ j v, par (Sum.inr j) = some v ↔ ∃ i, R.parentAgent j = some i ∧ v = Sum.inl i := by
    intro j v
    rw [hpar]
    simp only [Sum.elim_inr]
    rcases h : R.parentAgent j with _ | i
    · simp
    · simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro h'; exact ⟨i, rfl, h'.symm⟩
      · rintro ⟨i', hi', rfl⟩
        rw [hi']
  have hdec : ∀ u v, par u = some v → rk v < rk u := by
    intro u v h
    rcases u with a | j
    · obtain ⟨j, hj, -, rfl⟩ := (hpar_l a v).mp h
      exact hrk2 a j hj
    · obtain ⟨i, hi, rfl⟩ := (hpar_r j v).mp h
      exact hrk1 i j hi
  -- existence and uniqueness of terminal ancestors
  have hexists : ∀ n, ∀ v, rk v = n →
      ∃ r, Relation.ReflTransGen (fun a b => par a = some b) v r ∧ par r = none := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      rcases hpv : par v with _ | w
      · exact ⟨v, Relation.ReflTransGen.refl, hpv⟩
      · obtain ⟨r, hr, hr0⟩ := ih (rk w) (by rw [← hv]; exact hdec v w hpv) w rfl
        exact ⟨r, Relation.ReflTransGen.head hpv hr, hr0⟩
  have huniq : ∀ v r1, Relation.ReflTransGen (fun a b => par a = some b) v r1 → par r1 = none →
      ∀ r2, Relation.ReflTransGen (fun a b => par a = some b) v r2 → par r2 = none → r2 = r1 := by
    intro v r1 h1 t1
    induction h1 using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro r2 h2 t2
      rcases Relation.ReflTransGen.cases_head h2 with h | ⟨c, hc, -⟩
      · exact h.symm
      · rw [t1] at hc; cases hc
    | head hac _ ih =>
      intro r2 h2 t2
      rcases Relation.ReflTransGen.cases_head h2 with h | ⟨c', hc', hc'r⟩
      · subst h
        rw [t2] at hac; cases hac
      · rw [hac] at hc'
        cases hc'
        exact ih r2 hc'r t2
  obtain ⟨root, hroot⟩ : ∃ root : B ⊕ G → B ⊕ G, ∀ v,
      Relation.ReflTransGen (fun a b => par a = some b) v (root v) ∧ par (root v) = none :=
    ⟨fun v => Classical.choose (hexists (rk v) v rfl),
      fun v => Classical.choose_spec (hexists (rk v) v rfl)⟩
  have hroot_par : ∀ u v, par u = some v → root u = root v := by
    intro u v h
    exact (huniq u (root u) (hroot u).1 (hroot u).2 (root v)
      (Relation.ReflTransGen.head h (hroot v).1) (hroot v).2).symm
  have hroot_self : ∀ v, par v = none → root v = v := by
    intro v h
    exact huniq v v Relation.ReflTransGen.refl h (root v) (hroot v).1 (hroot v).2
  have hadj_root : ∀ u v, (R.ppGraph I.market x p).Adj u v → root u = root v := by
    intro u v h
    unfold RoundingRun.ppGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    obtain ⟨-, h1 | h1⟩ := h
    · rcases u with i | j <;> rcases v with i' | j'
      · exact absurd h1 (by simp)
      · rcases h1 with h1 | h1
        · exact (hroot_par _ _ ((hpar_r j' (Sum.inl i)).mpr ⟨i, h1, rfl⟩)).symm
        · exact hroot_par _ _ ((hpar_l i (Sum.inr j')).mpr ⟨j', hkc j' i h1, h1, rfl⟩)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
    · rcases u with i | j <;> rcases v with i' | j'
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · rcases h1 with h1 | h1
        · exact hroot_par _ _ ((hpar_r j (Sum.inl i')).mpr ⟨i', h1, rfl⟩)
        · exact (hroot_par _ _ ((hpar_l i' (Sum.inr j)).mpr ⟨j, hkc j i' h1, h1, rfl⟩)).symm
      · exact absurd h1 (by simp)
  have hreach_root : ∀ u v, (R.ppGraph I.market x p).Reachable u v → root u = root v := by
    intro u v h
    obtain ⟨w⟩ := h
    induction w with
    | nil => rfl
    | cons hadj _ ih => exact (hadj_root _ _ hadj).trans ih
  have hpar_adj : ∀ u v, par u = some v → (R.ppGraph I.market x p).Adj u v := by
    intro u v h
    unfold RoundingRun.ppGraph
    rw [SimpleGraph.fromRel_adj]
    rcases u with a | j
    · obtain ⟨j, -, hk, rfl⟩ := (hpar_l a v).mp h
      exact ⟨by simp, Or.inl (Or.inr hk)⟩
    · obtain ⟨i, hi, rfl⟩ := (hpar_r j v).mp h
      exact ⟨by simp, Or.inr (Or.inl hi)⟩
  have hrtg_reach : ∀ u v, Relation.ReflTransGen (fun a b => par a = some b) u v →
      (R.ppGraph I.market x p).Reachable u v := by
    intro u v h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hbc ih => exact ih.trans (hpar_adj _ _ hbc).reachable
  have hroot_iff : ∀ a, par (Sum.inl a) = none ↔ R.IsPPRoot I.market x p a := by
    intro a
    constructor
    · intro h j hj hk
      have := (hpar_l a (Sum.inr j)).mpr ⟨j, hj, hk, rfl⟩
      rw [h] at this; cases this
    · intro h
      rcases hp : par (Sum.inl a) with _ | v
      · rfl
      · obtain ⟨j, hj, hk, -⟩ := (hpar_l a v).mp hp
        exact absurd hk (h j hj)
  -- the common root of the component
  obtain ⟨a0, ha0⟩ := hT.1
  have ha0T : (R.ppGraph I.market x p).connectedComponentMk (Sum.inl a0) = T := by
    simpa [RoundingRun.agentsOf] using ha0
  have hroot_agent : ∃ r0, root (Sum.inl a0) = Sum.inl r0 := by
    rcases h : root (Sum.inl a0) with r0 | j
    · exact ⟨r0, rfl⟩
    · exfalso
      have h1 := (hroot (Sum.inl a0)).1
      have h2 := (hroot (Sum.inl a0)).2
      rw [h] at h1 h2
      rcases Relation.ReflTransGen.cases_tail h1 with h3 | ⟨c, -, hc⟩
      · cases h3
      · rcases c with a' | j'
        · obtain ⟨j'', hpg, -, hj⟩ := (hpar_l a' (Sum.inr j)).mp hc
          cases hj
          have hx : 0 < x a' j := (hv1 a' j).mpr (Or.inr hpg)
          obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hv3 j ⟨a', hx⟩)
          have := (hpar_r j (Sum.inl i)).mpr ⟨i, hi, rfl⟩
          rw [h2] at this; cases this
        · obtain ⟨i, -, hi⟩ := (hpar_r j' (Sum.inr j)).mp hc
          cases hi
  obtain ⟨r0, hr0⟩ := hroot_agent
  have hmemA : ∀ a, a ∈ R.agentsOf I.market x p T ↔
      (R.ppGraph I.market x p).connectedComponentMk (Sum.inl a) = T := by
    intro a; simp [RoundingRun.agentsOf]
  have hroot_A : ∀ a, a ∈ R.agentsOf I.market x p T → root (Sum.inl a) = Sum.inl r0 := by
    intro a ha
    rw [← hr0]
    apply hreach_root
    apply SimpleGraph.ConnectedComponent.exact
    rw [(hmemA a).mp ha, ha0T]
  have hr0A : r0 ∈ R.agentsOf I.market x p T := by
    rw [hmemA, ← ha0T]
    apply SimpleGraph.ConnectedComponent.sound
    have := hrtg_reach _ _ (hroot (Sum.inl a0)).1
    rw [hr0] at this
    exact this.symm
  have hr0root : R.IsPPRoot I.market x p r0 := by
    rw [← hroot_iff]
    have := (hroot (Sum.inl a0)).2
    rwa [hr0] at this
  have hrootA_iff : ∀ a ∈ R.agentsOf I.market x p T, R.IsPPRoot I.market x p a ↔ a = r0 := by
    intro a ha
    constructor
    · intro h
      have h1 := hroot_self _ ((hroot_iff a).mpr h)
      rw [hroot_A a ha] at h1
      exact (Sum.inl_injective h1).symm
    · rintro rfl; exact hr0root
  -- counting
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := R.agentsOf I.market x p T) (fun a => R.IsPPRoot I.market x p a)
  have hroots : (R.agentsOf I.market x p T).filter (fun a => R.IsPPRoot I.market x p a) = {r0} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hroot'⟩; exact (hrootA_iff a ha).mp hroot'
    · rintro rfl; exact ⟨hr0A, hr0root⟩
  rw [hroots, Finset.card_singleton] at hsplit
  have hbij : (R.remainingGoodsOf I.market x p T).card =
      ((R.agentsOf I.market x p T).filter (fun a => ¬ R.IsPPRoot I.market x p a)).card := by
    apply Finset.card_bij (fun j hj => Option.get (R.keptChild I.market x p j)
      (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hj).2))
    · intro j hj
      have hjT : (R.ppGraph I.market x p).connectedComponentMk (Sum.inr j) = T := by
        have := (Finset.mem_filter.mp hj).1
        simpa [RoundingRun.goodsOf] using this
      set a := Option.get (R.keptChild I.market x p j)
        (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hj).2) with ha_def
      have hka : R.keptChild I.market x p j = some a := by rw [ha_def]; simp
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hmemA, ← hjT]
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        exact hpar_adj _ _ ((hpar_l a (Sum.inr j)).mpr ⟨j, hkc j a hka, hka, rfl⟩)
      · intro hroot'
        exact hroot' j (hkc j a hka) hka
    · intro j1 hj1 j2 hj2 h
      have h1 : R.keptChild I.market x p j1 = some (Option.get _
          (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hj1).2)) := by simp
      have h2 : R.keptChild I.market x p j2 = some (Option.get _
          (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hj2).2)) := by simp
      rw [h] at h1
      have e1 := hkc j1 _ h1
      have e2 := hkc j2 _ h2
      rw [e1] at e2
      exact Option.some_injective _ e2
    · intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haA, hnr⟩ := ha
      unfold RoundingRun.IsPPRoot at hnr
      push_neg at hnr
      obtain ⟨j, hj, hk⟩ := hnr
      have hjR : j ∈ R.remainingGoodsOf I.market x p T := by
        unfold RoundingRun.remainingGoodsOf RoundingRun.goodsOf
        rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, ?_⟩, by rw [hk]; simp⟩
        rw [← (hmemA a).mp haA]
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        exact (hpar_adj _ _ ((hpar_l a (Sum.inr j)).mpr ⟨j, hj, hk, rfl⟩)).symm
      exact ⟨j, hjR, Option.some_injective _ ((Option.some_get _).trans hk)⟩
  omega
