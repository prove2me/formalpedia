-- Prove2me | solution 1 for SatiationFisherNSW.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:39:28.333565+00:00
-- url     : https://prove2.me/submissions/55349e4e-67dc-409a-9ff4-9cbf03317e3b

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
    (T : (R.ppGraph I.market x p).ConnectedComponent) (hT : R.IsPriceTree I.market x p T) :
    (R.agentsOf I.market x p T).card = (R.remainingGoodsOf I.market x p T).card + 1 ∧
    ∀ i ∈ R.agentsOf I.market x p T, ∀ j, R.parentAgent j = some i →
      R.keptChild I.market x p j = none → 1 < p j →
        p j * x i j = 1 ∧ (∀ i', i' ≠ i → p j * x i' j = 0) ∧
        I.val i (R.output I.market x p) = p j ∧
        ∀ a ∈ R.agentsOf I.market x p T, ¬ I.market.IsCapped x a := by
  obtain ⟨hp0, hsup, hbuy, hcs⟩ := hEq
  have hc : ∀ i, I.market.c i = I.c i := fun i => rfl
  have hm : ∀ i, I.market.m i = 1 := fun i => rfl
  have hd : ∀ j, I.market.d j = 1 := fun j => rfl
  have hes : ∀ j, I.market.modestSupply p j = if p j = 0 then 1 else min 1 (1 / p j) := by
    intro j
    unfold FisherMarket.modestSupply
    rw [hd]
  have hu0 : ∀ i j, 0 ≤ I.market.u i j := I.market.u_nonneg
  have huc : ∀ i j, I.market.u i j ≤ I.c i := fun i j => min_le_right _ _
  have hcpos := I.c_pos
  -- ratio facts for buyers outside `B₀`
  have hratio : ∀ i, ¬ I.market.InB0 p i →
      (∀ k, I.market.u i k ≤ p k) ∧ (∃ k, 0 < p k ∧ I.market.u i k = p k) := by
    intro i hi
    have hn := hN i hi
    unfold FisherMarket.mbbRatio at hn
    have hbdd : BddAbove (Set.range fun k => I.market.u i k / p k) :=
      (Set.finite_range _).bddAbove
    rcases isEmpty_or_nonempty G with hG | hG
    · exfalso
      rw [Real.iSup_of_isEmpty] at hn
      norm_num at hn
    constructor
    · intro k
      have h1 : I.market.u i k / p k ≤ 1 := by
        rw [← hn]
        exact le_ciSup hbdd k
      by_cases hpk : p k = 0
      · have hnot : ¬ (0 < I.market.u i k) := fun h => hi ⟨k, hpk, h⟩
        have h2 := hu0 i k
        rw [hpk]
        linarith [not_lt.mp hnot]
      · have hpk' : 0 < p k := lt_of_le_of_ne (hp0 k) (Ne.symm hpk)
        rwa [div_le_one hpk'] at h1
    · obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => I.market.u i k / p k)
      rw [hn] at hk
      have hpk : p k ≠ 0 := by
        intro h
        rw [h, div_zero] at hk
        norm_num at hk
      have hpk' : 0 < p k := lt_of_le_of_ne (hp0 k) (Ne.symm hpk)
      refine ⟨k, hpk', ?_⟩
      rwa [div_eq_one_iff_eq hpk] at hk
  -- MBB goods of a buyer outside `B₀` satisfy `u = p > 0`
  have hmbb_eq : ∀ i j, ¬ I.market.InB0 p i → I.market.IsMBB p i j →
      I.market.u i j = p j ∧ 0 < p j := by
    intro i j hi hmbb
    obtain ⟨hle, k, hpk, hk⟩ := hratio i hi
    obtain ⟨hpos, hcmp⟩ := hmbb
    have hpj : 0 < p j := by
      rcases (hp0 j).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨j, h.symm, hpos⟩ hi
    have h1 := hcmp k
    rw [hk] at h1
    have h2 : p j ≤ I.market.u i j := by nlinarith
    exact ⟨le_antisymm (hle j) h2, hpj⟩
  -- MBB goods of a buyer in `B₀` have price zero
  have hmbb_B0 : ∀ i j, I.market.InB0 p i → I.market.IsMBB p i j → p j = 0 := by
    intro i j hi hmbb
    obtain ⟨j0, hj0, hpos0⟩ := hi
    obtain ⟨hpos, hcmp⟩ := hmbb
    have h1 := hcmp j0
    rw [hj0, mul_zero] at h1
    have := hp0 j
    nlinarith
  -- part (a)
  have ha : ∀ i, ¬ I.market.InB0 p i →
      ∑ j, p j * x i j = min 1 (I.c i) ∧ I.market.utility i (x i) = min 1 (I.c i) ∧
        (I.market.IsCapped x i → I.c i ≤ 1) := by
    intro i hi
    obtain ⟨hdem, hthr, hmod⟩ := hbuy i
    obtain ⟨hx0, hbud, hopt⟩ := hdem
    obtain ⟨hle, k, hpk, hk⟩ := hratio i hi
    have hTS : ∑ j, I.market.u i j * x i j = ∑ j, p j * x i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rcases (hx0 j).lt_or_eq with h | h
      · rw [(hmbb_eq i j hi (hthr j h)).1]
      · rw [← h]; simp
    rw [hm] at hbud
    obtain ⟨z, hz⟩ : ∃ z : G → ℝ, z = fun j => if j = k then 1 / p k else 0 := ⟨_, rfl⟩
    have hz0 : ∀ j, 0 ≤ z j := by
      intro j; rw [hz]; dsimp only; split_ifs <;> positivity
    have hzcost : ∑ j, p j * z j = 1 := by
      rw [hz]
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [hpk.ne']
    have hzu : ∑ j, I.market.u i j * z j = 1 := by
      rw [hz]
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [hk, hpk.ne']
    have hopt' := hopt z hz0 (by rw [hzcost, hm])
    have hT : ∑ j, I.market.u i j * x i j ≤ I.c i := hmod
    unfold FisherMarket.utility at hopt'
    rw [hzu] at hopt'
    try rw [hc] at hopt'
    obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ∑ j, I.market.u i j * x i j := ⟨_, rfl⟩
    rw [← hTdef] at hopt' hT
    rw [← hTdef] at hTS
    have hT1 : T ≤ 1 := by rw [hTS]; exact hbud
    have hmin : min (I.c i) T = T := min_eq_right hT
    rw [hmin] at hopt'
    have hTeq : T = min 1 (I.c i) := by
      apply le_antisymm (le_min hT1 hT)
      rw [min_comm]
      exact hopt'
    have hutil : I.market.utility i (x i) = min 1 (I.c i) := by
      unfold FisherMarket.utility
      try rw [hc]
      rw [← hTdef, hmin, hTeq]
    refine ⟨by rw [← hTS, hTeq], hutil, ?_⟩
    intro hcap
    unfold FisherMarket.IsCapped at hcap
    rw [hutil] at hcap
    try rw [hc] at hcap
    rw [← hcap]
    exact min_le_left _ _
  -- part (e) of Lemma 4.3: money flowing into goods
  have he : ∀ j, p j * ∑ i, x i j = min (p j) 1 := by
    intro j
    rcases (hp0 j).lt_or_eq with hpj | hpj
    · have h := hcs j
      rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · have hsum : ∑ i, x i j = min 1 (1 / p j) := by
          rw [hes, if_neg hpj.ne'] at h'
          linarith
        rw [hsum, mul_min_of_nonneg _ _ hpj.le, mul_one, mul_one_div_cancel hpj.ne', min_comm]
    · rw [← hpj, zero_mul]
      exact (min_eq_left zero_le_one).symm
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
  have hmemA : ∀ a, a ∈ R.agentsOf I.market x p T ↔
      (R.ppGraph I.market x p).connectedComponentMk (Sum.inl a) = T := by
    intro a; simp [RoundingRun.agentsOf]
  constructor
  · -- the common root of the component
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
  · intro i hiT j hpa hkn hpj
    have hnb : ¬ I.market.InB0 p i := hT.2 i hiT
    have hpj0 : 0 < p j := by linarith
    have hx0' : ∀ i j, 0 ≤ x i j := fun i j => (hbuy i).1.1 j
    -- `j` has no child agent
    have hnochild : ∀ i', R.parentGood i' ≠ some j := by
      intro i' hi'
      have hne : R.keptChild I.market x p j ≠ none := by
        unfold RoundingRun.keptChild
        rcases hlc : R.largestChild j with _ | a
        · exact absurd hi' (hv6 j hlc i')
        · simp only
          have hk : RoundingRun.KeepCond I.market x p a j := by
            unfold RoundingRun.KeepCond
            rw [if_neg hpj0.ne']
            have h1 : I.market.activeBudget p a ≤ 1 := min_le_left _ _
            linarith
          rw [if_pos hk]
          exact Option.some_ne_none a
      exact hne hkn
    have hother : ∀ i', i' ≠ i → x i' j = 0 := by
      intro i' hne
      rcases (hx0' i' j).lt_or_eq with h | h
      · rcases (hv1 i' j).mp h with h1 | h1
        · rw [hpa] at h1
          exact absurd (Option.some_injective _ h1).symm hne
        · exact absurd h1 (hnochild i')
      · exact h.symm
    have hsumx : ∑ i', x i' j = x i j := by
      rw [Finset.sum_eq_single i]
      · intro i' _ hne; exact hother i' hne
      · intro h; exact absurd (Finset.mem_univ i) h
    have hpx : p j * x i j = 1 := by
      rw [← hsumx, he j, min_eq_right hpj.le]
    have hxij : 0 < x i j := by
      by_contra hneg
      push_neg at hneg
      have : x i j = 0 := le_antisymm hneg (hx0' i j)
      rw [this, mul_zero] at hpx
      norm_num at hpx
    obtain ⟨hdem, hthr, hmod⟩ := hbuy i
    obtain ⟨hug, -⟩ := hmbb_eq i j hnb (hthr j hxij)
    have hpc : p j ≤ I.c i := by rw [← hug]; exact huc i j
    have hc1 : 1 < I.c i := by linarith
    -- `i` buys nothing else
    obtain ⟨hspend, hutil, -⟩ := ha i hnb
    have honly : ∀ j', j' ≠ j → x i j' = 0 := by
      intro j' hne
      by_contra hpos
      have hpos' : 0 < x i j' := lt_of_le_of_ne (hx0' i j') (Ne.symm hpos)
      obtain ⟨-, hpj'⟩ := hmbb_eq i j' hnb (hthr j' hpos')
      have h1 : p j * x i j + p j' * x i j' ≤ ∑ k, p k * x i k := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({j, j'} : Finset G))
          (fun k _ _ => mul_nonneg (hp0 k) (hx0' i k))
        rw [Finset.sum_pair (Ne.symm hne)] at this
        exact this
      rw [hspend, min_eq_left hc1.le, hpx] at h1
      have : 0 < p j' * x i j' := mul_pos hpj' hpos'
      linarith
    -- the output gives `i` exactly the good `j`
    have hout_j : R.output I.market x p j = some i := by
      unfold RoundingRun.output
      rw [hpa]
      simp only [hkn]
    have hout_other : ∀ j', j' ≠ j → R.output I.market x p j' ≠ some i := by
      intro j' hne hout
      unfold RoundingRun.output at hout
      rcases hpa' : R.parentAgent j' with _ | b
      · rw [hpa'] at hout; simp at hout
      · rw [hpa'] at hout
        have hb : b ≠ i := by
          rintro rfl
          have := (hv1 b j').mpr (Or.inl hpa')
          rw [honly j' hne] at this
          exact lt_irrefl 0 this
        rcases hkc' : R.keptChild I.market x p j' with _ | a
        · rw [hkc'] at hout
          simp only [Option.some.injEq] at hout
          exact hb hout
        · rw [hkc'] at hout
          simp only at hout
          have ha' : a ≠ i := by
            rintro rfl
            have := (hv1 a j').mpr (Or.inr (hkc j' a hkc'))
            rw [honly j' hne] at this
            exact lt_irrefl 0 this
          split_ifs at hout
          · exact hb (Option.some_injective _ hout)
          · exact ha' (Option.some_injective _ hout)
    have hfilt : Finset.univ.filter (fun j' => R.output I.market x p j' = some i) = {j} := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        by_contra hne
        exact hout_other j' hne h
      · rintro rfl; exact hout_j
    have hval : I.val i (R.output I.market x p) = p j := by
      unfold NSWInstance.val
      rw [hfilt, Finset.sum_singleton]
      have hv : I.v i j = p j := by rw [← hug]; exact (min_eq_left (hvc i j)).symm
      rw [hv]
      exact min_eq_right hpc
    refine ⟨hpx, fun i' hne => by rw [hother i' hne, mul_zero], hval, ?_⟩
    -- the component is `{i, j}`
    intro a haT hcap
    have hclosed : ∀ u v, (R.ppGraph I.market x p).Adj u v →
        (u = Sum.inl i ∨ u = Sum.inr j) → (v = Sum.inl i ∨ v = Sum.inr j) := by
      intro u v h hu
      unfold RoundingRun.ppGraph at h
      rw [SimpleGraph.fromRel_adj] at h
      obtain ⟨-, h1⟩ := h
      rcases hu with rfl | rfl
      · rcases v with i' | j'
        · rcases h1 with h1 | h1 <;> exact absurd h1 (by simp)
        · right
          have hx : 0 < x i j' := by
            rcases h1 with h1 | h1
            · rcases h1 with h1 | h1
              · exact (hv1 i j').mpr (Or.inl h1)
              · exact (hv1 i j').mpr (Or.inr (hkc j' i h1))
            · exact absurd h1 (by simp)
          by_contra hne
          have hne' : j' ≠ j := fun e => hne (by rw [e])
          rw [honly j' hne'] at hx
          exact lt_irrefl 0 hx
      · rcases v with i' | j'
        · left
          have h2 : R.parentAgent j = some i' ∨ R.keptChild I.market x p j = some i' := by
            rcases h1 with h1 | h1
            · exact absurd h1 (by simp)
            · exact h1
          rcases h2 with h2 | h2
          · rw [hpa] at h2
            rw [Option.some_injective _ h2]
          · rw [hkn] at h2; cases h2
        · rcases h1 with h1 | h1 <;> exact absurd h1 (by simp)
    have hreachS : ∀ u v, (R.ppGraph I.market x p).Reachable u v →
        (u = Sum.inl i ∨ u = Sum.inr j) → (v = Sum.inl i ∨ v = Sum.inr j) := by
      intro u v h hu
      obtain ⟨w⟩ := h
      induction w with
      | nil => exact hu
      | cons hadj _ ih => exact ih (hclosed _ _ hadj hu)
    have hai : a = i := by
      have hr : (R.ppGraph I.market x p).Reachable (Sum.inl i) (Sum.inl a) := by
        apply SimpleGraph.ConnectedComponent.exact
        rw [(hmemA i).mp hiT, (hmemA a).mp haT]
      rcases hreachS _ _ hr (Or.inl rfl) with h | h
      · exact (Sum.inl_injective h)
      · cases h
    subst hai
    have hcap' : min (I.c a) (∑ k, I.market.u a k * x a k) = I.c a := hcap
    have hutil' : min (I.c a) (∑ k, I.market.u a k * x a k) = min 1 (I.c a) := hutil
    rw [hutil', min_eq_left hc1.le] at hcap'
    linarith
