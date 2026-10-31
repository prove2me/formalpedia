-- Prove2me | solution 1 for TradingNetFlow.ChainStable.contraction_blockingChain_lift
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:39:20.258865+00:00
-- url     : https://prove2.me/submissions/95f52ee7-e7e5-4da6-81b6-b9560288909e

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

open Finset TradingNetFlow.ChainStable

/-- Utility in `G` of `S ∪ B` (with `S` outside `X`, `B ⊆ X ∩ δ(i)`) splits into the term of the
maximum defining `ŵ_i(S)` plus the `G^X`-price part of `S`. -/
private lemma utility_split {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (X : Finset E) (pX p : E → ℝ) (hp : ∀ e ∈ X, p e = pX e)
    (q : {e : E // e ∉ X} → ℝ) (hq : ∀ x, q x = p x.1) (i : N)
    (S : Finset {e : E // e ∉ X}) (B : Finset E) (hB : B ⊆ X) :
    G.utility i (S.map (Function.Embedding.subtype _) ∪ B) p
      = (G.w i (S.map (Function.Embedding.subtype _) ∪ B)
          + ∑ e ∈ B ∩ G.deltaOut i, pX e - ∑ e ∈ B ∩ G.deltaIn i, pX e)
        + (∑ e ∈ S ∩ (G.contraction X pX).deltaOut i, q e
          - ∑ e ∈ S ∩ (G.contraction X pX).deltaIn i, q e) := by
  have hdisj : ∀ D : Finset E,
      Disjoint (S.map (Function.Embedding.subtype _) ∩ D) (B ∩ D) := by
    intro D
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨x, -, rfl⟩ := mem_map.1 (mem_inter.1 h1).1
    exact x.2 (hB (mem_inter.1 h2).1)
  have hsum : ∀ (D : Finset E) (DH : Finset {e : E // e ∉ X}),
      (∀ x : {e : E // e ∉ X}, x ∈ DH ↔ x.1 ∈ D) →
      ∑ e ∈ (S.map (Function.Embedding.subtype _) ∪ B) ∩ D, p e
        = ∑ e ∈ B ∩ D, pX e + ∑ e ∈ S ∩ DH, q e := by
    intro D DH hD
    rw [union_inter_distrib_right, sum_union (hdisj D), add_comm]
    congr 1
    · exact sum_congr rfl (fun e he => hp e (hB (mem_inter.1 he).1))
    · have : S.map (Function.Embedding.subtype _) ∩ D
          = (S ∩ DH).map (Function.Embedding.subtype _) := by
        ext e
        simp only [mem_inter, mem_map, Function.Embedding.coe_subtype]
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, h⟩; exact ⟨x, ⟨hx, (hD x).2 h⟩, rfl⟩
        · rintro ⟨x, ⟨hx, h⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, (hD x).1 h⟩
      rw [this, sum_map]
      exact sum_congr rfl (fun x _ => (hq x).symm)
  unfold Economy.utility
  rw [hsum (G.deltaOut i) ((G.contraction X pX).deltaOut i)
      (fun x => by simp [Economy.deltaOut, Economy.contraction]),
    hsum (G.deltaIn i) ((G.contraction X pX).deltaIn i)
      (fun x => by simp [Economy.deltaIn, Economy.contraction])]
  ring

theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (X : Finset E) (pX : E → ℝ)
    (T : Finset {e : E // e ∉ X}) (pT : {e : E // e ∉ X} → ℝ)
    (hT : (G.contraction X pX).IsBlockingChain ∅ pT T pT) :
    G.IsBlockingChain X pX (T.map (Function.Embedding.subtype _))
      (fun e => if h : e ∈ X then 0 else pT ⟨e, h⟩) := by
  obtain ⟨hne, ⟨l, hl0, hlnd, hlT, hlc⟩, -, hblock⟩ := hT
  set H := G.contraction X pX with hH
  set T' := T.map (Function.Embedding.subtype _) with hT'
  set p := joinPrices X pX (fun e => if h : e ∈ X then 0 else pT ⟨e, h⟩) with hp
  set q := joinPrices (∅ : Finset {e : E // e ∉ X}) pT pT with hq
  have hpX : ∀ e ∈ X, p e = pX e := fun e he => by simp [hp, joinPrices, he]
  have hqp : ∀ x, q x = p x.1 := fun x => by simp [hq, hp, joinPrices, x.2]
  -- `Ĥ`-utility is the max over `B` of `G`-utilities
  have hHu_ge : ∀ (i : N) (S : Finset {e : E // e ∉ X}) (B : Finset E), B ∈ (X ∩ G.delta i).powerset →
      G.utility i (S.map (Function.Embedding.subtype _) ∪ B) p ≤ H.utility i S q := by
    intro i S B hB
    rw [utility_split G X pX p hpX q hqp i S B
      ((mem_powerset.1 hB).trans inter_subset_left)]
    unfold Economy.utility
    have := Finset.le_sup' (fun Y =>
      G.w i (S.map (Function.Embedding.subtype _) ∪ Y)
        + ∑ e ∈ Y ∩ G.deltaOut i, pX e - ∑ e ∈ Y ∩ G.deltaIn i, pX e) hB
    simp only [hH, Economy.contraction] at this ⊢
    linarith
  have hHu_eq : ∀ (i : N) (S : Finset {e : E // e ∉ X}), ∃ B ∈ (X ∩ G.delta i).powerset,
      H.utility i S q = G.utility i (S.map (Function.Embedding.subtype _) ∪ B) p := by
    intro i S
    obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup' (⟨∅, Finset.empty_mem_powerset _⟩ :
        ((X ∩ G.delta i).powerset).Nonempty) (fun Y =>
      G.w i (S.map (Function.Embedding.subtype _) ∪ Y)
        + ∑ e ∈ Y ∩ G.deltaOut i, pX e - ∑ e ∈ Y ∩ G.deltaIn i, pX e)
    refine ⟨B, hB, ?_⟩
    rw [utility_split G X pX p hpX q hqp i S B
      ((mem_powerset.1 hB).trans inter_subset_left)]
    unfold Economy.utility
    simp only [hH, Economy.contraction] at hBeq ⊢
    linarith [hBeq]
  refine ⟨hne.map, ⟨l.map Subtype.val, fun h => hl0 (List.map_eq_nil_iff.1 h),
    hlnd.map Subtype.val_injective, ?_, ?_⟩, ?_, ?_⟩
  · rw [hT', ← hlT]; ext e; simp
  · rw [List.isChain_map]
    exact hlc
  · rw [Finset.disjoint_left]
    intro e he
    obtain ⟨x, -, rfl⟩ := mem_map.1 he
    exact x.2
  · intro i hi Y hY
    obtain ⟨hYsub, hYmax⟩ := hY
    -- split `Y` into its parts outside and inside `X`
    set S : Finset {e : E // e ∉ X} := Y.subtype (fun e => e ∉ X) with hS
    have hYeq : S.map (Function.Embedding.subtype _) ∪ Y ∩ X = Y := by
      rw [hS, Finset.subtype_map]; ext e; by_cases h : e ∈ X <;> simp [h]
    have hB0 : Y ∩ X ∈ (X ∩ G.delta i).powerset := by
      rw [mem_powerset]; intro e he
      exact mem_inter.2 ⟨(mem_inter.1 he).2, (mem_inter.1 (hYsub (mem_inter.1 he).1)).2⟩
    have hdeltaH : ∀ x : {e : E // e ∉ X}, x ∈ H.delta i ↔ x.1 ∈ G.delta i := by
      intro x
      simp [hH, Economy.delta, Economy.deltaOut, Economy.deltaIn, Economy.contraction]
    -- `S` is demanded in `G^X`
    have hSdem : S ∈ H.demandOn i (T ∪ ∅) q := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [hS, mem_subtype] at hx
        have h1 := hYsub hx
        rw [mem_inter, mem_union] at h1
        rw [union_empty, mem_inter, hdeltaH]
        refine ⟨?_, h1.2⟩
        rcases h1.1 with h | h
        · obtain ⟨y, hy, hyx⟩ := mem_map.1 h
          have : y = x := Subtype.ext hyx
          exact this ▸ hy
        · exact absurd h x.2
      · intro S' hS'
        obtain ⟨B, hB, hBeq⟩ := hHu_eq i S'
        rw [hBeq]
        have h2 : G.utility i (S'.map (Function.Embedding.subtype _) ∪ B) p ≤ G.utility i Y p := by
          apply hYmax
          intro e he
          rw [mem_union] at he
          rcases he with he | he
          · obtain ⟨x, hx, rfl⟩ := mem_map.1 he
            have := hS' hx
            rw [union_empty, mem_inter, hdeltaH] at this
            exact mem_inter.2 ⟨mem_union.2 (Or.inl (mem_map.2 ⟨x, this.1, rfl⟩)), this.2⟩
          · have := (mem_powerset.1 hB) he
            exact mem_inter.2 ⟨mem_union.2 (Or.inr (mem_inter.1 this).1), (mem_inter.1 this).2⟩
        have h3 := hHu_ge i S (Y ∩ X) hB0
        rw [hYeq] at h3
        linarith
    have hne' : (T ∩ H.delta i).Nonempty := by
      obtain ⟨e, he⟩ := hi
      obtain ⟨x, hx, rfl⟩ := mem_map.1 (mem_inter.1 he).1
      exact ⟨x, mem_inter.2 ⟨hx, (hdeltaH x).2 (mem_inter.1 he).2⟩⟩
    have hsub := hblock i hne' S hSdem
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_map.1 (mem_inter.1 he).1
    have := hsub (mem_inter.2 ⟨hx, (hdeltaH x).2 (mem_inter.1 he).2⟩)
    rw [hS, mem_subtype] at this
    exact this
