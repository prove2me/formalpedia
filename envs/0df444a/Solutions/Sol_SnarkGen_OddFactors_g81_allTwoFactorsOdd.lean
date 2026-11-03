-- Prove2me | solution 1 for SnarkGen.OddFactors.g81_allTwoFactorsOdd
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:40:43.829202+00:00
-- url     : https://prove2.me/submissions/2a66fee6-71be-4270-8918-e88199974acf

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_TwoFactor
import Definitions.Def_SnarkGen_OddFactors_G81

open SnarkGen.OddFactors

private def v0 : Fin 26 := ⟨0, by decide⟩
private def v1 : Fin 26 := ⟨1, by decide⟩
private def v2 : Fin 26 := ⟨2, by decide⟩
private def v3 : Fin 26 := ⟨3, by decide⟩
private def v4 : Fin 26 := ⟨4, by decide⟩
private def v5 : Fin 26 := ⟨5, by decide⟩
private def v6 : Fin 26 := ⟨6, by decide⟩
private def v7 : Fin 26 := ⟨7, by decide⟩
private def v8 : Fin 26 := ⟨8, by decide⟩
private def v9 : Fin 26 := ⟨9, by decide⟩
private def v10 : Fin 26 := ⟨10, by decide⟩
private def v11 : Fin 26 := ⟨11, by decide⟩
private def v12 : Fin 26 := ⟨12, by decide⟩
private def v13 : Fin 26 := ⟨13, by decide⟩
private def v14 : Fin 26 := ⟨14, by decide⟩
private def v15 : Fin 26 := ⟨15, by decide⟩
private def v16 : Fin 26 := ⟨16, by decide⟩
private def v17 : Fin 26 := ⟨17, by decide⟩
private def v18 : Fin 26 := ⟨18, by decide⟩
private def v19 : Fin 26 := ⟨19, by decide⟩
private def v20 : Fin 26 := ⟨20, by decide⟩
private def v21 : Fin 26 := ⟨21, by decide⟩
private def v22 : Fin 26 := ⟨22, by decide⟩
private def v23 : Fin 26 := ⟨23, by decide⟩
private def v24 : Fin 26 := ⟨24, by decide⟩
private def v25 : Fin 26 := ⟨25, by decide⟩

private def memEdges (p : Fin 26 × Fin 26) : Bool :=
  G81Edges.any (fun q => p.1.val == q.1.val && p.2.val == q.2.val)

private def adjBool (a b : Fin 26) : Bool :=
  memEdges (a, b) || memEdges (b, a)

private lemma adj_iff_adjBool (a b : Fin 26) : G81.Adj a b ↔ adjBool a b = true := by
  simp only [adjBool, memEdges, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, ← Fin.ext_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨(a, b), h, rfl, rfl⟩
    · exact Or.inr ⟨(b, a), h, rfl, rfl⟩
  · rintro (⟨⟨q1, q2⟩, h, rfl, rfl⟩ | ⟨⟨q1, q2⟩, h, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr h

private def inList (x : Fin 26) (l : List (Fin 26)) : Bool :=
  l.any (fun y => x.val == y.val)

private lemma inList_iff {x : Fin 26} {l : List (Fin 26)} : inList x l = true ↔ x ∈ l := by
  simp only [inList, List.any_eq_true, beq_iff_eq, ← Fin.ext_iff]
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun h => ⟨x, h, rfl⟩⟩

private def inPairList (p : Fin 26 × Fin 26) (l : List (Fin 26 × Fin 26)) : Bool :=
  l.any (fun q => p.1.val == q.1.val && p.2.val == q.2.val)

private lemma inPairList_iff {p : Fin 26 × Fin 26} {l : List (Fin 26 × Fin 26)} :
    inPairList p l = true ↔ p ∈ l := by
  simp only [inPairList, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, ← Fin.ext_iff]
  constructor
  · rintro ⟨⟨q1, q2⟩, h, rfl, rfl⟩; exact h
  · intro h; exact ⟨p, h, rfl, rfl⟩

private def nbrsOk (v a b c : Fin 26) : Bool :=
  !(a.val == b.val) && !(a.val == c.val) && !(b.val == c.val) &&
  (List.finRange 26).all (fun w => adjBool v w == (w.val == a.val || w.val == b.val || w.val == c.val))

private def nbrsList : List (Fin 26 × Fin 26 × Fin 26 × Fin 26) :=
  [(v0, v1, v2, v3),
   (v1, v0, v4, v5),
   (v2, v0, v6, v7),
   (v3, v0, v8, v9),
   (v4, v1, v6, v8),
   (v5, v1, v7, v9),
   (v6, v2, v4, v10),
   (v7, v2, v5, v11),
   (v8, v3, v4, v12),
   (v9, v3, v5, v13),
   (v10, v6, v14, v15),
   (v11, v7, v14, v16),
   (v12, v8, v17, v18),
   (v13, v9, v17, v19),
   (v14, v10, v11, v17),
   (v15, v10, v20, v21),
   (v16, v11, v20, v22),
   (v17, v12, v13, v14),
   (v18, v12, v22, v23),
   (v19, v13, v21, v23),
   (v20, v15, v16, v24),
   (v21, v15, v19, v25),
   (v22, v16, v18, v25),
   (v23, v18, v19, v24),
   (v24, v20, v23, v25),
   (v25, v21, v22, v24)]

private def checkAllNbrs : Bool :=
  (nbrsList.map Prod.fst == List.finRange 26) &&
  nbrsList.all (fun t => nbrsOk t.1 t.2.1 t.2.2.1 t.2.2.2)

private lemma checkAllNbrs_eq_true : checkAllNbrs = true := rfl

private lemma exists_nbrsOk (v : Fin 26) : ∃ a b c : Fin 26, nbrsOk v a b c = true := by
  have h := checkAllNbrs_eq_true
  simp only [checkAllNbrs, Bool.and_eq_true, beq_iff_eq] at h
  have hv : v ∈ nbrsList.map Prod.fst := by rw [h.1]; exact List.mem_finRange v
  rcases List.mem_map.mp hv with ⟨⟨v', a, b, c⟩, hmem, rfl⟩
  exact ⟨a, b, c, List.all_eq_true.mp h.2 (v', a, b, c) hmem⟩

private lemma mem_three_of_subset_card_two {α : Type*} [DecidableEq α]
    {s : Finset α} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsub : s ⊆ {a, b, c}) (hcard : s.card = 2) :
    (a ∉ s ∧ b ∈ s ∧ c ∈ s) ∨ (a ∈ s ∧ b ∉ s ∧ c ∈ s) ∨ (a ∈ s ∧ b ∈ s ∧ c ∉ s) := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> by_cases hc : c ∈ s
  · exfalso
    have h1 : ({a, b, c} : Finset α) ⊆ s := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h3 : ({a, b, c} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hbc]
      · simp [hab, hac]
    have := Finset.card_le_card h1
    omega
  · right; right; exact ⟨ha, hb, hc⟩
  · right; left; exact ⟨ha, hb, hc⟩
  · exfalso
    have h1 : s ⊆ {a} := fun x hx => by
      have := hsub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl | rfl
      · rfl
      · exact absurd hx hb
      · exact absurd hx hc
    have := Finset.card_le_card h1
    simp only [Finset.card_singleton] at this; omega
  · left; exact ⟨ha, hb, hc⟩
  · exfalso
    have h1 : s ⊆ {b} := fun x hx => by
      have := hsub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl | rfl
      · exact absurd hx ha
      · rfl
      · exact absurd hx hc
    have := Finset.card_le_card h1
    simp only [Finset.card_singleton] at this; omega
  · exfalso
    have h1 : s ⊆ {c} := fun x hx => by
      have := hsub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl | rfl
      · exact absurd hx ha
      · exact absurd hx hb
      · rfl
    have := Finset.card_le_card h1
    simp only [Finset.card_singleton] at this; omega
  · exfalso
    have h1 : s = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => by
      have := hsub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl <;> contradiction
    rw [h1, Finset.card_empty] at hcard; omega

private def IsMissing (F : SimpleGraph (Fin 26)) (u v : Fin 26) : Prop :=
  G81.Adj u v ∧ ¬ F.Adj u v

private lemma isMissing_symm {F : SimpleGraph (Fin 26)} {u v : Fin 26} (h : IsMissing F u v) :
    IsMissing F v u :=
  ⟨h.1.symm, fun hf => h.2 hf.symm⟩

private lemma nbrsOk_spec {F : SimpleGraph (Fin 26)}
    (hTF : SnarkGen.EdgeInsertion.IsTwoFactor G81 F)
    {v a b c : Fin 26} (hn : nbrsOk v a b c = true) :
    (IsMissing F v a ∨ IsMissing F v b ∨ IsMissing F v c) ∧
    (∀ u₁ u₂, IsMissing F v u₁ → IsMissing F v u₂ → u₁ = u₂) := by
  classical
  simp only [nbrsOk, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    ← Fin.ext_iff, List.all_eq_true, beq_iff_eq] at hn
  rcases hn with ⟨⟨⟨hab, hac⟩, hbc⟩, hall⟩
  have hadj : ∀ w : Fin 26, G81.Adj v w ↔ w = a ∨ w = b ∨ w = c := by
    intro w
    rw [adj_iff_adjBool, hall w (List.mem_finRange w)]
    simp only [Bool.or_eq_true, beq_iff_eq, ← Fin.ext_iff, or_assoc]
  have hsub : F.neighborFinset v ⊆ {a, b, c} := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    have hg : G81.Adj v w := hTF.1 hw
    rw [hadj] at hg
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hg
  have hcard : (F.neighborFinset v).card = 2 := hTF.2 v
  have h3 := mem_three_of_subset_card_two hab hac hbc hsub hcard
  simp only [SimpleGraph.mem_neighborFinset] at h3
  have haG : G81.Adj v a := (hadj a).mpr (Or.inl rfl)
  have hbG : G81.Adj v b := (hadj b).mpr (Or.inr (Or.inl rfl))
  have hcG : G81.Adj v c := (hadj c).mpr (Or.inr (Or.inr rfl))
  rcases h3 with ⟨hna, hfb, hfc⟩ | ⟨hfa, hnb, hfc⟩ | ⟨hfa, hfb, hnc⟩
  · refine ⟨Or.inl ⟨haG, hna⟩, ?_⟩
    intro u₁ u₂ ⟨hg₁, hn₁⟩ ⟨hg₂, hn₂⟩
    rcases (hadj u₁).mp hg₁ with rfl | rfl | rfl <;>
    rcases (hadj u₂).mp hg₂ with rfl | rfl | rfl <;>
    first | rfl | contradiction
  · refine ⟨Or.inr (Or.inl ⟨hbG, hnb⟩), ?_⟩
    intro u₁ u₂ ⟨hg₁, hn₁⟩ ⟨hg₂, hn₂⟩
    rcases (hadj u₁).mp hg₁ with rfl | rfl | rfl <;>
    rcases (hadj u₂).mp hg₂ with rfl | rfl | rfl <;>
    first | rfl | contradiction
  · refine ⟨Or.inr (Or.inr ⟨hcG, hnc⟩), ?_⟩
    intro u₁ u₂ ⟨hg₁, hn₁⟩ ⟨hg₂, hn₂⟩
    rcases (hadj u₁).mp hg₁ with rfl | rfl | rfl <;>
    rcases (hadj u₂).mp hg₂ with rfl | rfl | rfl <;>
    first | rfl | contradiction

private lemma isMissing_unique {F : SimpleGraph (Fin 26)}
    (hTF : SnarkGen.EdgeInsertion.IsTwoFactor G81 F)
    {v u₁ u₂ : Fin 26} (h1 : IsMissing F v u₁) (h2 : IsMissing F v u₂) : u₁ = u₂ := by
  rcases exists_nbrsOk v with ⟨a, b, c, hn⟩
  exact (nbrsOk_spec hTF hn).2 u₁ u₂ h1 h2

private def inNbrsList (v a b c : Fin 26) : Bool :=
  nbrsList.any (fun t =>
    t.1.val == v.val && t.2.1.val == a.val && t.2.2.1.val == b.val && t.2.2.2.val == c.val)

private lemma nbrsOk_of_inNbrsList {v a b c : Fin 26} (h : inNbrsList v a b c = true) :
    nbrsOk v a b c = true := by
  have hc := checkAllNbrs_eq_true
  simp only [checkAllNbrs, Bool.and_eq_true] at hc
  simp only [inNbrsList, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, ← Fin.ext_iff] at h
  rcases h with ⟨⟨v', a', b', c'⟩, hmem, ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  exact List.all_eq_true.mp hc.2 (v', a', b', c') hmem

private def fAdj (ctx : List (Fin 26 × Fin 26)) (u v : Fin 26) : Bool :=
  adjBool u v && !inPairList (u, v) ctx

private def walkValidCtx (ctx : List (Fin 26 × Fin 26)) : Fin 26 → List (Fin 26) → Bool
  | _, [] => true
  | a, b :: l => fAdj ctx a b && walkValidCtx ctx b l

private def closedCtx (ctx : List (Fin 26 × Fin 26)) (L : List (Fin 26)) : Bool :=
  G81Edges.all (fun p => inPairList p ctx || (inList p.1 L == inList p.2 L))

private def nodupBool : List (Fin 26) → Bool
  | [] => true
  | x :: l => !inList x l && nodupBool l

private def cycleOk (ctx : List (Fin 26 × Fin 26)) (h : Fin 26) (t : List (Fin 26)) : Bool :=
  walkValidCtx ctx h t && closedCtx ctx (h :: t) && nodupBool (h :: t) && ((h :: t).length % 2 == 1)

private def leafOk (ctx : List (Fin 26 × Fin 26)) (c1 c2 : Fin 26 × List (Fin 26)) : Bool :=
  (List.finRange 26).all (fun u => ctx.any (fun p => p.1.val == u.val)) &&
  cycleOk ctx c1.1 c1.2 && cycleOk ctx c2.1 c2.2 &&
  (List.finRange 26).all (fun x => inList x (c1.1 :: c1.2) || inList x (c2.1 :: c2.2))

private inductive CertTree
  | leaf (c1 c2 : Fin 26 × List (Fin 26))
  | conflict (u v z : Fin 26)
  | branch (v a b c : Fin 26) (t0 t1 t2 : CertTree)

private def checkTree (ctx : List (Fin 26 × Fin 26)) : CertTree → Bool
  | .leaf c1 c2 => leafOk ctx c1 c2
  | .conflict u v z => inPairList (u, v) ctx && inPairList (u, z) ctx && !(v.val == z.val)
  | .branch v a b c t0 t1 t2 =>
    inNbrsList v a b c &&
    checkTree ((v, a) :: (a, v) :: ctx) t0 &&
    checkTree ((v, b) :: (b, v) :: ctx) t1 &&
    checkTree ((v, c) :: (c, v) :: ctx) t2

private def theTree : CertTree :=
  .branch v0 v1 v2 v3 (.branch v2 v0 v6 v7 (.conflict v0 v2 v1) (.branch v4 v1 v6 v8 (.conflict v1 v4 v0) (.conflict v6 v4 v2) (.branch v3 v0 v8 v9 (.conflict v0 v3 v1) (.conflict v8 v3 v4) (.branch v5 v1 v7 v9 (.conflict v1 v5 v0) (.branch v10 v6 v14 v15 (.conflict v6 v10 v2) (.branch v11 v7 v14 v16 (.conflict v7 v11 v5) (.conflict v14 v11 v10) (.branch v12 v8 v17 v18 (.conflict v8 v12 v4) (.branch v13 v9 v17 v19 (.conflict v9 v13 v3) (.conflict v17 v13 v12) (.branch v15 v10 v20 v21 (.conflict v10 v15 v14) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.conflict v19 v21 v13) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.conflict v19 v23 v13) (.leaf (v0, [v2, v7, v11, v14, v17, v13, v9, v5, v1, v4, v6, v10, v15, v21, v19, v23, v18, v12, v8, v3]) (v16, [v20, v24, v25, v22]))) (.conflict v25 v22 v21))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.conflict v16 v20 v11) (.branch v23 v18 v19 v24 (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v23) (.leaf (v0, [v2, v7, v11, v14, v17, v13, v9, v5, v1, v4, v6, v10, v15, v20, v16, v22, v18, v12, v8, v3]) (v19, [v21, v25, v24, v23]))) (.conflict v19 v23 v13) (.conflict v24 v23 v20))))) (.branch v17 v12 v13 v14 (.conflict v12 v17 v18) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v12) (.branch v15 v10 v20 v21 (.conflict v10 v15 v14) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v21) (.leaf (v0, [v2, v7, v11, v14, v17, v12, v8, v3]) (v1, [v4, v6, v10, v15, v21, v25, v24, v20, v16, v22, v18, v23, v19, v13, v9, v5]))) (.conflict v25 v21 v22)) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.conflict v21 v19 v15) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.conflict v16 v20 v11) (.leaf (v0, [v2, v7, v11, v14, v17, v12, v8, v3]) (v1, [v4, v6, v10, v15, v20, v16, v22, v18, v23, v24, v25, v21, v19, v13, v9, v5])))))) (.conflict v14 v17 v10)))) (.branch v11 v7 v14 v16 (.conflict v7 v11 v5) (.branch v12 v8 v17 v18 (.conflict v8 v12 v4) (.branch v13 v9 v17 v19 (.conflict v9 v13 v3) (.conflict v17 v13 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v13) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.conflict v19 v23 v13) (.leaf (v0, [v2, v7, v11, v16, v22, v25, v24, v20, v15, v21, v19, v23, v18, v12, v8, v3]) (v1, [v4, v6, v10, v14, v17, v13, v9, v5]))) (.conflict v25 v22 v21)) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.conflict v22 v18 v16) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v22) (.leaf (v0, [v2, v7, v11, v16, v20, v15, v21, v19, v23, v24, v25, v22, v18, v12, v8, v3]) (v1, [v4, v6, v10, v14, v17, v13, v9, v5]))))))) (.branch v17 v12 v13 v14 (.conflict v12 v17 v18) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.conflict v18 v22 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v21) (.leaf (v0, [v2, v7, v11, v16, v22, v18, v23, v19, v13, v9, v5, v1, v4, v6, v10, v14, v17, v12, v8, v3]) (v15, [v20, v24, v25, v21]))) (.conflict v25 v21 v22))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v22) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v23) (.leaf (v0, [v2, v7, v11, v16, v20, v15, v21, v19, v13, v9, v5, v1, v4, v6, v10, v14, v17, v12, v8, v3]) (v18, [v22, v25, v24, v23]))) (.conflict v24 v23 v20)))) (.conflict v14 v17 v11))) (.branch v14 v10 v11 v17 (.conflict v10 v14 v15) (.conflict v11 v14 v16) (.branch v12 v8 v17 v18 (.conflict v8 v12 v4) (.conflict v17 v12 v14) (.branch v13 v9 v17 v19 (.conflict v9 v13 v3) (.conflict v17 v13 v14) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v11) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v13) (.conflict v24 v23 v20)))))))) (.conflict v9 v5 v3)))) (.branch v5 v1 v7 v9 (.conflict v1 v5 v0) (.conflict v7 v5 v2) (.branch v3 v0 v8 v9 (.conflict v0 v3 v1) (.branch v4 v1 v6 v8 (.conflict v1 v4 v0) (.branch v10 v6 v14 v15 (.conflict v6 v10 v4) (.branch v11 v7 v14 v16 (.conflict v7 v11 v2) (.conflict v14 v11 v10) (.branch v12 v8 v17 v18 (.conflict v8 v12 v3) (.branch v13 v9 v17 v19 (.conflict v9 v13 v5) (.conflict v17 v13 v12) (.branch v15 v10 v20 v21 (.conflict v10 v15 v14) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.conflict v19 v21 v13) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.conflict v19 v23 v13) (.leaf (v0, [v2, v6, v10, v15, v21, v19, v23, v18, v12, v8, v4, v1, v5, v7, v11, v14, v17, v13, v9, v3]) (v16, [v20, v24, v25, v22]))) (.conflict v25 v22 v21))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.conflict v16 v20 v11) (.branch v23 v18 v19 v24 (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v23) (.leaf (v0, [v2, v6, v10, v15, v20, v16, v22, v18, v12, v8, v4, v1, v5, v7, v11, v14, v17, v13, v9, v3]) (v19, [v21, v25, v24, v23]))) (.conflict v19 v23 v13) (.conflict v24 v23 v20))))) (.branch v17 v12 v13 v14 (.conflict v12 v17 v18) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v12) (.branch v15 v10 v20 v21 (.conflict v10 v15 v14) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v21) (.leaf (v0, [v2, v6, v10, v15, v21, v25, v24, v20, v16, v22, v18, v23, v19, v13, v9, v3]) (v1, [v4, v8, v12, v17, v14, v11, v7, v5]))) (.conflict v25 v21 v22)) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.conflict v21 v19 v15) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.conflict v16 v20 v11) (.leaf (v0, [v2, v6, v10, v15, v20, v16, v22, v18, v23, v24, v25, v21, v19, v13, v9, v3]) (v1, [v4, v8, v12, v17, v14, v11, v7, v5])))))) (.conflict v14 v17 v10)))) (.branch v11 v7 v14 v16 (.conflict v7 v11 v2) (.branch v12 v8 v17 v18 (.conflict v8 v12 v3) (.branch v13 v9 v17 v19 (.conflict v9 v13 v5) (.conflict v17 v13 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v13) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.conflict v19 v23 v13) (.leaf (v0, [v2, v6, v10, v14, v17, v13, v9, v3]) (v1, [v4, v8, v12, v18, v23, v19, v21, v15, v20, v24, v25, v22, v16, v11, v7, v5]))) (.conflict v25 v22 v21)) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.conflict v22 v18 v16) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v22) (.leaf (v0, [v2, v6, v10, v14, v17, v13, v9, v3]) (v1, [v4, v8, v12, v18, v22, v25, v24, v23, v19, v21, v15, v20, v16, v11, v7, v5]))))))) (.branch v17 v12 v13 v14 (.conflict v12 v17 v18) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.conflict v18 v22 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v21) (.leaf (v0, [v2, v6, v10, v14, v17, v12, v8, v4, v1, v5, v7, v11, v16, v22, v18, v23, v19, v13, v9, v3]) (v15, [v20, v24, v25, v21]))) (.conflict v25 v21 v22))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v22) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v23) (.leaf (v0, [v2, v6, v10, v14, v17, v12, v8, v4, v1, v5, v7, v11, v16, v20, v15, v21, v19, v13, v9, v3]) (v18, [v22, v25, v24, v23]))) (.conflict v24 v23 v20)))) (.conflict v14 v17 v11))) (.branch v14 v10 v11 v17 (.conflict v10 v14 v15) (.conflict v11 v14 v16) (.branch v12 v8 v17 v18 (.conflict v8 v12 v3) (.conflict v17 v12 v14) (.branch v13 v9 v17 v19 (.conflict v9 v13 v5) (.conflict v17 v13 v14) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v11) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v13) (.conflict v24 v23 v20)))))))) (.conflict v8 v4 v3)) (.conflict v9 v3 v5)))) (.branch v1 v0 v4 v5 (.conflict v0 v1 v2) (.branch v6 v2 v4 v10 (.conflict v2 v6 v0) (.conflict v4 v6 v1) (.branch v3 v0 v8 v9 (.conflict v0 v3 v2) (.branch v5 v1 v7 v9 (.conflict v1 v5 v4) (.branch v9 v3 v5 v13 (.conflict v3 v9 v8) (.conflict v5 v9 v7) (.branch v11 v7 v14 v16 (.conflict v7 v11 v5) (.branch v17 v12 v13 v14 (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.conflict v20 v16 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.conflict v22 v18 v16) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.branch v24 v20 v23 v25 (.conflict v20 v24 v15) (.conflict v23 v24 v18) (.leaf (v0, [v1, v5, v9, v3]) (v2, [v6, v4, v8, v12, v18, v22, v25, v21, v15, v10, v14, v17, v13, v19, v23, v24, v20, v16, v11, v7]))) (.conflict v23 v19 v18)))) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.conflict v21 v19 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.branch v24 v20 v23 v25 (.conflict v20 v24 v16) (.conflict v23 v24 v19) (.leaf (v0, [v1, v5, v9, v3]) (v2, [v6, v4, v8, v12, v18, v23, v24, v20, v15, v10, v14, v17, v13, v19, v21, v25, v22, v16, v11, v7]))) (.conflict v22 v16 v18)) (.conflict v23 v18 v19)))) (.conflict v13 v17 v9) (.conflict v14 v17 v11)) (.branch v14 v10 v11 v17 (.conflict v10 v14 v6) (.conflict v11 v14 v16) (.branch v12 v8 v17 v18 (.conflict v8 v12 v3) (.conflict v17 v12 v14) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v12) (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v21) (.leaf (v0, [v1, v5, v9, v3]) (v2, [v6, v4, v8, v12, v17, v13, v19, v23, v18, v22, v16, v20, v24, v25, v21, v15, v10, v14, v11, v7]))) (.conflict v25 v21 v22)) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.conflict v21 v19 v15) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.conflict v16 v20 v11) (.leaf (v0, [v1, v5, v9, v3]) (v2, [v6, v4, v8, v12, v17, v13, v19, v21, v25, v24, v23, v18, v22, v16, v20, v15, v10, v14, v11, v7])))))))))) (.branch v7 v2 v5 v11 (.conflict v2 v7 v0) (.conflict v5 v7 v9) (.branch v14 v10 v11 v17 (.conflict v10 v14 v6) (.conflict v11 v14 v7) (.branch v12 v8 v17 v18 (.conflict v8 v12 v3) (.conflict v17 v12 v14) (.branch v13 v9 v17 v19 (.conflict v9 v13 v5) (.conflict v17 v13 v14) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v13) (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.conflict v20 v16 v15) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.conflict v19 v21 v13) (.leaf (v0, [v1, v5, v7, v2, v6, v4, v8, v12, v17, v13, v9, v3]) (v10, [v14, v11, v16, v20, v24, v25, v22, v18, v23, v19, v21, v15])))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.conflict v18 v22 v12) (.leaf (v0, [v1, v5, v7, v2, v6, v4, v8, v12, v17, v13, v9, v3]) (v10, [v14, v11, v16, v22, v18, v23, v19, v21, v25, v24, v20, v15]))) (.conflict v24 v20 v23))))))))) (.branch v5 v1 v7 v9 (.conflict v1 v5 v4) (.branch v8 v3 v4 v12 (.conflict v3 v8 v9) (.conflict v4 v8 v1) (.branch v11 v7 v14 v16 (.conflict v7 v11 v5) (.branch v17 v12 v13 v14 (.conflict v12 v17 v8) (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.conflict v20 v16 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.conflict v22 v18 v16) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.branch v24 v20 v23 v25 (.conflict v20 v24 v15) (.conflict v23 v24 v18) (.leaf (v0, [v1, v5, v9, v13, v19, v23, v24, v20, v16, v11, v7, v2, v6, v4, v8, v3]) (v10, [v14, v17, v12, v18, v22, v25, v21, v15]))) (.conflict v23 v19 v18)))) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.conflict v21 v19 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.branch v24 v20 v23 v25 (.conflict v20 v24 v16) (.conflict v23 v24 v19) (.leaf (v0, [v1, v5, v9, v13, v19, v21, v25, v22, v16, v11, v7, v2, v6, v4, v8, v3]) (v10, [v14, v17, v12, v18, v23, v24, v20, v15]))) (.conflict v22 v16 v18)) (.conflict v23 v18 v19)))) (.conflict v14 v17 v11)) (.branch v14 v10 v11 v17 (.conflict v10 v14 v6) (.conflict v11 v14 v16) (.branch v13 v9 v17 v19 (.conflict v9 v13 v3) (.conflict v17 v13 v14) (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.conflict v19 v21 v13) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.conflict v19 v23 v13) (.leaf (v0, [v1, v5, v9, v13, v17, v12, v18, v23, v19, v21, v15, v10, v14, v11, v7, v2, v6, v4, v8, v3]) (v16, [v20, v24, v25, v22]))) (.conflict v25 v22 v21))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.conflict v16 v20 v11) (.branch v23 v18 v19 v24 (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v23) (.leaf (v0, [v1, v5, v9, v13, v17, v12, v18, v22, v16, v20, v15, v10, v14, v11, v7, v2, v6, v4, v8, v3]) (v19, [v21, v25, v24, v23]))) (.conflict v19 v23 v13) (.conflict v24 v23 v20)))))))) (.conflict v9 v5 v3)))) (.branch v7 v2 v5 v11 (.conflict v2 v7 v0) (.conflict v5 v7 v1) (.branch v3 v0 v8 v9 (.conflict v0 v3 v2) (.branch v4 v1 v6 v8 (.conflict v1 v4 v5) (.branch v9 v3 v5 v13 (.conflict v3 v9 v8) (.conflict v5 v9 v1) (.branch v10 v6 v14 v15 (.conflict v6 v10 v4) (.branch v17 v12 v13 v14 (.branch v15 v10 v20 v21 (.conflict v10 v15 v14) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.conflict v20 v16 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.conflict v22 v18 v16) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.branch v24 v20 v23 v25 (.conflict v20 v24 v15) (.conflict v23 v24 v18) (.leaf (v0, [v1, v4, v8, v12, v18, v22, v25, v21, v15, v10, v6, v2, v7, v5, v9, v3]) (v11, [v14, v17, v13, v19, v23, v24, v20, v16]))) (.conflict v23 v19 v18)))) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.conflict v21 v19 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.branch v24 v20 v23 v25 (.conflict v20 v24 v16) (.conflict v23 v24 v19) (.leaf (v0, [v1, v4, v8, v12, v18, v23, v24, v20, v15, v10, v6, v2, v7, v5, v9, v3]) (v11, [v14, v17, v13, v19, v21, v25, v22, v16]))) (.conflict v22 v16 v18)) (.conflict v23 v18 v19)))) (.conflict v13 v17 v9) (.conflict v14 v17 v10)) (.branch v14 v10 v11 v17 (.conflict v10 v14 v15) (.conflict v11 v14 v7) (.branch v12 v8 v17 v18 (.conflict v8 v12 v3) (.conflict v17 v12 v14) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.conflict v18 v22 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v21) (.leaf (v0, [v1, v4, v8, v12, v17, v13, v19, v23, v18, v22, v16, v11, v14, v10, v6, v2, v7, v5, v9, v3]) (v15, [v20, v24, v25, v21]))) (.conflict v25 v21 v22))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v22) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v23) (.leaf (v0, [v1, v4, v8, v12, v17, v13, v19, v21, v15, v20, v16, v11, v14, v10, v6, v2, v7, v5, v9, v3]) (v18, [v22, v25, v24, v23]))) (.conflict v24 v23 v20)))))))) (.conflict v8 v4 v3)) (.branch v4 v1 v6 v8 (.conflict v1 v4 v5) (.branch v8 v3 v4 v12 (.conflict v3 v8 v9) (.conflict v4 v8 v6) (.branch v10 v6 v14 v15 (.conflict v6 v10 v4) (.branch v17 v12 v13 v14 (.conflict v12 v17 v8) (.branch v15 v10 v20 v21 (.conflict v10 v15 v14) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.conflict v20 v16 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.conflict v22 v18 v16) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.branch v24 v20 v23 v25 (.conflict v20 v24 v15) (.conflict v23 v24 v18) (.leaf (v0, [v1, v4, v8, v3]) (v2, [v6, v10, v15, v21, v25, v22, v18, v12, v17, v14, v11, v16, v20, v24, v23, v19, v13, v9, v5, v7]))) (.conflict v23 v19 v18)))) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.conflict v21 v19 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.branch v24 v20 v23 v25 (.conflict v20 v24 v16) (.conflict v23 v24 v19) (.leaf (v0, [v1, v4, v8, v3]) (v2, [v6, v10, v15, v20, v24, v23, v18, v12, v17, v14, v11, v16, v22, v25, v21, v19, v13, v9, v5, v7]))) (.conflict v22 v16 v18)) (.conflict v23 v18 v19)))) (.conflict v14 v17 v10)) (.branch v14 v10 v11 v17 (.conflict v10 v14 v15) (.conflict v11 v14 v7) (.branch v13 v9 v17 v19 (.conflict v9 v13 v3) (.conflict v17 v13 v14) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v13) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.conflict v19 v23 v13) (.leaf (v0, [v1, v4, v8, v3]) (v2, [v6, v10, v14, v11, v16, v22, v25, v24, v20, v15, v21, v19, v23, v18, v12, v17, v13, v9, v5, v7]))) (.conflict v25 v22 v21)) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.conflict v22 v18 v16) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v22) (.leaf (v0, [v1, v4, v8, v3]) (v2, [v6, v10, v14, v11, v16, v20, v15, v21, v19, v23, v24, v25, v22, v18, v12, v17, v13, v9, v5, v7])))))))))) (.branch v6 v2 v4 v10 (.conflict v2 v6 v0) (.conflict v4 v6 v8) (.branch v14 v10 v11 v17 (.conflict v10 v14 v6) (.conflict v11 v14 v7) (.branch v12 v8 v17 v18 (.conflict v8 v12 v4) (.conflict v17 v12 v14) (.branch v13 v9 v17 v19 (.conflict v9 v13 v3) (.conflict v17 v13 v14) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v13) (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.conflict v20 v16 v15) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.conflict v19 v21 v13) (.leaf (v0, [v1, v4, v6, v2, v7, v5, v9, v13, v17, v12, v8, v3]) (v10, [v14, v11, v16, v20, v24, v25, v22, v18, v23, v19, v21, v15])))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.conflict v18 v22 v12) (.leaf (v0, [v1, v4, v6, v2, v7, v5, v9, v13, v17, v12, v8, v3]) (v10, [v14, v11, v16, v22, v18, v23, v19, v21, v25, v24, v20, v15]))) (.conflict v24 v20 v23)))))))))))) (.branch v1 v0 v4 v5 (.conflict v0 v1 v3) (.branch v8 v3 v4 v12 (.conflict v3 v8 v0) (.conflict v4 v8 v1) (.branch v2 v0 v6 v7 (.conflict v0 v2 v3) (.branch v5 v1 v7 v9 (.conflict v1 v5 v4) (.branch v9 v3 v5 v13 (.conflict v3 v9 v0) (.conflict v5 v9 v7) (.branch v17 v12 v13 v14 (.conflict v12 v17 v8) (.conflict v13 v17 v9) (.branch v10 v6 v14 v15 (.conflict v6 v10 v2) (.conflict v14 v10 v17) (.branch v11 v7 v14 v16 (.conflict v7 v11 v5) (.conflict v14 v11 v17) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v11) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v23) (.leaf (v0, [v1, v5, v9, v3, v8, v4, v6, v10, v14, v11, v7, v2]) (v12, [v17, v13, v19, v21, v15, v20, v16, v22, v25, v24, v23, v18]))) (.conflict v24 v23 v20)) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v23) (.leaf (v0, [v1, v5, v9, v3, v8, v4, v6, v10, v14, v11, v7, v2]) (v12, [v17, v13, v19, v23, v24, v25, v21, v15, v20, v16, v22, v18]))) (.conflict v23 v19 v18)))))))) (.branch v7 v2 v5 v11 (.conflict v2 v7 v6) (.conflict v5 v7 v9) (.branch v10 v6 v14 v15 (.conflict v6 v10 v2) (.branch v17 v12 v13 v14 (.conflict v12 v17 v8) (.branch v15 v10 v20 v21 (.conflict v10 v15 v14) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.conflict v20 v16 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.conflict v22 v18 v16) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.branch v24 v20 v23 v25 (.conflict v20 v24 v15) (.conflict v23 v24 v18) (.leaf (v0, [v1, v5, v7, v2]) (v3, [v8, v4, v6, v10, v15, v21, v25, v22, v18, v12, v17, v14, v11, v16, v20, v24, v23, v19, v13, v9]))) (.conflict v23 v19 v18)))) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.conflict v21 v19 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.branch v24 v20 v23 v25 (.conflict v20 v24 v16) (.conflict v23 v24 v19) (.leaf (v0, [v1, v5, v7, v2]) (v3, [v8, v4, v6, v10, v15, v20, v24, v23, v18, v12, v17, v14, v11, v16, v22, v25, v21, v19, v13, v9]))) (.conflict v22 v16 v18)) (.conflict v23 v18 v19)))) (.conflict v14 v17 v10)) (.branch v14 v10 v11 v17 (.conflict v10 v14 v15) (.conflict v11 v14 v7) (.branch v13 v9 v17 v19 (.conflict v9 v13 v5) (.conflict v17 v13 v14) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v13) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.conflict v19 v23 v13) (.leaf (v0, [v1, v5, v7, v2]) (v3, [v8, v4, v6, v10, v14, v11, v16, v22, v25, v24, v20, v15, v21, v19, v23, v18, v12, v17, v13, v9]))) (.conflict v25 v22 v21)) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.conflict v22 v18 v16) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v22) (.leaf (v0, [v1, v5, v7, v2]) (v3, [v8, v4, v6, v10, v14, v11, v16, v20, v15, v21, v19, v23, v24, v25, v22, v18, v12, v17, v13, v9]))))))))))) (.branch v5 v1 v7 v9 (.conflict v1 v5 v4) (.conflict v7 v5 v2) (.branch v6 v2 v4 v10 (.conflict v2 v6 v7) (.conflict v4 v6 v1) (.branch v11 v7 v14 v16 (.conflict v7 v11 v2) (.branch v17 v12 v13 v14 (.conflict v12 v17 v8) (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.conflict v20 v16 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.conflict v22 v18 v16) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.branch v24 v20 v23 v25 (.conflict v20 v24 v15) (.conflict v23 v24 v18) (.leaf (v0, [v1, v5, v7, v11, v16, v20, v24, v23, v19, v13, v9, v3, v8, v4, v6, v2]) (v10, [v14, v17, v12, v18, v22, v25, v21, v15]))) (.conflict v23 v19 v18)))) (.branch v19 v13 v21 v23 (.conflict v13 v19 v17) (.conflict v21 v19 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.branch v24 v20 v23 v25 (.conflict v20 v24 v16) (.conflict v23 v24 v19) (.leaf (v0, [v1, v5, v7, v11, v16, v22, v25, v21, v19, v13, v9, v3, v8, v4, v6, v2]) (v10, [v14, v17, v12, v18, v23, v24, v20, v15]))) (.conflict v22 v16 v18)) (.conflict v23 v18 v19)))) (.conflict v14 v17 v11)) (.branch v14 v10 v11 v17 (.conflict v10 v14 v6) (.conflict v11 v14 v16) (.branch v13 v9 v17 v19 (.conflict v9 v13 v5) (.conflict v17 v13 v14) (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.conflict v19 v21 v13) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.conflict v19 v23 v13) (.leaf (v0, [v1, v5, v7, v11, v14, v10, v15, v21, v19, v23, v18, v12, v17, v13, v9, v3, v8, v4, v6, v2]) (v16, [v20, v24, v25, v22]))) (.conflict v25 v22 v21))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.conflict v16 v20 v11) (.branch v23 v18 v19 v24 (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v23) (.leaf (v0, [v1, v5, v7, v11, v14, v10, v15, v20, v16, v22, v18, v12, v17, v13, v9, v3, v8, v4, v6, v2]) (v19, [v21, v25, v24, v23]))) (.conflict v19 v23 v13) (.conflict v24 v23 v20))))))))))) (.branch v9 v3 v5 v13 (.conflict v3 v9 v0) (.conflict v5 v9 v1) (.branch v2 v0 v6 v7 (.conflict v0 v2 v3) (.branch v4 v1 v6 v8 (.conflict v1 v4 v5) (.conflict v6 v4 v2) (.branch v7 v2 v5 v11 (.conflict v2 v7 v6) (.conflict v5 v7 v1) (.branch v10 v6 v14 v15 (.conflict v6 v10 v2) (.branch v17 v12 v13 v14 (.branch v15 v10 v20 v21 (.conflict v10 v15 v14) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.conflict v20 v16 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.conflict v22 v18 v16) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.branch v24 v20 v23 v25 (.conflict v20 v24 v15) (.conflict v23 v24 v18) (.leaf (v0, [v1, v4, v6, v10, v15, v21, v25, v22, v18, v12, v8, v3, v9, v5, v7, v2]) (v11, [v14, v17, v13, v19, v23, v24, v20, v16]))) (.conflict v23 v19 v18)))) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.conflict v21 v19 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.branch v24 v20 v23 v25 (.conflict v20 v24 v16) (.conflict v23 v24 v19) (.leaf (v0, [v1, v4, v6, v10, v15, v20, v24, v23, v18, v12, v8, v3, v9, v5, v7, v2]) (v11, [v14, v17, v13, v19, v21, v25, v22, v16]))) (.conflict v22 v16 v18)) (.conflict v23 v18 v19)))) (.conflict v13 v17 v9) (.conflict v14 v17 v10)) (.branch v14 v10 v11 v17 (.conflict v10 v14 v15) (.conflict v11 v14 v7) (.branch v12 v8 v17 v18 (.conflict v8 v12 v4) (.conflict v17 v12 v14) (.branch v16 v11 v20 v22 (.conflict v11 v16 v7) (.branch v22 v16 v18 v25 (.conflict v16 v22 v20) (.conflict v18 v22 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v21) (.leaf (v0, [v1, v4, v6, v10, v14, v11, v16, v22, v18, v23, v19, v13, v17, v12, v8, v3, v9, v5, v7, v2]) (v15, [v20, v24, v25, v21]))) (.conflict v25 v21 v22))) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v22) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v23) (.leaf (v0, [v1, v4, v6, v10, v14, v11, v16, v20, v15, v21, v19, v13, v17, v12, v8, v3, v9, v5, v7, v2]) (v18, [v22, v25, v24, v23]))) (.conflict v24 v23 v20))))))))) (.branch v4 v1 v6 v8 (.conflict v1 v4 v5) (.branch v8 v3 v4 v12 (.conflict v3 v8 v0) (.conflict v4 v8 v6) (.branch v17 v12 v13 v14 (.conflict v12 v17 v8) (.conflict v13 v17 v9) (.branch v10 v6 v14 v15 (.conflict v6 v10 v4) (.conflict v14 v10 v17) (.branch v11 v7 v14 v16 (.conflict v7 v11 v2) (.conflict v14 v11 v17) (.branch v20 v15 v16 v24 (.conflict v15 v20 v10) (.conflict v16 v20 v11) (.branch v18 v12 v22 v23 (.conflict v12 v18 v8) (.branch v23 v18 v19 v24 (.conflict v18 v23 v22) (.branch v21 v15 v19 v25 (.conflict v15 v21 v10) (.conflict v19 v21 v23) (.leaf (v0, [v1, v4, v8, v3, v9, v5, v7, v11, v14, v10, v6, v2]) (v12, [v17, v13, v19, v21, v15, v20, v16, v22, v25, v24, v23, v18]))) (.conflict v24 v23 v20)) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v23) (.leaf (v0, [v1, v4, v8, v3, v9, v5, v7, v11, v14, v10, v6, v2]) (v12, [v17, v13, v19, v23, v24, v25, v21, v15, v20, v16, v22, v18]))) (.conflict v23 v19 v18)))))))) (.branch v6 v2 v4 v10 (.conflict v2 v6 v7) (.conflict v4 v6 v8) (.branch v11 v7 v14 v16 (.conflict v7 v11 v2) (.branch v17 v12 v13 v14 (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.conflict v20 v16 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.conflict v22 v18 v16) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.branch v24 v20 v23 v25 (.conflict v20 v24 v15) (.conflict v23 v24 v18) (.leaf (v0, [v1, v4, v6, v2]) (v3, [v8, v12, v18, v22, v25, v21, v15, v10, v14, v17, v13, v19, v23, v24, v20, v16, v11, v7, v5, v9]))) (.conflict v23 v19 v18)))) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.conflict v21 v19 v15) (.branch v18 v12 v22 v23 (.conflict v12 v18 v17) (.branch v16 v11 v20 v22 (.conflict v11 v16 v14) (.branch v24 v20 v23 v25 (.conflict v20 v24 v16) (.conflict v23 v24 v19) (.leaf (v0, [v1, v4, v6, v2]) (v3, [v8, v12, v18, v23, v24, v20, v15, v10, v14, v17, v13, v19, v21, v25, v22, v16, v11, v7, v5, v9]))) (.conflict v22 v16 v18)) (.conflict v23 v18 v19)))) (.conflict v13 v17 v9) (.conflict v14 v17 v11)) (.branch v14 v10 v11 v17 (.conflict v10 v14 v6) (.conflict v11 v14 v16) (.branch v12 v8 v17 v18 (.conflict v8 v12 v4) (.conflict v17 v12 v14) (.branch v22 v16 v18 v25 (.conflict v16 v22 v11) (.conflict v18 v22 v12) (.branch v15 v10 v20 v21 (.conflict v10 v15 v6) (.branch v21 v15 v19 v25 (.conflict v15 v21 v20) (.branch v23 v18 v19 v24 (.conflict v18 v23 v12) (.conflict v19 v23 v21) (.leaf (v0, [v1, v4, v6, v2]) (v3, [v8, v12, v17, v13, v19, v23, v18, v22, v16, v20, v24, v25, v21, v15, v10, v14, v11, v7, v5, v9]))) (.conflict v25 v21 v22)) (.branch v19 v13 v21 v23 (.conflict v13 v19 v9) (.conflict v21 v19 v15) (.branch v20 v15 v16 v24 (.conflict v15 v20 v21) (.conflict v16 v20 v11) (.leaf (v0, [v1, v4, v6, v2]) (v3, [v8, v12, v17, v13, v19, v21, v25, v24, v23, v18, v22, v16, v20, v15, v10, v14, v11, v7, v5, v9]))))))))))))))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
private lemma checkTree_theTree : checkTree [] theTree = true := rfl

private lemma nodup_of_nodupBool : ∀ {l : List (Fin 26)}, nodupBool l = true → l.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
    simp only [nodupBool, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, inList_iff] at h
    exact List.nodup_cons.mpr ⟨h.1, nodup_of_nodupBool h.2⟩

private lemma reachable_of_walkValidCtx {F : SimpleGraph (Fin 26)} {ctx : List (Fin 26 × Fin 26)}
    (hf : ∀ u v, F.Adj u v ↔ fAdj ctx u v = true) :
    ∀ (a : Fin 26) (l : List (Fin 26)),
      walkValidCtx ctx a l = true →
      ∀ x ∈ a :: l, F.Reachable a x := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _ x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rfl
  | cons b l ih =>
    intro hval x hx
    simp only [walkValidCtx, Bool.and_eq_true] at hval
    rcases List.mem_cons.mp hx with rfl | hx'
    · rfl
    · have hab : F.Adj a b := (hf a b).mpr hval.1
      exact hab.reachable.trans (ih b hval.2 x hx')

private lemma mem_of_closedCtx_walk {F : SimpleGraph (Fin 26)} {ctx : List (Fin 26 × Fin 26)}
    {L : List (Fin 26)} (hf : ∀ u v, F.Adj u v ↔ fAdj ctx u v = true)
    (hcl : closedCtx ctx L = true) {a b : Fin 26} (p : F.Walk a b) (ha : a ∈ L) : b ∈ L := by
  induction p with
  | nil => exact ha
  | @cons u v w huv _ ih =>
    have hv : v ∈ L := by
      have huv' : fAdj ctx u v = true := (hf u v).mp huv
      have hvu' : fAdj ctx v u = true := (hf v u).mp huv.symm
      simp only [fAdj, Bool.and_eq_true, Bool.not_eq_true'] at huv' hvu'
      have hg : G81.Adj u v := (adj_iff_adjBool u v).mpr huv'.1
      have huL : inList u L = true := inList_iff.mpr ha
      rcases hg with hmem | hmem
      · have h1 := List.all_eq_true.mp hcl (u, v) hmem
        simp only [huv'.2, Bool.false_or, beq_iff_eq, huL] at h1
        exact inList_iff.mp h1.symm
      · have h1 := List.all_eq_true.mp hcl (v, u) hmem
        simp only [hvu'.2, Bool.false_or, beq_iff_eq, huL] at h1
        exact inList_iff.mp h1
    exact ih hv

private lemma odd_card_of_cycleOk {F : SimpleGraph (Fin 26)} {ctx : List (Fin 26 × Fin 26)}
    (hf : ∀ u v, F.Adj u v ↔ fAdj ctx u v = true)
    {h : Fin 26} {t : List (Fin 26)} (hc : cycleOk ctx h t = true)
    {v : Fin 26} (hv : v ∈ h :: t) :
    Odd (Nat.card (F.connectedComponentMk v).supp) := by
  simp only [cycleOk, Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨hw, hcl⟩, hnd⟩, hodd⟩
  have hrv : F.Reachable h v := reachable_of_walkValidCtx hf h t hw v hv
  have hcomp : F.connectedComponentMk v = F.connectedComponentMk h :=
    SimpleGraph.ConnectedComponent.eq.mpr hrv.symm
  rw [hcomp]
  have hsupp : (F.connectedComponentMk h).supp = ↑((h :: t).toFinset) := by
    ext x
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
      Finset.mem_coe, List.mem_toFinset]
    constructor
    · intro hrx
      rcases hrx.symm with ⟨p⟩
      exact mem_of_closedCtx_walk hf hcl p List.mem_cons_self
    · intro hx
      exact (reachable_of_walkValidCtx hf h t hw x hx).symm
  rw [hsupp, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup (nodup_of_nodupBool hnd)]
  exact Nat.odd_iff.mpr hodd

private lemma odd_of_leafOk {F : SimpleGraph (Fin 26)}
    (hTF : SnarkGen.EdgeInsertion.IsTwoFactor G81 F)
    {ctx : List (Fin 26 × Fin 26)} {c1 c2 : Fin 26 × List (Fin 26)}
    (hl : leafOk ctx c1 c2 = true)
    (hctx : ∀ p ∈ ctx, IsMissing F p.1 p.2)
    (c : F.ConnectedComponent) : Odd (Nat.card c.supp) := by
  simp only [leafOk, Bool.and_eq_true] at hl
  rcases hl with ⟨⟨⟨hall_u, hc1⟩, hc2⟩, hcov⟩
  have hf : ∀ u v : Fin 26, F.Adj u v ↔ fAdj ctx u v = true := by
    intro u v
    simp only [fAdj, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
      inPairList_iff, ← adj_iff_adjBool]
    constructor
    · intro hfuv
      refine ⟨hTF.1 hfuv, ?_⟩
      intro hmem
      exact (hctx (u, v) hmem).2 hfuv
    · rintro ⟨hguv, hnmem⟩
      by_contra hnf
      have hmiss : IsMissing F u v := ⟨hguv, hnf⟩
      have hu := List.all_eq_true.mp hall_u u (List.mem_finRange u)
      simp only [List.any_eq_true, beq_iff_eq, ← Fin.ext_iff] at hu
      rcases hu with ⟨⟨u', w⟩, hmem, hu'⟩
      subst hu'
      have hmiss' : IsMissing F u' w := hctx (u', w) hmem
      have hvw : v = w := isMissing_unique hTF hmiss hmiss'
      subst hvw
      exact hnmem hmem
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    have hv := List.all_eq_true.mp hcov v (List.mem_finRange v)
    simp only [Bool.or_eq_true, inList_iff] at hv
    rcases hv with hv1 | hv2
    · exact odd_card_of_cycleOk hf hc1 hv1
    · exact odd_card_of_cycleOk hf hc2 hv2

private lemma eval_certTree {F : SimpleGraph (Fin 26)}
    (hTF : SnarkGen.EdgeInsertion.IsTwoFactor G81 F) :
    ∀ (t : CertTree) (ctx : List (Fin 26 × Fin 26)),
      checkTree ctx t = true →
      (∀ p ∈ ctx, IsMissing F p.1 p.2) →
      ∀ c : F.ConnectedComponent, Odd (Nat.card c.supp)
  | .leaf c1 c2, ctx, hchk, hctx, c =>
    odd_of_leafOk hTF hchk hctx c
  | .conflict u v z, ctx, hchk, hctx, _ => by
    simp only [checkTree, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq, ← Fin.ext_iff, inPairList_iff] at hchk
    rcases hchk with ⟨⟨huv, huz⟩, hvz⟩
    exact absurd (isMissing_unique hTF (hctx (u, v) huv) (hctx (u, z) huz)) hvz
  | .branch v a b c t0 t1 t2, ctx, hchk, hctx, comp => by
    simp only [checkTree, Bool.and_eq_true] at hchk
    rcases hchk with ⟨⟨⟨hn, ht0⟩, ht1⟩, ht2⟩
    rcases (nbrsOk_spec hTF (nbrsOk_of_inNbrsList hn)).1 with ha | hb | hc
    · apply eval_certTree hTF t0 ((v, a) :: (a, v) :: ctx) ht0 _ comp
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp1
      · exact ha
      · rcases List.mem_cons.mp hp1 with rfl | hp2
        · exact isMissing_symm ha
        · exact hctx p hp2
    · apply eval_certTree hTF t1 ((v, b) :: (b, v) :: ctx) ht1 _ comp
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp1
      · exact hb
      · rcases List.mem_cons.mp hp1 with rfl | hp2
        · exact isMissing_symm hb
        · exact hctx p hp2
    · apply eval_certTree hTF t2 ((v, c) :: (c, v) :: ctx) ht2 _ comp
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp1
      · exact hc
      · rcases List.mem_cons.mp hp1 with rfl | hp2
        · exact isMissing_symm hc
        · exact hctx p hp2

theorem solution : AllTwoFactorsOdd G81 := by
  intro F hTF c
  exact eval_certTree hTF theTree [] checkTree_theTree (fun _ hp => by cases hp) c
