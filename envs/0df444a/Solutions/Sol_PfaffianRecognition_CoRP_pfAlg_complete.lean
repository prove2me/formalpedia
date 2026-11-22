-- Prove2me | solution 1 for PfaffianRecognition.CoRP.pfAlg_complete
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:39:20.799935+00:00
-- url     : https://prove2.me/submissions/d60a240d-a6db-43b6-8102-16badfeea037

import Definitions.Def_PfaffianRecognition_CoRP_Algorithm
import Definitions.Def_PfaffianRecognition_Recognition_computation_model
import Definitions.Def_PfaffianRecognition_CoRP_ListLinAlg
import Definitions.Def_PfaffianRecognition_Recognition_graph_model

-- ===== from Solutions/Main/Parse.lean =====
section

namespace PfaffianRecognition.CoRP
open PfaffianRecognition.Recognition

theorem findIdx_replicate_true (N : ℕ) (rest : List Bool) :
    (List.replicate N true ++ false :: rest).findIdx (fun b => !b) = N := by
  induction N with
  | zero => simp [List.findIdx_cons]
  | succ n ih => simp [List.replicate_succ, List.findIdx_cons, ih]

theorem flatMap_getElem?_const {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (hk : ∀ a, (f a).length = k) (i j : ℕ) (hj : j < k) :
    (l.flatMap f)[i * k + j]? = (l[i]?).bind (fun a => (f a)[j]?) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rcases i with _ | i
    · rw [List.getElem?_append_left (by rw [hk]; omega)]
      simp
    · have e : (i + 1) * k + j = (f a).length + (i * k + j) := by rw [hk]; ring
      rw [e, List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ]
      exact ih i

theorem idxPairs_length (N : ℕ) : (idxPairs N).length = N * N := by
  simp [idxPairs, List.length_flatMap, List.sum_replicate]

theorem idxPairs_getElem? (N i j : ℕ) (hi : i < N) (hj : j < N) :
    (idxPairs N)[i * N + j]? = some (i, j) := by
  unfold idxPairs
  rw [flatMap_getElem?_const _ _ N (by simp) i j hj]
  simp [hi, hj]

theorem vertexPairs_length (N : ℕ) : (CatalyticMatching.General.vertexPairs N).length = N * N := by
  simp [CatalyticMatching.General.vertexPairs, List.length_flatMap, List.sum_replicate]

theorem vertexPairs_getElem? (N : ℕ) (i j : Fin N) :
    (CatalyticMatching.General.vertexPairs N)[i.val * N + j.val]? = some (i, j) := by
  unfold CatalyticMatching.General.vertexPairs
  rw [flatMap_getElem?_const _ _ N (by simp) i j j.2]
  simp


open CatalyticMatching.General in
theorem hdrN_graphBits {N : ℕ} (G : SimpleGraph (Fin N)) : hdrN (graphBits G) = N := by
  classical
  unfold hdrN graphBits
  simp only [List.append_assoc, List.singleton_append]
  convert findIdx_replicate_true N _

theorem drop_replicate_true (N : ℕ) (rest : List Bool) :
    (List.replicate N true ++ false :: rest).drop (N + 1) = rest := by
  induction N with
  | zero => simp
  | succ n ih => simpa [List.replicate_succ] using ih

open CatalyticMatching.General in
theorem encBody_graphBits {N : ℕ} (G : SimpleGraph (Fin N)) :
    ∃ f : Fin N × Fin N → Bool, (∀ ij, f ij = true ↔ G.Adj ij.1 ij.2) ∧
      encBody (graphBits G) = (vertexPairs N).map f := by
  classical
  refine ⟨fun ij => decide (G.Adj ij.1 ij.2), fun ij => by simp, ?_⟩
  unfold encBody
  rw [hdrN_graphBits]
  unfold graphBits
  simp only [List.append_assoc, List.singleton_append]
  convert drop_replicate_true N _

theorem encBody_graphBits_length {N : ℕ} (G : SimpleGraph (Fin N)) :
    (encBody (CatalyticMatching.General.graphBits G)).length = N * N := by
  obtain ⟨f, -, hf⟩ := encBody_graphBits G
  rw [hf, List.length_map, vertexPairs_length]

theorem adjBit_graphBits {N : ℕ} (G : SimpleGraph (Fin N)) (i j : Fin N) :
    adjBit (CatalyticMatching.General.graphBits G) i j = true ↔ G.Adj i j := by
  obtain ⟨f, hf1, hf⟩ := encBody_graphBits G
  unfold adjBit
  rw [hdrN_graphBits, hf, List.getD_eq_getElem?_getD, List.getElem?_map, vertexPairs_getElem?]
  simpa using hf1 (i, j)

theorem mem_idxPairs (N : ℕ) (ij : ℕ × ℕ) : ij ∈ idxPairs N ↔ ij.1 < N ∧ ij.2 < N := by
  unfold idxPairs
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩; exact ⟨hi, hj⟩
  · rintro ⟨h1, h2⟩; exact ⟨ij.1, h1, ij.2, h2, rfl⟩

theorem validEnc_graphBits {N : ℕ} (G : SimpleGraph (Fin N)) :
    validEnc (CatalyticMatching.General.graphBits G) = true := by
  unfold validEnc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hdrN_graphBits]; unfold CatalyticMatching.General.graphBits; simp
  · rw [hdrN_graphBits, encBody_graphBits_length]
  · intro ij hij
    rw [hdrN_graphBits, mem_idxPairs] at hij
    obtain ⟨h1, h2⟩ := hij
    have e1 := adjBit_graphBits G ⟨ij.1, h1⟩ ⟨ij.2, h2⟩
    have e2 := adjBit_graphBits G ⟨ij.2, h2⟩ ⟨ij.1, h1⟩
    simp only at e1 e2
    refine ⟨?_, ?_⟩
    · cases h : adjBit (CatalyticMatching.General.graphBits G) ij.1 ij.2 <;>
        cases h' : adjBit (CatalyticMatching.General.graphBits G) ij.2 ij.1 <;> simp_all [G.adj_comm]
    · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      by_cases hij : ij.1 = ij.2
      · right
        have : ¬ G.Adj ⟨ij.1, h1⟩ ⟨ij.2, h2⟩ := by
          have : (⟨ij.1, h1⟩ : Fin N) = ⟨ij.2, h2⟩ := Fin.ext hij
          rw [this]; exact G.irrefl
        cases h : adjBit (CatalyticMatching.General.graphBits G) ij.1 ij.2 <;> simp_all
      · left; exact hij


/-- The graph read off a (valid) encoding. -/
def encGraph (w : List Bool) (hw : validEnc w = true) : SimpleGraph (Fin (hdrN w)) where
  Adj i j := adjBit w i j = true
  symm := by
    refine ⟨fun i j h => ?_⟩
    unfold validEnc at hw
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hw
    have := (hw.2 (i, j) ((mem_idxPairs _ _).2 ⟨i.2, j.2⟩)).1
    simp only at this
    rw [← this]; exact h
  loopless := by
    refine ⟨fun i h => ?_⟩
    unfold validEnc at hw
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hw
    have := (hw.2 (i, i) ((mem_idxPairs _ _).2 ⟨i.2, i.2⟩)).2
    simp_all

theorem encGraph_adj (w : List Bool) (hw : validEnc w = true) (i j : Fin (hdrN w)) :
    (encGraph w hw).Adj i j ↔ adjBit w i j = true := Iff.rfl

theorem graphBits_encGraph (w : List Bool) (hw : validEnc w = true) :
    CatalyticMatching.General.graphBits (encGraph w hw) = w := by
  classical
  have hw' := hw
  unfold validEnc at hw'
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hw'
  obtain ⟨⟨hlt, hlen⟩, -⟩ := hw'
  have hfalse : w[hdrN w] = false := by
    have := List.findIdx_getElem (w := hlt)
    simp only [Bool.not_eq_true'] at this
    exact this
  have htake : w.take (hdrN w) = List.replicate (hdrN w) true := by
    apply List.eq_replicate_iff.2
    refine ⟨by simp; omega, fun b hb => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    simp only [List.length_take] at hk
    have hk' : k < List.findIdx (fun b => !b) w := lt_of_lt_of_le hk (Nat.min_le_left _ _)
    have := List.not_of_lt_findIdx hk'
    simpa using this
  have hsplit : w = List.replicate (hdrN w) true ++ [false] ++ encBody w := by
    conv_lhs => rw [← List.take_append_drop (hdrN w) w]
    rw [htake, List.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, hfalse]
    rfl
  conv_rhs => rw [hsplit]
  unfold CatalyticMatching.General.graphBits
  congr 1
  apply List.ext_getElem
  · simp [vertexPairs_length, hlen]
  · intro k hk1 hk2
    simp only [List.length_map, vertexPairs_length] at hk1
    rw [List.getElem_map]
    have hNpos : 0 < hdrN w := by
      rcases Nat.eq_zero_or_pos (hdrN w) with h | h
      · rw [h] at hk1; simp at hk1
      · exact h
    have hk : k = (k / hdrN w) * hdrN w + k % hdrN w := (Nat.div_add_mod' k _).symm
    have hq : k / hdrN w < hdrN w := by
      rw [Nat.div_lt_iff_lt_mul hNpos]; exact hk1
    have hr : k % hdrN w < hdrN w := Nat.mod_lt _ hNpos
    have hv := vertexPairs_getElem? (hdrN w) ⟨k / hdrN w, hq⟩ ⟨k % hdrN w, hr⟩
    simp only at hv
    rw [← hk] at hv
    have hv' : (CatalyticMatching.General.vertexPairs (hdrN w))[k]'(by rw [vertexPairs_length]; exact hk1) =
        (⟨k / hdrN w, hq⟩, ⟨k % hdrN w, hr⟩) := by
      rw [List.getElem?_eq_getElem (by rw [vertexPairs_length]; exact hk1)] at hv
      exact Option.some.inj hv
    simp only [hv', encGraph]
    unfold adjBit
    rw [← hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2]
    simp

end PfaffianRecognition.CoRP

end

-- ===== from Solutions/Main/Edges.lean =====
section

namespace PfaffianRecognition.CoRP
open PfaffianRecognition.Recognition

variable {N : ℕ} {G : SimpleGraph (Fin N)}

theorem edge_eq_lo_hi (e : G.edgeSet) : (e : Sym2 (Fin N)) = s(edgeLo e, edgeHi e) := by
  unfold edgeLo edgeHi
  have h : (e : Sym2 (Fin N)) = s(e.val.out.1, e.val.out.2) := (Quot.out_eq e.val).symm
  rcases le_total e.val.out.1 e.val.out.2 with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]; exact h
  · rw [min_eq_right hle, max_eq_left hle, Sym2.eq_swap]; exact h

theorem edgeLo_lt_edgeHi (e : G.edgeSet) : edgeLo e < edgeHi e := by
  have hadj : G.Adj (edgeLo e) (edgeHi e) := by
    have := e.2; rw [edge_eq_lo_hi] at this; exact this
  have hne : edgeLo e ≠ edgeHi e := G.ne_of_adj hadj
  exact lt_of_le_of_ne (by unfold edgeLo edgeHi; exact min_le_max) hne

theorem edge_adj (e : G.edgeSet) : G.Adj (edgeLo e) (edgeHi e) := by
  have := e.2; rw [edge_eq_lo_hi] at this; exact this

theorem edgeLo_hi_of_eq (e : G.edgeSet) (a b : Fin N) (hab : a < b) (h : (e : Sym2 (Fin N)) = s(a, b)) :
    edgeLo e = a ∧ edgeHi e = b := by
  rw [edge_eq_lo_hi] at h
  have hlt := edgeLo_lt_edgeHi e
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exfalso; rw [h1, h2] at hlt; exact lt_asymm hlt hab

theorem mem_edge_iff (e : G.edgeSet) (v : Fin N) : v ∈ (e : Sym2 (Fin N)) ↔ v = edgeLo e ∨ v = edgeHi e := by
  rw [edge_eq_lo_hi]; simp

/-- An edge as a pair of natural numbers (smaller endpoint first). -/
noncomputable def toPair (e : G.edgeSet) : ℕ × ℕ := ((edgeLo e : ℕ), (edgeHi e : ℕ))

theorem toPair_injective : Function.Injective (toPair (G := G)) := by
  intro e f h
  simp only [toPair, Prod.mk.injEq] at h
  apply Subtype.ext
  rw [edge_eq_lo_hi, edge_eq_lo_hi, Fin.ext h.1, Fin.ext h.2]


theorem toPair_lt (e : G.edgeSet) : (toPair e).1 < (toPair e).2 ∧ (toPair e).2 < N :=
  ⟨edgeLo_lt_edgeHi e, (edgeHi e).2⟩

theorem mem_encEdges_graphBits (p : ℕ × ℕ) :
    p ∈ encEdges (CatalyticMatching.General.graphBits G) ↔ ∃ e : G.edgeSet, toPair e = p := by
  unfold encEdges
  rw [List.mem_filter, hdrN_graphBits, mem_idxPairs]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, hlt, hadj⟩
    have hadj' := (adjBit_graphBits G ⟨p.1, h1⟩ ⟨p.2, h2⟩).1 hadj
    refine ⟨⟨s(⟨p.1, h1⟩, ⟨p.2, h2⟩), G.mem_edgeSet.2 hadj'⟩, ?_⟩
    obtain ⟨hl, hh⟩ := edgeLo_hi_of_eq (G := G) ⟨s(⟨p.1, h1⟩, ⟨p.2, h2⟩), G.mem_edgeSet.2 hadj'⟩
      ⟨p.1, h1⟩ ⟨p.2, h2⟩ (by simpa [Fin.lt_def] using hlt) rfl
    simp [toPair, hl, hh]
  · rintro ⟨e, rfl⟩
    refine ⟨toPair_lt e |>.elim (fun a b => ⟨lt_trans a b, b⟩), (toPair_lt e).1, ?_⟩
    have := (adjBit_graphBits G (edgeLo e) (edgeHi e)).2 (edge_adj e)
    simpa [toPair] using this

theorem encEdges_nodup (w : List Bool) : (encEdges w).Nodup := by
  unfold encEdges idxPairs
  apply List.Nodup.filter
  apply List.nodup_flatMap.2
  refine ⟨fun i _ => (List.nodup_range).map (fun a b h => by simpa using h), ?_⟩
  apply List.Pairwise.imp_of_mem _ (List.nodup_range)
  intro a b _ _ hab
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range]
  rintro x ⟨j, -, rfl⟩ ⟨j', -, h⟩
  simp at h; exact hab h.1.symm


/-- The edge set of a list of pairs. -/
noncomputable def pmSet (S : List (ℕ × ℕ)) : Finset G.edgeSet := by
  classical exact Finset.univ.filter (fun e => toPair e ∈ S)

theorem mem_pmSet (S : List (ℕ × ℕ)) (e : G.edgeSet) : e ∈ pmSet S ↔ toPair e ∈ S := by
  classical
  unfold pmSet; simp

theorem eq_of_filter_length_one {α : Type} (l : List α) (q : α → Bool) (hl : (l.filter q).length = 1)
    (a b : α) (ha : a ∈ l) (hb : b ∈ l) (hqa : q a = true) (hqb : q b = true) : a = b := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl
  have h1 : a ∈ l.filter q := List.mem_filter.2 ⟨ha, hqa⟩
  have h2 : b ∈ l.filter q := List.mem_filter.2 ⟨hb, hqb⟩
  rw [hx] at h1 h2
  simp at h1 h2; rw [h1, h2]

theorem nodup_of_filter_length_one {α β : Type} [DecidableEq α] (l : List α) (q : β → α → Bool)
    (hq : ∀ a, ∃ v, q v a = true)
    (hl : ∀ v, (l.filter (q v)).length ≤ 1) : l.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro a
  obtain ⟨v, hv⟩ := hq a
  have h1 := hl v
  have h2 : (l.filter (q v)).count a = l.count a := List.count_filter hv
  have h3 : (l.filter (q v)).count a ≤ (l.filter (q v)).length := List.count_le_length
  omega

/-- List-level perfect matchings correspond to perfect matchings of `G`. -/
theorem isPMList_spec (S : List (ℕ × ℕ))
    (h : isPMList N (encEdges (CatalyticMatching.General.graphBits G)) S = true) :
    MulmuleyVV.Matching.IsPerfectMatchingEdges G (pmSet S) ∧ S.Nodup ∧
      (∀ p ∈ S, ∃ e : G.edgeSet, toPair e = p) := by
  unfold isPMList at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨hcov, hsub⟩ := h
  have hsub' : ∀ p ∈ S, ∃ e : G.edgeSet, toPair e = p := fun p hp =>
    (mem_encEdges_graphBits p).1 (hsub p hp)
  refine ⟨?_, ?_, hsub'⟩
  · intro v
    have hv := hcov v v.2
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hv
    have hxmem : x ∈ S.filter (fun f => f.1 == ↑v || f.2 == ↑v) := by rw [hx]; simp
    rw [List.mem_filter] at hxmem
    obtain ⟨e, rfl⟩ := hsub' x hxmem.1
    refine ⟨e, ⟨(mem_pmSet S e).2 hxmem.1, ?_⟩, ?_⟩
    · rw [mem_edge_iff]
      simp only [toPair, Bool.or_eq_true, beq_iff_eq] at hxmem
      rcases hxmem.2 with h | h
      · left; exact Fin.ext h.symm
      · right; exact Fin.ext h.symm
    · rintro f ⟨hf, hvf⟩
      rw [mem_pmSet] at hf
      apply toPair_injective
      apply eq_of_filter_length_one S _ hv _ _ hf ((mem_pmSet S e).1 ((mem_pmSet S e).2 hxmem.1))
      · rw [mem_edge_iff] at hvf
        simp only [toPair, Bool.or_eq_true, beq_iff_eq]
        rcases hvf with h | h
        · left; rw [h]
        · right; rw [h]
      · exact hxmem.2
  · apply nodup_of_filter_length_one S (fun v f => f.1 == v || f.2 == v)
    · intro a; exact ⟨a.1, by simp⟩
    · intro v
      by_cases hv : v < N
      · rw [hcov v hv]
      · have : S.filter (fun f => f.1 == v || f.2 == v) = [] := by
          apply List.filter_eq_nil_iff.2
          intro f hf
          obtain ⟨e, rfl⟩ := hsub' f hf
          have := toPair_lt e
          simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true, beq_eq_false_iff_ne]
          constructor <;> omega
        rw [this]; simp


theorem crossCond_iff (e f : G.edgeSet) :
    (decide ((toPair e).1 < (toPair f).1) && decide ((toPair f).1 < (toPair e).2) &&
      decide ((toPair e).2 < (toPair f).2)) = true ↔ (edgeLo e < edgeLo f ∧ Crosses e f) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  simp only [toPair, Crosses, Fin.lt_def]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, Or.inl ⟨h1, h2, h3⟩⟩
  · rintro ⟨h1, (⟨-, h2, h3⟩ | ⟨h4, -, -⟩)⟩
    · exact ⟨⟨h1, h2⟩, h3⟩
    · omega

theorem product_nodup {α : Type} (S : List α) (hS : S.Nodup) :
    (S.flatMap (fun e => S.map (fun f => (e, f)))).Nodup := by
  apply List.nodup_flatMap.2
  refine ⟨fun e _ => hS.map (fun a b h => by simpa using h), ?_⟩
  apply List.Pairwise.imp_of_mem _ hS
  intro a b _ _ hab
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro x ⟨j, -, rfl⟩ ⟨j', -, h⟩
  simp at h; exact hab h.1.symm

theorem crossCount_eq (S : List (ℕ × ℕ)) (hS : S.Nodup) (himg : ∀ p ∈ S, ∃ e : G.edgeSet, toPair e = p) :
    crossCount S = ((crossingPairs G).filter (fun ef => ef.1 ∈ pmSet S ∧ ef.2 ∈ pmSet S)).card := by
  classical
  unfold crossCount crossPairs
  have hnd := (product_nodup S hS).filter
    (fun ef => decide (ef.1.1 < ef.2.1) && decide (ef.2.1 < ef.1.2) && decide (ef.1.2 < ef.2.2))
  rw [← List.toFinset_card_of_nodup hnd]
  rw [← Finset.card_image_of_injective _ (f := fun ef : G.edgeSet × G.edgeSet => (toPair ef.1, toPair ef.2))
    (by intro a b h; simp only [Prod.mk.injEq] at h; exact Prod.ext (toPair_injective h.1) (toPair_injective h.2))]
  congr 1
  ext q
  simp only [List.mem_toFinset, List.mem_filter, List.mem_flatMap, List.mem_map, Finset.mem_image,
    Finset.mem_filter, crossingPairs, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, hc⟩
    obtain ⟨e, rfl⟩ := himg a ha
    obtain ⟨f, rfl⟩ := himg b hb
    exact ⟨(e, f), ⟨(crossCond_iff e f).1 hc, (mem_pmSet S e).2 ha, (mem_pmSet S f).2 hb⟩, rfl⟩
  · rintro ⟨⟨e, f⟩, ⟨hc, he, hf⟩, rfl⟩
    exact ⟨⟨toPair e, (mem_pmSet S e).1 he, toPair f, (mem_pmSet S f).1 hf, rfl⟩, (crossCond_iff e f).2 hc⟩


/-- Backward-edge indicator of an orientation, on pairs of natural numbers. -/
noncomputable def bkOf (D : Orientation G) (p : ℕ × ℕ) : Bool := by
  classical
  exact if h : p.1 < N ∧ p.2 < N then decide (D.val ⟨p.2, h.2⟩ ⟨p.1, h.1⟩) else false

theorem bkOf_toPair (D : Orientation G) (e : G.edgeSet) :
    bkOf D (toPair e) = true ↔ D.val (edgeHi e) (edgeLo e) := by
  classical
  unfold bkOf
  have h := toPair_lt e
  rw [dif_pos ⟨lt_trans h.1 h.2, h.2⟩]
  simp only [toPair, Fin.eta]
  exact decide_eq_true_iff

theorem zip_map_self {α β : Type} (l : List α) (f : α → β) :
    l.zip (l.map f) = l.map (fun p => (p, f p)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem dCount_map (E : List (ℕ × ℕ)) (f : ℕ × ℕ → Bool) (S : List (ℕ × ℕ)) :
    dCount E (E.map f) S = (E.filter (fun p => f p && S.contains p)).length := by
  unfold dCount
  rw [zip_map_self, List.filter_map, List.length_map]
  rfl

theorem dCount_bkOf (D : Orientation G) (S : List (ℕ × ℕ)) :
    dCount (encEdges (CatalyticMatching.General.graphBits G))
        ((encEdges (CatalyticMatching.General.graphBits G)).map (bkOf D)) S =
      (pmSet S ∩ backwardEdges D).card := by
  classical
  rw [dCount_map]
  have hnd := (encEdges_nodup (CatalyticMatching.General.graphBits G)).filter
    (fun p => bkOf D p && S.contains p)
  rw [← List.toFinset_card_of_nodup hnd]
  rw [← Finset.card_image_of_injective _ (toPair_injective (G := G))]
  congr 1
  ext q
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_image, Finset.mem_inter,
    backwardEdges, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
    List.contains_iff_mem, mem_encEdges_graphBits]
  constructor
  · rintro ⟨⟨e, rfl⟩, hb, hs⟩
    exact ⟨e, ⟨(mem_pmSet S e).2 hs, (bkOf_toPair D e).1 hb⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hb⟩, rfl⟩
    exact ⟨⟨e, rfl⟩, (bkOf_toPair D e).2 hb, (mem_pmSet S e).1 hs⟩

end PfaffianRecognition.CoRP

end

-- ===== from Solutions/Main/EqnLemmas.lean =====
section

namespace PfaffianRecognition.CoRP

theorem range_filter_zip {α β : Type} (E : List α) (d : List β) (hd : d.length = E.length)
    (f : α → β → Bool) (a0 : α) (b0 : β) :
    ((List.range E.length).filter (fun i => f (E.getD i a0) (d.getD i b0))).length =
      ((E.zip d).filter (fun p => f p.1 p.2)).length := by
  induction E generalizing d with
  | nil => simp
  | cons a E ih =>
    cases d with
    | nil => simp at hd
    | cons b d =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hd
      rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.zip_cons_cons,
        List.filter_cons]
      simp only [List.getD_cons_zero, List.filter_map, List.length_map, List.getD_cons_succ]
      have := ih d hd
      split <;> simp_all [Function.comp_def]

theorem matchEqn_length (E S : List (ℕ × ℕ)) : (matchEqn E S).1.length = E.length + 1 := by
  simp [matchEqn]

theorem satisfies_matchEqn (E S : List (ℕ × ℕ)) (d : List Bool) (s : Bool)
    (hd : d.length = E.length) :
    satisfiesEqn (d ++ [s]) (matchEqn E S) = !violates E d s S := by
  unfold satisfiesEqn violates
  rw [matchEqn_length, List.range_succ, List.filter_append, List.length_append]
  have h1 : ((List.range E.length).filter (fun i => (matchEqn E S).1.getD i false &&
      (d ++ [s]).getD i false)).length = dCount E d S := by
    have : ((List.range E.length).filter (fun i => (matchEqn E S).1.getD i false &&
        (d ++ [s]).getD i false)) = ((List.range E.length).filter
          (fun i => (fun (a : ℕ × ℕ) (b : Bool) => b && S.contains a) (E.getD i (0, 0)) (d.getD i false))) := by
      apply List.filter_congr
      intro i hi
      rw [List.mem_range] at hi
      simp only [matchEqn, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simpa using hi), List.getElem?_append_left (by omega),
        List.getElem?_map]
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)]
      simp [Bool.and_comm]
    rw [this]
    exact range_filter_zip E d hd (fun (a : ℕ × ℕ) (b : Bool) => b && S.contains a) (0, 0) false
  rw [h1]
  have h2 : ((List.filter (fun i => (matchEqn E S).1.getD i false && (d ++ [s]).getD i false)
      [E.length]).length) = if s then 1 else 0 := by
    simp only [List.filter_cons, List.filter_nil, matchEqn, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by omega)]
    cases s <;> simp [hd]
  rw [h2]
  simp only [matchEqn]
  rcases Nat.mod_two_eq_zero_or_one (crossCount S) with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (dCount E d S + if s = true then 1 else 0) with hb | hb <;>
    simp [Nat.add_mod, ha, hb, Nat.add_assoc] <;> omega

end PfaffianRecognition.CoRP

end

-- ===== from Solutions/Lib/LinAlg.lean =====
section

namespace PfaffianRecognition.CoRP

theorem foldl_range_iterate {σ : Type} (f : σ → σ) (k : ℕ) (s : σ) :
    (List.range k).foldl (fun st _ => f st) s = f^[k] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ_apply']
    rfl

theorem elimStep_nil {α : Type} (F : FieldOps α) (a : α) : elimStep F ([], a) = ([], a) := by
  simp [elimStep]

theorem elimStep_iter_nil {α : Type} (F : FieldOps α) (a : α) (k : ℕ) :
    (elimStep F)^[k] ([], a) = ([], a) :=
  Function.iterate_fixed (elimStep_nil F a) k

theorem eraseIdx_ofFn {β : Type} {n : ℕ} (f : Fin (n + 1) → β) (k : Fin (n + 1)) :
    (List.ofFn f).eraseIdx k = List.ofFn (fun i : Fin n => f (k.succAbove i)) := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx]; omega
  · intro j h1 h2
    rw [List.getElem_eraseIdx]
    simp only [List.getElem_ofFn]
    split_ifs with hj
    · rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · simpa [Fin.lt_def] using hj
    · rw [Fin.succAbove_of_le_castSucc]
      · rfl
      · simp only [Fin.le_def, Fin.val_castSucc]; omega

theorem elimRow_ofFn {K : Type} [Field K] [DecidableEq K] {n : ℕ} (c : K) (g f : Fin (n + 1) → K) :
    elimRow (stdOps K) c (List.ofFn g) (List.ofFn f)
      = List.ofFn (fun j : Fin n => f j.succ + -(f 0 * c * g j.succ)) := by
  apply List.ext_getElem
  · simp [elimRow]
  · intro j h1 h2
    simp [elimRow, stdOps, List.ofFn_succ]

theorem det_pivot {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (k : Fin (n + 1)) (hp : A k 0 ≠ 0) :
    A.det = (-1) ^ (k : ℕ) * A k 0 *
      (Matrix.of (fun (i j : Fin n) => A (k.succAbove i) j.succ +
        -(A (k.succAbove i) 0 * (A k 0)⁻¹ * A k j.succ))).det := by
  classical
  let c : Fin (n + 1) → K := fun i => if i = k then 0 else -(A i 0 * (A k 0)⁻¹)
  let A' : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of (fun i j => A i j + c i * A k j)
  have h1 : A'.det = A.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c k (by simp [c]) (fun i j => rfl)
  rw [← h1, Matrix.det_succ_column_zero, Finset.sum_eq_single k]
  · congr 2
    · simp [A', c]
    · ext i j
      have := Fin.succAbove_ne k i
      simp [A', c, this]
  · intro i _ hik
    have : A' i 0 = 0 := by
      simp only [A', c, Matrix.of_apply, if_neg hik]
      field_simp
      ring
    simp [this]
  · simp


theorem detAlg_iter {K : Type} [Field K] [DecidableEq K] (n : ℕ) :
    ∀ (A : Matrix (Fin n) (Fin n) K) (acc : K),
      ((elimStep (stdOps K))^[n] (List.ofFn (fun i => List.ofFn (A i)), acc)).2 = acc * A.det := by
  induction n with
  | zero => intro A acc; simp
  | succ n ih =>
    intro A acc
    rw [Function.iterate_succ_apply]
    set rows := List.ofFn (fun i => List.ofFn (A i)) with hrows
    have hne : rows.isEmpty = false := by simp [rows, List.ofFn_succ]
    have hlen : rows.length = n + 1 := by simp [rows]
    have hhead : ∀ i, (List.ofFn (A i)).headD 0 = A i 0 := by intro i; simp [List.ofFn_succ]
    by_cases h : pivotIdx (stdOps K) rows < rows.length
    · set k := pivotIdx (stdOps K) rows with hk
      let kf : Fin (n + 1) := ⟨k, by omega⟩
      have hget : rows.getD k [] = List.ofFn (A kf) := by
        rw [List.getD_eq_getElem _ _ h]; simp only [rows, List.getElem_ofFn]; rfl
      have hp : A kf 0 ≠ 0 := by
        have e : rows[k]'h = List.ofFn (A kf) := by simp only [rows, List.getElem_ofFn]; rfl
        have := List.findIdx_getElem (w := h)
        change (!decide ((rows[k]'h).headD 0 = 0)) = true at this
        rw [e, hhead] at this
        simpa using this
      have hstep : elimStep (stdOps K) (rows, acc)
          = (List.ofFn (fun i => List.ofFn ((Matrix.of (fun (i j : Fin n) => A (kf.succAbove i) j.succ +
              -(A (kf.succAbove i) 0 * (A kf 0)⁻¹ * A kf j.succ))) i)),
            acc * (if k % 2 = 0 then A kf 0 else -A kf 0)) := by
        simp only [elimStep, hne, h, ← hk, hget]
        simp only [Bool.false_eq_true, if_false, if_true, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        swap
        · show acc * (if k % 2 = 0 then (List.ofFn (A kf)).headD 0
            else -((List.ofFn (A kf)).headD 0)) = _
          rw [hhead]
        have : rows.eraseIdx k = List.ofFn (fun i : Fin n => List.ofFn (A (kf.succAbove i))) := by
          have := eraseIdx_ofFn (fun i => List.ofFn (A i)) kf
          simpa [rows, kf] using this
        rw [this, List.map_ofFn]
        congr 1
        funext i
        simp only [Function.comp]
        rw [elimRow_ofFn]
        change List.ofFn (fun j => A (kf.succAbove i) j.succ +
          -(A (kf.succAbove i) 0 * ((List.ofFn (A kf)).headD 0)⁻¹ * A kf j.succ)) = _
        rw [hhead]
        rfl
      rw [hstep, ih, det_pivot A kf hp, mul_assoc]
      congr 1
      have : (kf : ℕ) = k := rfl
      rw [this]
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · rw [if_pos (by omega), hm, ← two_mul, pow_mul]; simp
      · rw [if_neg (by omega), hm, pow_succ, pow_mul]; simp
    · have hstep : elimStep (stdOps K) (rows, acc) = ([], 0) := by
        simp only [elimStep, hne, h]; rfl
      rw [hstep, elimStep_iter_nil]
      have hz : A.det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero 0
        intro i
        have h' : pivotIdx (stdOps K) rows = rows.length := by
          have := List.findIdx_le_length (p := fun r => !(stdOps K).isZero (r.headD (stdOps K).zero))
            (xs := rows)
          unfold pivotIdx at h ⊢; omega
        unfold pivotIdx at h'
        rw [List.findIdx_eq_length] at h'
        have := h' (List.ofFn (A i)) (by rw [List.mem_ofFn]; exact ⟨i, rfl⟩)
        change (!decide ((List.ofFn (A i)).headD 0 = 0)) = false at this
        rw [hhead] at this
        simpa using this
      simp [hz]

theorem detAlg_stdOps {K : Type} [Field K] [DecidableEq K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K) :
    detAlg (stdOps K) (List.ofFn (fun i => List.ofFn (A i))) = A.det := by
  unfold detAlg
  rw [foldl_range_iterate, List.length_ofFn, detAlg_iter]
  show 1 * A.det = A.det
  rw [one_mul]

theorem listSum_map {α β : Type} (F : FieldOps α) (G : FieldOps β) (φ : α → β)
    (hzero : φ F.zero = G.zero) (hadd : ∀ a b, φ (F.add a b) = G.add (φ a) (φ b))
    (xs : List α) : φ (listSum F xs) = listSum G (xs.map φ) := by
  have key : ∀ (ys : List α) (a : α), φ (ys.foldl F.add a) = (ys.map φ).foldl G.add (φ a) := by
    intro ys
    induction ys with
    | nil => intro a; rfl
    | cons y ys ih => intro a; simp [ih, hadd]
  unfold listSum
  rw [key, hzero]

theorem listSum_stdOps {K : Type} [Field K] [DecidableEq K] (xs : List K) :
    listSum (stdOps K) xs = xs.sum := by
  rw [List.sum_eq_foldl]; rfl

theorem detAlg_map {α β : Type} (F : FieldOps α) (G : FieldOps β) (φ : α → β)
    (hzero : φ F.zero = G.zero) (hone : φ F.one = G.one)
    (hadd : ∀ a b, φ (F.add a b) = G.add (φ a) (φ b)) (hneg : ∀ a, φ (F.neg a) = G.neg (φ a))
    (hmul : ∀ a b, φ (F.mul a b) = G.mul (φ a) (φ b)) (hinv : ∀ a, φ (F.inv a) = G.inv (φ a))
    (hz : ∀ a, F.isZero a = G.isZero (φ a)) (M : List (List α)) :
    φ (detAlg F M) = detAlg G (M.map (List.map φ)) := by
  let mS : List (List α) × α → List (List β) × β := fun st => (st.1.map (List.map φ), φ st.2)
  have hhead : ∀ r : List α, (r.map φ).headD G.zero = φ (r.headD F.zero) := by
    intro r; cases r <;> simp [hzero]
  have hpiv : ∀ rows : List (List α), pivotIdx G (rows.map (List.map φ)) = pivotIdx F rows := by
    intro rows
    unfold pivotIdx
    rw [List.findIdx_map]
    congr 1
    funext r
    simp only [Function.comp, hhead, hz]
  have hgetD : ∀ (rows : List (List α)) (k : ℕ),
      (rows.map (List.map φ)).getD k [] = (rows.getD k []).map φ := by
    intro rows k
    have := List.getD_map rows [] (n := k) (List.map φ)
    simpa using this
  have hrow : ∀ (pinv : α) (piv row : List α),
      elimRow G (φ pinv) (piv.map φ) (row.map φ) = (elimRow F pinv piv row).map φ := by
    intro pinv piv row
    unfold elimRow
    rw [← List.map_tail, ← List.map_tail, List.zip_map, List.map_map, List.map_map, hhead]
    congr 1
    funext ab
    simp [hadd, hneg, hmul]
  have hstep : ∀ st, elimStep G (mS st) = mS (elimStep F st) := by
    rintro ⟨rows, acc⟩
    simp only [mS, elimStep, List.isEmpty_map, hpiv, List.length_map, hgetD, hhead]
    split_ifs with h1 h2
    · rfl
    · simp only [Prod.mk.injEq]
      constructor
      · rw [List.eraseIdx_map, List.map_map, List.map_map]
        refine List.map_congr_left ?_
        intro r _
        simp only [Function.comp, ← hinv, hrow]
      · simp [hmul]
    · simp only [Prod.mk.injEq]
      constructor
      · rw [List.eraseIdx_map, List.map_map, List.map_map]
        refine List.map_congr_left ?_
        intro r _
        simp only [Function.comp, ← hinv, hrow]
      · simp [hmul, hneg]
    · simp [hzero]
  have hfold : ∀ (l : List ℕ) st, l.foldl (fun st _ => elimStep G st) (mS st)
      = mS (l.foldl (fun st _ => elimStep F st) st) := by
    intro l
    induction l with
    | nil => intro st; rfl
    | cons a l ih => intro st; simp only [List.foldl_cons, hstep, ih]
  unfold detAlg
  rw [List.length_map]
  have h0 : ((M.map (List.map φ)), G.one) = mS (M, F.one) := by simp [mS, hone]
  rw [h0, hfold]

/-- Boolean to `ZMod 2`. -/
def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_inj (a b : Bool) : b2z a = b2z b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem b2z_false : b2z false = 0 := rfl
theorem b2z_true : b2z true = 1 := rfl

theorem b2z_mod (k : ℕ) : b2z (k % 2 == 1) = (k : ZMod 2) := by
  rw [← ZMod.natCast_mod k 2]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> decide

theorem cast_filter_length (f : ℕ → Bool) (N : ℕ) :
    (((List.range N).filter f).length : ZMod 2) = ∑ i ∈ Finset.range N, b2z (f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, Nat.cast_add, ih,
      Finset.sum_range_succ]
    congr 1
    cases h : f N <;> simp [List.filter, h, b2z]

theorem sat_iff (x : List Bool) (e : Eqn) (N : ℕ) (hN : e.1.length ≤ N) :
    satisfiesEqn x e = true ↔
      ∑ i ∈ Finset.range N, b2z (e.1.getD i false) * b2z (x.getD i false) = b2z e.2 := by
  unfold satisfiesEqn
  rw [beq_iff_eq, ← b2z_inj, b2z_mod, cast_filter_length]
  simp only [b2z_and]
  have : ∑ i ∈ Finset.range e.1.length, b2z (e.1.getD i false) * b2z (x.getD i false)
      = ∑ i ∈ Finset.range N, b2z (e.1.getD i false) * b2z (x.getD i false) := by
    apply Finset.sum_subset
    · intro i; simp only [Finset.mem_range]; omega
    · intro i _ hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [List.getD_eq_default _ _ hi, b2z_false, zero_mul]
  rw [this]

theorem getD_addEqn (e f : Eqn) (i : ℕ) :
    (addEqn e f).1.getD i false = xor (e.1.getD i false) (f.1.getD i false) := by
  unfold addEqn
  by_cases h : i < max e.1.length f.1.length
  · simp [List.getD_eq_getElem?_getD, h]
  · simp only [not_lt, max_le_iff] at h
    rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ h.1,
      List.getD_eq_default _ _ h.2]
    rfl

theorem sat_addEqn (x : List Bool) (e f : Eqn) :
    satisfiesEqn x (addEqn e f) = true ↔ (satisfiesEqn x e = true ↔ satisfiesEqn x f = true) := by
  have hl : (addEqn e f).1.length = max e.1.length f.1.length := by simp [addEqn]
  rw [sat_iff x (addEqn e f) _ hl.le, sat_iff x e (max e.1.length f.1.length) (le_max_left _ _),
    sat_iff x f (max e.1.length f.1.length) (le_max_right _ _)]
  simp only [getD_addEqn, b2z_xor, add_mul, Finset.sum_add_distrib]
  have h2 : (addEqn e f).2 = xor e.2 f.2 := rfl
  rw [h2, b2z_xor]
  generalize ∑ i ∈ Finset.range (max e.1.length f.1.length),
    b2z (e.1.getD i false) * b2z (x.getD i false) = a
  generalize ∑ i ∈ Finset.range (max e.1.length f.1.length),
    b2z (f.1.getD i false) * b2z (x.getD i false) = b
  generalize b2z e.2 = c
  generalize b2z f.2 = d
  revert a b c d
  decide

theorem sat_nil (x : List Bool) : satisfiesEqn x ([], false) = true := by
  simp [satisfiesEqn]

theorem sat_set_irrel (x : List Bool) (e : Eqn) (m : ℕ) (v : Bool) (he : e.1.getD m false = false) :
    satisfiesEqn (x.set m v) e = satisfiesEqn x e := by
  unfold satisfiesEqn
  congr 4
  apply List.filter_congr
  intro i _
  by_cases hi : i = m
  · subst hi; simp only [he, Bool.false_and]
  · simp [List.getD_eq_getElem?_getD, Ne.symm hi]

theorem sat_back_self (p : Eqn) (x : List Bool) (m : ℕ) (hm : m < x.length)
    (hp : p.1.getD m false = true) :
    satisfiesEqn (x.set m (xor p.2 (((List.range p.1.length).filter
        (fun l => l != m && p.1.getD l false && x.getD l false)).length % 2 == 1))) p = true := by
  have hmp : m < p.1.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (not_lt.1 hc)] at hp
    exact Bool.false_ne_true hp
  rw [sat_iff _ p p.1.length le_rfl]
  set T := ∑ i ∈ Finset.range p.1.length, b2z (i != m) * b2z (p.1.getD i false) * b2z (x.getD i false)
  set v := xor p.2 (((List.range p.1.length).filter
        (fun l => l != m && p.1.getD l false && x.getD l false)).length % 2 == 1)
  have hterm : ∀ i, b2z (p.1.getD i false) * b2z ((x.set m v).getD i false)
      = (if m = i then b2z (p.1.getD i false) * b2z v else 0)
        + b2z (i != m) * b2z (p.1.getD i false) * b2z (x.getD i false) := by
    intro i
    by_cases hi : i = m
    · subst hi; simp [List.getD_eq_getElem?_getD, hm, b2z_false]
    · have h1 : (i != m) = true := by simp [hi]
      have h2 : (x.set m v).getD i false = x.getD i false := by
        simp [List.getD_eq_getElem?_getD, Ne.symm hi]
      rw [h1, h2, b2z_true, one_mul, if_neg (Ne.symm hi), zero_add]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_range, hmp, if_true]
  rw [hp, b2z_true, one_mul]
  have hv : b2z v = b2z p.2 + T := by
    show b2z (xor p.2 _) = _
    rw [b2z_xor, b2z_mod, cast_filter_length]
    simp only [b2z_and]
    rfl
  rw [hv]
  have e : ∀ c t : ZMod 2, c + t + t = c := by decide
  exact e _ _


/-- Pivot property for column `j`. -/
def PivOK (piv : List Eqn) (j : ℕ) : Prop :=
  (∀ i < j, (piv.getD j ([], false)).1.getD i false = false) ∧
    (piv.getD j ([], false) = ([], false) ∨ (piv.getD j ([], false)).1.getD j false = true)

/-- Invariant of the forward pass after `j` columns. -/
def FInv (n : ℕ) (eqs : List Eqn) (j : ℕ) (st : List Eqn × List Eqn) : Prop :=
  st.2.length = j ∧ (∀ e ∈ st.1, e.1.length ≤ n) ∧ (∀ e ∈ st.2, e.1.length ≤ n) ∧
    (∀ x, (∀ e ∈ eqs, satisfiesEqn x e = true) ↔
      ((∀ e ∈ st.1, satisfiesEqn x e = true) ∧ (∀ e ∈ st.2, satisfiesEqn x e = true))) ∧
    (∀ e ∈ st.1, ∀ i < j, e.1.getD i false = false) ∧
    (∀ j' < j, PivOK st.2 j')

theorem FInv_init (n : ℕ) (eqs : List Eqn) (hlen : ∀ e ∈ eqs, e.1.length ≤ n) :
    FInv n eqs 0 (eqs, []) := by
  refine ⟨rfl, hlen, by simp, ?_, by simp, by simp⟩
  intro x; simp

theorem FInv_step (n : ℕ) (eqs : List Eqn) (j : ℕ) (st : List Eqn × List Eqn)
    (hI : FInv n eqs j st) : FInv n eqs (j + 1) (f2Forward st j) := by
  obtain ⟨rest, piv⟩ := st
  obtain ⟨hpl, hl1, hl2, hsat, hz, hpiv⟩ := hI
  simp only at hpl hl1 hl2 hsat hz hpiv
  unfold f2Forward
  simp only
  split_ifs with h
  · set k := rest.findIdx (fun e => e.1.getD j false) with hk
    have hget : rest.getD k ([], false) = rest[k] := List.getD_eq_getElem _ _ h
    set q := rest.getD k ([], false) with hq
    have hqmem : q ∈ rest := by rw [hget]; exact List.getElem_mem h
    have hqj : q.1.getD j false = true := by
      rw [hget]; exact List.findIdx_getElem (w := h)
    set g : Eqn → Eqn := fun e => if e.1.getD j false then addEqn e q else e with hg
    have hmem : ∀ e', e' ∈ (rest.eraseIdx k).map g ↔ ∃ e ∈ rest.eraseIdx k, g e = e' := by
      intro e'; simp
    refine ⟨by simp [hpl], ?_, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := (hmem e').1 he'
      have := hl1 e (List.mem_of_mem_eraseIdx he)
      simp only [g]
      split_ifs
      · simp [addEqn, this, hl1 q hqmem]
      · exact this
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact hl2 e he
      · simp at he; rw [he]; exact hl1 q hqmem
    · intro x
      rw [hsat x]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · intro e' he'
          obtain ⟨e, he, rfl⟩ := (hmem e').1 he'
          have := h1 e (List.mem_of_mem_eraseIdx he)
          simp only [g]
          split_ifs
          · exact (sat_addEqn x e q).2 (iff_of_true this (h1 q hqmem))
          · exact this
        · intro e he
          rcases List.mem_append.1 he with he | he
          · exact h2 e he
          · simp at he; rw [he]; exact h1 q hqmem
      · rintro ⟨h1, h2⟩
        have hqs : satisfiesEqn x q = true := h2 q (by simp)
        refine ⟨?_, fun e he => h2 e (List.mem_append_left _ he)⟩
        intro e he
        have hp := (List.getElem_cons_eraseIdx_perm h).mem_iff.2 he
        rcases List.mem_cons.1 hp with he1 | he1
        · rw [he1, ← hget]; exact hqs
        · have := h1 (g e) (List.mem_map_of_mem he1)
          simp only [g] at this
          split_ifs at this
          · exact ((sat_addEqn x e q).1 this).2 hqs
          · exact this
    · intro e' he' i hi
      obtain ⟨e, he, rfl⟩ := (hmem e').1 he'
      have hemem := List.mem_of_mem_eraseIdx he
      simp only [g]
      split_ifs with hej
      · rw [getD_addEqn]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [hz e hemem i hi, hz q hqmem i hi]; rfl
        · subst hi; rw [hej, hqj]; rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact hz e hemem i hi
        · subst hi; simpa using hej
    · intro j' hj'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | hj'
      · have := hpiv j' hj'
        unfold PivOK at this ⊢
        rw [List.getD_append _ _ _ _ (by omega)]
        exact this
      · subst hj'
        unfold PivOK
        rw [List.getD_append_right _ _ _ _ (by omega), hpl, Nat.sub_self]
        simp only [List.getD_cons_zero]
        exact ⟨fun i hi => hz q hqmem i hi, Or.inr hqj⟩
  · have hnot : ∀ e ∈ rest, e.1.getD j false = false := by
      intro e he
      by_contra hc
      exact h (List.findIdx_lt_length.2 ⟨e, he, by simpa using hc⟩)
    refine ⟨by simp [hpl], hl1, ?_, ?_, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact hl2 e he
      · simp at he; rw [he]; simp
    · intro x
      rw [hsat x]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact h2 e he
        · simp at he; rw [he]; exact sat_nil x
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun e he => h2 e (List.mem_append_left _ he)⟩
    · intro e he i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact hz e he i hi
      · subst hi; exact hnot e he
    · intro j' hj'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | hj'
      · have := hpiv j' hj'
        unfold PivOK at this ⊢
        rw [List.getD_append _ _ _ _ (by omega)]
        exact this
      · subst hj'
        unfold PivOK
        rw [List.getD_append_right _ _ _ _ (by omega), hpl, Nat.sub_self]
        simp

theorem FInv_fold (n : ℕ) (eqs : List Eqn) (hlen : ∀ e ∈ eqs, e.1.length ≤ n) (m : ℕ) :
    FInv n eqs m ((List.range m).foldl f2Forward (eqs, [])) := by
  induction m with
  | zero => exact FInv_init n eqs hlen
  | succ m ih =>
    rw [List.range_succ, List.foldl_append]
    exact FInv_step n eqs m _ ih

theorem back_fold (piv : List Eqn) (n : ℕ) (hP : ∀ j < n, PivOK piv j) :
    ∀ m, m ≤ n → ∀ x : List Bool, x.length = n →
      (∀ j, m ≤ j → j < n → satisfiesEqn x (piv.getD j ([], false)) = true) →
      ((List.range m).reverse.foldl (f2Back piv) x).length = n ∧
        ∀ j < n, satisfiesEqn ((List.range m).reverse.foldl (f2Back piv) x)
          (piv.getD j ([], false)) = true := by
  intro m
  induction m with
  | zero =>
    intro _ x hx hs
    exact ⟨hx, fun j hj => hs j (Nat.zero_le _) hj⟩
  | succ m ih =>
    intro hm x hx hs
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    apply ih (by omega)
    · simp [f2Back, hx]
    · intro j hj1 hj2
      rcases Nat.lt_or_eq_of_le hj1 with hj1 | hj1
      · unfold f2Back
        rw [sat_set_irrel _ _ _ _ ((hP j hj2).1 m hj1)]
        exact hs j (by omega) hj2
      · subst hj1
        rcases (hP m hj2).2 with h0 | h1
        · rw [h0]; exact sat_nil _
        · exact sat_back_self _ x m (by omega) h1

theorem rest_sat (n : ℕ) (e : Eqn) (hl : e.1.length ≤ n) (hz : ∀ i < n, e.1.getD i false = false)
    (x : List Bool) : satisfiesEqn x e = true ↔ e.2 = false := by
  rw [sat_iff x e e.1.length le_rfl]
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [hz i (by simp at hi; omega), b2z_false, zero_mul])]
  cases e.2 <;> decide

theorem solveF2_sound (n : ℕ) (eqs : List Eqn) (hlen : ∀ e ∈ eqs, e.1.length ≤ n)
    (h : (solveF2 n eqs).1 = true) :
    (solveF2 n eqs).2.length = n ∧ ∀ e ∈ eqs, satisfiesEqn (solveF2 n eqs).2 e = true := by
  have hI := FInv_fold n eqs hlen n
  set st := (List.range n).foldl f2Forward (eqs, []) with hst
  have h1 : (solveF2 n eqs).1 = st.1.all (fun e => !e.2) := rfl
  have h2 : (solveF2 n eqs).2 = (List.range n).reverse.foldl (f2Back st.2)
      (List.replicate n false) := rfl
  obtain ⟨hpl, hl1, hl2, hsat, hz, hpiv⟩ := hI
  rw [h1, List.all_eq_true] at h
  obtain ⟨hlenres, hres⟩ := back_fold st.2 n hpiv n le_rfl (List.replicate n false) (by simp)
    (fun j hj1 hj2 => absurd hj2 (by omega))
  rw [h2]
  refine ⟨hlenres, ?_⟩
  apply (hsat _).2
  constructor
  · intro e he
    rw [rest_sat n e (hl1 e he) (hz e he)]
    simpa using h e he
  · intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
    rw [← List.getD_eq_getElem _ ([], false) hj]
    exact hres j (by omega)

theorem solveF2_complete (n : ℕ) (eqs : List Eqn) (hlen : ∀ e ∈ eqs, e.1.length ≤ n)
    (h : (solveF2 n eqs).1 = false) (x : List Bool) : ∃ e ∈ eqs, satisfiesEqn x e = false := by
  have hI := FInv_fold n eqs hlen n
  set st := (List.range n).foldl f2Forward (eqs, []) with hst
  have h1 : (solveF2 n eqs).1 = st.1.all (fun e => !e.2) := rfl
  obtain ⟨hpl, hl1, hl2, hsat, hz, hpiv⟩ := hI
  rw [h1, List.all_eq_false] at h
  obtain ⟨e, he, he2⟩ := h
  by_contra hc
  push Not at hc
  have hall : ∀ e ∈ eqs, satisfiesEqn x e = true := fun e he => by simpa using hc e he
  have := ((hsat x).1 hall).1 e he
  rw [rest_sat n e (hl1 e he) (hz e he)] at this
  simp [this] at he2


theorem eqn_chain_length_le (n : ℕ) (eqs : List Eqn) (hlen : ∀ e ∈ eqs, e.1.length = n)
    (hchain : ∀ i (hi : i < eqs.length), ∃ x : List Bool,
      (∀ j (hj : j < i), satisfiesEqn x (eqs[j]'(lt_trans hj hi)) = true) ∧
        satisfiesEqn x (eqs[i]'hi) = false)
    (hcons : ∃ x : List Bool, ∀ e ∈ eqs, satisfiesEqn x e = true) : eqs.length ≤ n := by
  classical
  let m := eqs.length
  let v : Fin m → (Fin n → ZMod 2) := fun i j => b2z ((eqs[i.1]'i.2).1.getD j false)
  let r : Fin m → ZMod 2 := fun i => b2z (eqs[i.1]'i.2).2
  let X : List Bool → Fin n → ZMod 2 := fun x j => b2z (x.getD j false)
  have hsat : ∀ (x : List Bool) (i : Fin m),
      satisfiesEqn x (eqs[i.1]'i.2) = true ↔ ∑ j, v i j * X x j = r i := by
    intro x i
    rw [sat_iff x _ n (hlen _ (List.getElem_mem _)).le, Finset.sum_range]
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hcol : ∀ j, ∑ i, g i * v i j = 0 := by
      intro j
      have := congrFun hg j
      simpa [Finset.sum_apply] using this
    have hzero : ∀ x, ∑ i, g i * (∑ j, v i j * X x j) = 0 := by
      intro x
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro j _
      have : ∑ i, g i * (v i j * X x j) = (∑ i, g i * v i j) * X x j := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      rw [this, hcol j, zero_mul]
    obtain ⟨y, hy⟩ := hcons
    have hr : ∑ i, g i * r i = 0 := by
      rw [← hzero y]
      apply Finset.sum_congr rfl
      intro i _
      rw [(hsat y i).1 (hy _ (List.getElem_mem _))]
    by_contra hne
    push Not at hne
    obtain ⟨i1, hi1⟩ := hne
    let s := Finset.univ.filter (fun i => g i ≠ 0)
    have hs : s.Nonempty := ⟨i1, by simp [s, hi1]⟩
    let i0 := s.max' hs
    have hi0 : g i0 ≠ 0 := by
      have := s.max'_mem hs
      simpa [s] using this
    have hgt : ∀ i, i0 < i → g i = 0 := by
      intro i hi
      by_contra hc
      have : i ≤ i0 := s.le_max' i (by simp [s, hc])
      exact absurd hi (not_lt.2 this)
    obtain ⟨x, hx1, hx2⟩ := hchain i0.1 i0.2
    have hD : ∑ i, g i * ((∑ j, v i j * X x j) - r i) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, hzero x, hr, sub_zero]
    rw [Finset.sum_eq_single i0] at hD
    · rcases mul_eq_zero.1 hD with h | h
      · exact hi0 h
      · have := (hsat x i0).2 (sub_eq_zero.1 h)
        rw [this] at hx2
        exact Bool.noConfusion hx2
    · intro i _ hi
      rcases lt_or_gt_of_ne hi with hlt | hlt
      · have := (hsat x i).1 (hx1 i.1 hlt)
        rw [this, sub_self, mul_zero]
      · rw [hgt i hlt, zero_mul]
    · simp
  have := hli.fintype_card_le_finrank
  simpa [Module.finrank_fin_fun] using this

end PfaffianRecognition.CoRP

end

-- ===== from Solutions/Lib/Sign.lean =====
section

namespace PfaffianRecognition.Recognition.SignParityAux

open PfaffianRecognition.Recognition
open Classical

def inv {α : Type*} [LinearOrder α] : List α → ℕ
  | [] => 0
  | x :: l => l.countP (fun y => decide (y < x)) + inv l

theorem inv_cons {α : Type*} [LinearOrder α] (x : α) (l : List α) :
    inv (x :: l) = l.countP (fun y => decide (y < x)) + inv l := rfl

theorem inv_append {α : Type*} [LinearOrder α] (l₁ l₂ : List α) :
    inv (l₁ ++ l₂) = inv l₁ + inv l₂ +
      (l₁.map fun x => l₂.countP (fun y => decide (y < x))).sum := by
  induction l₁ with
  | nil => simp [inv]
  | cons x l ih =>
    rw [List.cons_append, inv_cons, inv_cons, ih, List.countP_append, List.map_cons,
      List.sum_cons]
    ring

theorem countP_ofFn' {α : Type*} (p : α → Bool) : ∀ (n : ℕ) (g : Fin n → α),
    (List.ofFn g).countP p = ∑ i, if p (g i) then 1 else 0
  | 0, g => by simp
  | n + 1, g => by
    rw [List.ofFn_succ, List.countP_cons, countP_ofFn' p n, Fin.sum_univ_succ]
    ring

theorem inv_ofFn {α : Type*} [LinearOrder α] : ∀ (n : ℕ) (f : Fin n → α),
    inv (List.ofFn f) = ∑ i, ∑ j, if i < j ∧ f j < f i then 1 else 0
  | 0, f => by simp [inv]
  | n + 1, f => by
    rw [List.ofFn_succ, inv_cons, inv_ofFn n, Fin.sum_univ_succ]
    congr 1
    · rw [Fin.sum_univ_succ, countP_ofFn']
      simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.sum_univ_succ]
      simp [Fin.succ_lt_succ_iff]

theorem sign_eq_inv {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign p : ℤˣ) : ℤ) = (-1) ^ inv (List.ofFn p) := by
  rw [inv_ofFn, Equiv.Perm.sign_eq_prod_prod_Ioi, ← Finset.prod_pow_eq_pow_sum]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  have hI : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext; simp
  rw [hI, Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hij : i < j
  · have hne : p i ≠ p j := fun h => hij.ne (p.injective h)
    rcases lt_or_gt_of_ne hne with h | h
    · simp [hij, h, h.not_gt]
    · simp [hij, h, h.not_gt]
  · simp [hij]


variable {N : ℕ} {G : SimpleGraph (Fin N)}

theorem val_eq (e : G.edgeSet) : e.val = s(edgeLo e, edgeHi e) := by
  unfold edgeLo edgeHi
  have h := Quot.out_eq e.val
  rcases le_total e.val.out.1 e.val.out.2 with h1 | h1
  · rw [min_eq_left h1, max_eq_right h1]
    exact h.symm
  · rw [min_eq_right h1, max_eq_left h1, Sym2.eq_swap]
    exact h.symm

theorem adj (e : G.edgeSet) : G.Adj (edgeLo e) (edgeHi e) := by
  have := e.prop
  rw [val_eq e, SimpleGraph.mem_edgeSet] at this
  exact this

theorem lo_lt_hi (e : G.edgeSet) : edgeLo e < edgeHi e := by
  have h1 : edgeLo e ≤ edgeHi e := by unfold edgeLo edgeHi; exact min_le_max
  exact lt_of_le_of_ne h1 (adj e).ne

theorem mem_iff (e : G.edgeSet) (v : Fin N) : v ∈ e.val ↔ v = edgeLo e ∨ v = edgeHi e := by
  rw [val_eq e, Sym2.mem_iff]

/-- The block of the one-line sequence contributed by one edge. -/
noncomputable def blk (D : Orientation G) (e : G.edgeSet) : List (Fin N) :=
  if D.val (edgeLo e) (edgeHi e) then [edgeLo e, edgeHi e] else [edgeHi e, edgeLo e]

theorem seq_eq (D : Orientation G) (M : Finset G.edgeSet) :
    matchingSequence D M = (matchingEdgeOrder M).flatMap (blk D) := rfl

theorem mem_blk (D : Orientation G) (e : G.edgeSet) (v : Fin N) :
    v ∈ blk D e ↔ v ∈ e.val := by
  rw [mem_iff]; unfold blk; split_ifs <;> simp [or_comm]

theorem countP_blk (D : Orientation G) (e : G.edgeSet) (P : Fin N → Bool) :
    (blk D e).countP P = (if P (edgeLo e) then 1 else 0) + (if P (edgeHi e) then 1 else 0) := by
  unfold blk
  by_cases hD : D.val (edgeLo e) (edgeHi e) <;>
    simp only [hD, if_true, if_false, List.countP_cons, List.countP_nil] <;>
    cases P (edgeLo e) <;> cases P (edgeHi e) <;> simp

theorem inv_blk (D : Orientation G) (e : G.edgeSet) :
    inv (blk D e) = if D.val (edgeHi e) (edgeLo e) then 1 else 0 := by
  have hlt := lo_lt_hi e
  have hor := D.prop.2 _ _ (adj e)
  unfold blk
  by_cases h : D.val (edgeLo e) (edgeHi e)
  · have : ¬ D.val (edgeHi e) (edgeLo e) := fun h' => hor.2 ⟨h, h'⟩
    simp [h, this, inv, hlt.not_gt]
  · have : D.val (edgeHi e) (edgeLo e) := hor.1.resolve_left h
    simp [h, this, inv, hlt]

theorem sum_blk (D : Orientation G) (e : G.edgeSet) (l : List (Fin N)) :
    ((blk D e).map fun x => l.countP (fun y => decide (y < x))).sum =
      l.countP (fun y => decide (y < edgeLo e)) + l.countP (fun y => decide (y < edgeHi e)) := by
  unfold blk; split_ifs <;> simp [add_comm]

theorem sum_cast_eq_countP {α : Type*} (l : List α) (h : α → ℕ) (Q : α → Prop)
    [DecidablePred Q] (hh : ∀ a ∈ l, (h a : ZMod 2) = if Q a then 1 else 0) :
    ((l.map h).sum : ZMod 2) = (l.countP (fun a => decide (Q a)) : ZMod 2) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, Nat.cast_add]
    rw [ih (fun b hb => hh b (List.mem_cons_of_mem _ hb)), hh a List.mem_cons_self]
    split_ifs <;> simp_all [add_comm]

/-- Edge `e` precedes `f`, and they are vertex-disjoint. -/
def Prec (e f : G.edgeSet) : Prop := edgeLo e < edgeLo f ∧ ∀ v, v ∈ e.val → v ∉ f.val

theorem parity_cross (g f : G.edgeSet) (h : Prec g f) :
    (((if edgeLo f < edgeHi g then 1 else 0) + (if edgeHi f < edgeHi g then 1 else 0) : ℕ) :
      ZMod 2) = if edgeLo g < edgeLo f ∧ Crosses g f then 1 else 0 := by
  have h1 := lo_lt_hi g
  have h2 := lo_lt_hi f
  have hne : edgeHi f ≠ edgeHi g := by
    intro heq
    exact h.2 (edgeHi g) ((mem_iff g _).2 (Or.inr rfl)) ((mem_iff f _).2 (Or.inr heq.symm))
  have hlo := h.1
  by_cases ha : edgeLo f < edgeHi g <;> by_cases hb : edgeHi f < edgeHi g
  · have : ¬ (edgeLo g < edgeLo f ∧ Crosses g f) := by
      rintro ⟨_, (⟨_, _, h3⟩ | ⟨h3, _, _⟩)⟩
      · exact absurd hb (not_lt.2 h3.le)
      · exact absurd hlo (not_lt.2 h3.le)
    rw [if_neg this, if_pos ha, if_pos hb]; decide
  · have h4 : edgeHi g < edgeHi f := lt_of_le_of_ne (not_lt.1 hb) (Ne.symm hne)
    have : edgeLo g < edgeLo f ∧ Crosses g f := ⟨hlo, Or.inl ⟨hlo, ha, h4⟩⟩
    rw [if_pos this, if_pos ha, if_neg hb]; simp
  · exact absurd (lt_trans h2 hb) ha
  · have : ¬ (edgeLo g < edgeLo f ∧ Crosses g f) := by
      rintro ⟨_, (⟨_, h3, _⟩ | ⟨h3, _, _⟩)⟩
      · exact ha h3
      · exact absurd hlo (not_lt.2 h3.le)
    rw [if_neg this, if_neg ha, if_neg hb]; simp

theorem main_ind (D : Orientation G) : ∀ (L : List G.edgeSet), L.Pairwise Prec →
    (inv (L.flatMap (blk D)) : ZMod 2) =
      ((∑ e ∈ L.toFinset,
          (L.toFinset.filter fun f => edgeLo e < edgeLo f ∧ Crosses e f).card : ℕ) : ZMod 2) +
      ((L.toFinset.filter fun e => D.val (edgeHi e) (edgeLo e)).card : ZMod 2)
  | [], _ => by simp [inv]
  | g :: L, hP => by
    rw [List.pairwise_cons] at hP
    obtain ⟨hg, hP⟩ := hP
    have ih := main_ind D L hP
    have hgL : g ∉ L := fun h => lt_irrefl _ (hg g h).1
    have hnd : L.Nodup := hP.imp fun h => fun heq => lt_irrefl _ (heq ▸ h.1)
    rw [List.flatMap_cons, inv_append, inv_blk, sum_blk]
    have h0 : (L.flatMap (blk D)).countP (fun y => decide (y < edgeLo g)) = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      obtain ⟨f, hf, ha⟩ := List.mem_flatMap.1 ha
      rw [mem_blk, mem_iff] at ha
      have := (hg f hf).1
      have := lo_lt_hi f
      simp only [decide_eq_true_eq, not_lt]
      rcases ha with rfl | rfl <;> order
    have h1 : ((L.flatMap (blk D)).countP (fun y => decide (y < edgeHi g)) : ZMod 2) =
        ((L.toFinset.filter fun f => edgeLo g < edgeLo f ∧ Crosses g f).card : ZMod 2) := by
      rw [List.countP_flatMap, sum_cast_eq_countP _ _ (fun f => edgeLo g < edgeLo f ∧ Crosses g f)]
      · rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _),
          List.toFinset_filter]
        simp
      · intro f hf
        rw [Function.comp_apply, countP_blk, ← parity_cross g f (hg f hf)]
        simp
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using hgL), Finset.filter_insert,
      if_neg (show ¬(edgeLo g < edgeLo g ∧ Crosses g g) from fun h => lt_irrefl _ h.1)]
    have h2 : ∑ e ∈ L.toFinset, ((insert g L.toFinset).filter
        fun f => edgeLo e < edgeLo f ∧ Crosses e f).card =
        ∑ e ∈ L.toFinset, (L.toFinset.filter fun f => edgeLo e < edgeLo f ∧ Crosses e f).card := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.filter_insert, if_neg]
      have := (hg e (by simpa using he)).1
      intro h; exact absurd h.1 (not_lt.2 this.le)
    rw [h2]
    push_cast
    rw [h0, h1, ih]
    rw [Finset.filter_insert]
    by_cases hb : D.val (edgeHi g) (edgeLo g)
    · rw [if_pos hb, if_pos hb, Finset.card_insert_of_notMem (by simp [hgL])]
      push_cast; ring
    · rw [if_neg hb, if_neg hb]
      push_cast; ring

theorem exists_perm_ofFn {N : ℕ} (l : List (Fin N)) (hnd : l.Nodup) (hall : ∀ v, v ∈ l) :
    ∃ p : Equiv.Perm (Fin N), List.ofFn p = l := by
  have hlen : l.length = N := by
    apply le_antisymm
    · simpa using hnd.length_le_card
    · have : (Finset.univ : Finset (Fin N)) ⊆ l.toFinset := fun v _ => by simpa using hall v
      simpa using (Finset.card_le_card this).trans (List.toFinset_card_le l)
  refine ⟨(finCongr hlen.symm).trans (hnd.getEquivOfForallMemList l hall), ?_⟩
  apply List.ext_get (by simp [hlen])
  intro n h1 h2
  simp [List.Nodup.getEquivOfForallMemList]

theorem order_perm (M : Finset G.edgeSet) : (matchingEdgeOrder M).Perm M.toList := by
  unfold matchingEdgeOrder; exact List.mergeSort_perm _ _

theorem order_sorted (M : Finset G.edgeSet) :
    (matchingEdgeOrder M).Pairwise (fun e f => edgeLo e ≤ edgeLo f) := by
  unfold matchingEdgeOrder
  have := List.pairwise_mergeSort (le := fun e f : G.edgeSet => decide (edgeLo e ≤ edgeLo f))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; exact le_trans h1 h2)
    (fun a b => by simpa using le_total _ _) M.toList
  simpa using this

end PfaffianRecognition.Recognition.SignParityAux

namespace PfaffianRecognition.Recognition

open PfaffianRecognition.Recognition.SignParityAux

/-- Lemma 2.1 (mission milestone, exact statement). -/
theorem matching_sign_parity {N : ℕ} (G : SimpleGraph (Fin N)) (D : Orientation G)
    (M : Finset G.edgeSet) (hM : MulmuleyVV.Matching.IsPerfectMatchingEdges G M) :
    matchingSign D M = (-1 : ℤ) ^ (crossingParity M + backwardParity D M) := by
  classical
  have hcommon : ∀ e f : G.edgeSet, e ∈ M → f ∈ M → ∀ v, v ∈ e.val → v ∈ f.val → e = f :=
    fun e f he hf v hv hv' => (hM v).unique ⟨he, hv⟩ ⟨hf, hv'⟩
  set L := matchingEdgeOrder M with hLdef
  have hnd : L.Nodup := (order_perm M).nodup_iff.mpr M.nodup_toList
  have hmem : ∀ e, e ∈ L ↔ e ∈ M := fun e => (order_perm M).mem_iff.trans (Finset.mem_toList)
  have hP : L.Pairwise Prec := by
    have h2 : L.Pairwise (fun e f => edgeLo e ≤ edgeLo f ∧ e ≠ f) := (order_sorted M).and hnd
    refine h2.imp_of_mem fun {e f} he hf h => ?_
    have he' := (hmem e).1 he
    have hf' := (hmem f).1 hf
    refine ⟨lt_of_le_of_ne h.1 fun heq => h.2 ?_, fun v hv hv' => h.2 ?_⟩
    · exact hcommon e f he' hf' (edgeLo e) ((mem_iff e _).2 (Or.inl rfl))
        ((mem_iff f _).2 (Or.inl heq))
    · exact hcommon e f he' hf' v hv hv'
  have hseq_nd : (matchingSequence D M).Nodup := by
    rw [seq_eq, List.nodup_flatMap]
    refine ⟨fun e _ => ?_, hP.imp fun {e f} h => ?_⟩
    · have := lo_lt_hi e
      unfold blk; split_ifs <;> simp [this.ne, this.ne']
    · intro a ha hb
      rw [mem_blk] at ha hb
      exact h.2 a ha hb
  have hseq_all : ∀ v, v ∈ matchingSequence D M := by
    intro v
    obtain ⟨e, ⟨he, hv⟩, _⟩ := hM v
    rw [seq_eq, List.mem_flatMap]
    exact ⟨e, (hmem e).2 he, (mem_blk D e v).2 hv⟩
  have hex := exists_perm_ofFn _ hseq_nd hseq_all
  have hσ : List.ofFn (matchingPermutation D M) = matchingSequence D M := by
    unfold matchingPermutation
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  unfold matchingSign
  rw [sign_eq_inv, hσ, seq_eq, neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (n := crossingParity M + backwardParity D M)]
  congr 1
  have key := main_ind D L hP
  have hLM : L.toFinset = M := by ext e; simp [hmem]
  rw [hLM] at key
  have hA : ((crossingPairs G).filter fun ef => ef.1 ∈ M ∧ ef.2 ∈ M).card =
      ∑ e ∈ M, (M.filter fun f => edgeLo e < edgeLo f ∧ Crosses e f).card := by
    have : ((crossingPairs G).filter fun ef => ef.1 ∈ M ∧ ef.2 ∈ M) =
        (M ×ˢ M).filter fun ef => edgeLo ef.1 < edgeLo ef.2 ∧ Crosses ef.1 ef.2 := by
      ext ef; simp [crossingPairs]; tauto
    rw [this, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.card_filter]
  have hB : (M ∩ backwardEdges D).card =
      (M.filter fun e => D.val (edgeHi e) (edgeLo e)).card := by
    congr 1; ext e; simp [backwardEdges]
  unfold crossingParity backwardParity
  rw [← Nat.add_mod]
  apply (ZMod.natCast_eq_natCast_iff' _ _ 2).1
  push_cast
  rw [key, hA, hB]

end PfaffianRecognition.Recognition

end

-- ===== from Solutions/Main/Complete.lean =====
section

namespace PfaffianRecognition.CoRP
open PfaffianRecognition.Recognition

variable {N : ℕ} {G : SimpleGraph (Fin N)}

theorem neg_one_pow_eq_iff_mod (a b : ℕ) : (-1 : ℤ) ^ a = (-1) ^ b ↔ a % 2 = b % 2 := by
  rcases Nat.even_or_odd a with ha | ha <;> rcases Nat.even_or_odd b with hb | hb <;>
    simp [ha.neg_one_pow, hb.neg_one_pow, Nat.even_iff.1, Nat.odd_iff.1, ha, hb] <;>
    first
    | (rw [Nat.even_iff.1 ha, Nat.odd_iff.1 hb]; decide)
    | (rw [Nat.odd_iff.1 ha, Nat.even_iff.1 hb]; decide)
    | skip

theorem parity_of_pfaffian (D : Orientation G) (hD : IsPfaffianOrientation D) (M₁ M₂ : Finset G.edgeSet)
    (h₁ : MulmuleyVV.Matching.IsPerfectMatchingEdges G M₁)
    (h₂ : MulmuleyVV.Matching.IsPerfectMatchingEdges G M₂) :
    (crossingParity M₁ + backwardParity D M₁) % 2 = (crossingParity M₂ + backwardParity D M₂) % 2 := by
  have := hD M₁ M₂ h₁ h₂
  rw [matching_sign_parity G D M₁ h₁, matching_sign_parity G D M₂ h₂] at this
  exact (neg_one_pow_eq_iff_mod _ _).1 this


theorem crossCount_mod (S : List (ℕ × ℕ))
    (h : isPMList N (encEdges (CatalyticMatching.General.graphBits G)) S = true) :
    crossCount S % 2 = crossingParity (pmSet (G := G) S) := by
  classical
  obtain ⟨-, hnd, himg⟩ := isPMList_spec S h
  rw [crossCount_eq S hnd himg]
  unfold crossingParity
  congr 2

theorem dCount_mod (D : Orientation G) (S : List (ℕ × ℕ)) :
    dCount (encEdges (CatalyticMatching.General.graphBits G))
        ((encEdges (CatalyticMatching.General.graphBits G)).map (bkOf D)) S % 2 =
      backwardParity D (pmSet (G := G) S) := by
  classical
  rw [dCount_bkOf]
  unfold backwardParity
  rfl

/-- The reference sign bit of a Pfaffian orientation. -/
noncomputable def refBit (D : Orientation G) : Bool := by
  classical
  exact if h : ∃ M : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G M then
    decide ((crossingParity (Classical.choose h) + backwardParity D (Classical.choose h)) % 2 = 1)
  else false

theorem not_violates_of_pfaffian (D : Orientation G) (hD : IsPfaffianOrientation D) (S : List (ℕ × ℕ))
    (h : isPMList N (encEdges (CatalyticMatching.General.graphBits G)) S = true) :
    violates (encEdges (CatalyticMatching.General.graphBits G))
      ((encEdges (CatalyticMatching.General.graphBits G)).map (bkOf D)) (refBit D) S = false := by
  classical
  obtain ⟨hpm, -, -⟩ := isPMList_spec S h
  have hex : ∃ M : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G M := ⟨_, hpm⟩
  have hpar := parity_of_pfaffian D hD _ _ (Classical.choose_spec hex) hpm
  have hc := crossCount_mod S h
  have hb := dCount_mod D S
  unfold violates refBit
  rw [dif_pos hex]
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro hcon
  rcases Nat.mod_two_eq_zero_or_one ((crossingParity (Classical.choose hex) +
    backwardParity D (Classical.choose hex))) with hq | hq <;> simp [hq] at hcon <;> omega


/-- Invariant of the rounds on a Pfaffian graph: only genuine matching equations, never rejected. -/
def CInv (N : ℕ) (E : List (ℕ × ℕ)) (st : List Eqn × (Bool × Bool)) : Prop :=
  (∀ e ∈ st.1, ∃ S, isPMList N E S = true ∧ e = matchEqn E S) ∧ (st.2.1 = true → st.2.2 = true)

theorem roundStep_CInv (D : Orientation G) (hD : IsPfaffianOrientation D) (m : ℕ) (ρ : List Bool)
    (st : List Eqn × (Bool × Bool)) (r : ℕ)
    (h : CInv N (encEdges (CatalyticMatching.General.graphBits G)) st) :
    CInv N (encEdges (CatalyticMatching.General.graphBits G))
      (roundStep m N (encEdges (CatalyticMatching.General.graphBits G)) ρ st r) := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  obtain ⟨hgen, hdone⟩ := h
  unfold roundStep
  split_ifs with h1 h2 h3 h4
  · exact ⟨hgen, hdone⟩
  · exfalso
    have hlen : ∀ e ∈ st.1, e.1.length ≤ E.length + 1 := by
      intro e he
      obtain ⟨S, -, rfl⟩ := hgen e he
      rw [matchEqn_length]
    have hfalse : (solveF2 (E.length + 1) st.1).1 = false := by simpa using h2
    obtain ⟨e, he, hsat⟩ := solveF2_complete (E.length + 1) st.1 hlen hfalse
      (E.map (bkOf D) ++ [refBit D])
    obtain ⟨S, hS, rfl⟩ := hgen e he
    rw [satisfies_matchEqn E S _ _ (by simp), not_violates_of_pfaffian D hD S hS] at hsat
    simp at hsat
  · exact ⟨hgen, fun _ => rfl⟩
  · refine ⟨?_, fun h => by simp at h⟩
    intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact hgen e he
    · simp only [List.mem_singleton] at he
      rw [Bool.and_eq_true] at h4
      exact ⟨_, h4.1, he⟩
  · exact ⟨hgen, fun _ => rfl⟩

theorem runRounds_true_of_pfaffian (D : Orientation G) (hD : IsPfaffianOrientation D) (m : ℕ)
    (ρ : List Bool) :
    runRounds m N (encEdges (CatalyticMatching.General.graphBits G)) ρ = true := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  have key : ∀ (l : List ℕ) (st : List Eqn × (Bool × Bool)), CInv N E st →
      CInv N E (l.foldl (roundStep m N E ρ) st) := by
    intro l
    induction l with
    | nil => intro st h; exact h
    | cons a l ih => intro st h; exact ih _ (roundStep_CInv D hD m ρ st a h)
  have hfin := key (List.range (E.length + 3)) ([], (false, false)) ⟨by simp, by simp⟩
  unfold runRounds
  rcases hfin with ⟨-, hd⟩
  cases hx : ((List.range (E.length + 3)).foldl (roundStep m N E ρ) ([], (false, false))).2.1
  · simp
  · simp [hd hx]

theorem pfAlg_complete_core (ρ w : List Bool) (h : PfaffianRecognition.Recognition.pfaffianLanguage w) :
    pfAlg (ρ, w) = true := by
  obtain ⟨N, G, rfl, D, hD⟩ := h
  unfold pfAlg
  simp only
  rw [validEnc_graphBits, Bool.true_and]
  have := runRounds_true_of_pfaffian (G := G) D hD (fieldM (hdrN (CatalyticMatching.General.graphBits G))) ρ
  convert this using 2
  exact hdrN_graphBits G

end PfaffianRecognition.CoRP

end

theorem solution (ρ w : List Bool) (h : PfaffianRecognition.Recognition.pfaffianLanguage w) :
    PfaffianRecognition.CoRP.pfAlg (ρ, w) = true :=
  PfaffianRecognition.CoRP.pfAlg_complete_core ρ w h
