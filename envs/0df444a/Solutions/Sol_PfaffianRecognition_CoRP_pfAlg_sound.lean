-- Prove2me | solution 1 for PfaffianRecognition.CoRP.pfAlg_sound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:02:49.069889+00:00
-- url     : https://prove2.me/submissions/097f439a-ae56-49dc-9200-e80785c33cd8

import Definitions.Def_PfaffianRecognition_CoRP_Algorithm
import Definitions.Def_PfaffianRecognition_Recognition_computation_model
import Definitions.Def_PfaffianRecognition_CoRP_GF2Bits
import Definitions.Def_PfaffianRecognition_CoRP_ListLinAlg
import Definitions.Def_PfaffianRecognition_Recognition_polynomial_model
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

-- ===== from Solutions/Lib/GF.lean =====
section

namespace PfaffianRecognition.CoRP
open Polynomial

lemma two_pow_three_pow (k : ℕ) :
    ∃ u : ℤ, (2 : ℤ) ^ (3 ^ k) + 1 = 3 ^ (k + 1) * u ∧ ¬ (3 : ℤ) ∣ u := by
  induction k with
  | zero => exact ⟨1, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨u, hu, h3⟩ := ih
    set w : ℤ := 3 ^ k * u with hw
    refine ⟨u * (3 * w ^ 2 - 3 * w + 1), ?_, ?_⟩
    · have ht : (2 : ℤ) ^ (3 ^ k) = 3 * w - 1 := by rw [hw]; linear_combination hu
      rw [pow_succ 3 k, pow_mul, ht]
      rw [hw]; ring
    · intro hd
      rcases (Int.prime_three.dvd_mul).1 hd with h | h
      · exact h3 h
      · have : (3 : ℤ) ∣ 1 := by
          have : (1 : ℤ) = (3 * w ^ 2 - 3 * w + 1) - 3 * (w ^ 2 - w) := by ring
          rw [this]; exact dvd_sub h (dvd_mul_right _ _)
        norm_num at this

lemma orderOf_two_zmod (k : ℕ) :
    orderOf (2 : ZMod (3 ^ (k + 1))) = 2 * 3 ^ k := by
  obtain ⟨u, hu, h3⟩ := two_pow_three_pow k
  have hneg : (2 : ZMod (3 ^ (k + 1))) ^ (3 ^ k) = -1 := by
    have := congrArg (fun z : ℤ => (z : ZMod (3 ^ (k + 1)))) hu
    simp only [Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_one, Int.cast_mul] at this
    have h0 : ((3 : ZMod (3 ^ (k + 1)))) ^ (k + 1) = 0 := by
      exact_mod_cast ZMod.natCast_self (3 ^ (k + 1))
    rw [h0, zero_mul] at this
    linear_combination this
  have hne1 : (2 : ZMod (3 ^ (k + 1))) ^ (3 ^ k) ≠ 1 := by
    rw [hneg]
    intro h
    have h2 : ((2 : ℕ) : ZMod (3 ^ (k + 1))) = 0 := by
      push_cast; linear_combination -h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have : 3 ≤ 3 ^ (k + 1) := Nat.le_self_pow (by omega) 3
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity)
  · rw [mul_comm, pow_mul, hneg]; norm_num
  · intro p hp hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
    · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
      subst this
      simpa using hne1
    · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
      subst this
      cases k with
      | zero => norm_num at h
      | succ j =>
        obtain ⟨v, hv, hv3⟩ := two_pow_three_pow j
        have he : 2 * 3 ^ (j + 1) / 3 = 2 * 3 ^ j := by
          rw [pow_succ]; omega
        rw [he]
        intro h1
        have h1' : (((2 : ℤ) ^ (2 * 3 ^ j) - 1 : ℤ) : ZMod (3 ^ (j + 1 + 1))) = 0 := by
          push_cast; rw [h1]; ring
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1'
        push_cast at h1'
        have hsq : (2 : ℤ) ^ (2 * 3 ^ j) - 1 = 3 ^ (j + 1) * (3 ^ (j + 1) * v ^ 2 - 2 * v) := by
          have ht : (2 : ℤ) ^ (3 ^ j) = 3 ^ (j + 1) * v - 1 := by linear_combination hv
          rw [pow_mul', ht]; ring
        rw [hsq, pow_succ (3 : ℤ) (j + 1)] at h1'
        have h2 := (mul_dvd_mul_iff_left (by positivity : (3 : ℤ) ^ (j + 1) ≠ 0)).1 h1'
        have h3' : (3 : ℤ) ∣ 2 * v := by
          have : 2 * v = 3 ^ (j + 1) * v ^ 2 - (3 ^ (j + 1) * v ^ 2 - 2 * v) := by ring
          rw [this]
          exact dvd_sub (dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _) h2
        rcases (Int.prime_three.dvd_mul).1 h3' with h | h
        · norm_num at h
        · exact hv3 h

lemma gfPoly_eq_cyclotomic (k : ℕ) : gfPoly (3 ^ k) = cyclotomic (3 ^ (k + 1)) (ZMod 2) := by
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_three]
  simp [gfPoly, Finset.sum_range_succ, ← pow_mul]
  ring

theorem gfPoly_irreducible (k : ℕ) : Irreducible (gfPoly (3 ^ k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Fintype.card (ZMod 2) = 2 ^ 1 := by simp
  have hn : Nat.Coprime 2 (3 ^ (k + 1)) := by
    apply Nat.Coprime.pow_right; norm_num
  rw [gfPoly_eq_cyclotomic]
  apply irreducible_of_dvd_cyclotomic_of_natDegree hK hn dvd_rfl
  rw [← orderOf_units, ZMod.coe_unitOfCoprime, natDegree_cyclotomic, Nat.totient_prime_pow_succ Nat.prime_three]
  push_cast
  rw [orderOf_two_zmod]
  ring


local notation "rt" m => AdjoinRoot.root (gfPoly m)

lemma gf_two_eq_zero (m : ℕ) : (2 : GF m) = 0 := by
  rw [← map_ofNat (AdjoinRoot.of (gfPoly m)) 2]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, map_zero]

lemma gf_add_self (m : ℕ) (x : GF m) : x + x = 0 := by
  rw [← two_mul, gf_two_eq_zero, zero_mul]

lemma gf_neg_eq (m : ℕ) (x : GF m) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, gf_add_self]

lemma gf_root_eq (m : ℕ) : (rt m) ^ (2 * m) + (rt m) ^ m + 1 = 0 := by
  have h : AdjoinRoot.mk (gfPoly m) (X ^ (2 * m) + X ^ m + 1) = 0 := AdjoinRoot.mk_self
  simpa [map_add, map_pow, AdjoinRoot.mk_X] using h

lemma gf_root_pow_three (m : ℕ) : (rt m) ^ (3 * m) = 1 := by
  have h := gf_root_eq m
  have : (rt m) ^ (3 * m) - 1 = ((rt m) ^ m - 1) * ((rt m) ^ (2 * m) + (rt m) ^ m + 1) := by ring
  rw [h, mul_zero, sub_eq_zero] at this
  exact this

lemma gf_root_pow_fold (m e : ℕ) (he : 2 * m ≤ e) :
    (rt m) ^ e = (rt m) ^ (e - m) + (rt m) ^ (e - 2 * m) := by
  have h := gf_root_eq m
  have h2 : (rt m) ^ (2 * m) = (rt m) ^ m + 1 := by
    rw [← gf_neg_eq m ((rt m) ^ m + 1)]; linear_combination h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  have e1 : 2 * m + d - m = m + d := by omega
  rw [e1, Nat.add_sub_cancel_left, pow_add, h2]; ring

lemma gfPoly_zero : gfPoly 0 = 1 := by
  simp only [gfPoly, mul_zero, pow_zero, CharTwo.add_self_eq_zero, zero_add]

lemma gfPoly_monic (m : ℕ) : (gfPoly m).Monic := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [gfPoly_zero]; exact monic_one
  · unfold gfPoly
    rw [add_assoc]
    apply monic_X_pow_add
    calc degree ((X : (ZMod 2)[X]) ^ m + 1) ≤ m := by
          refine (degree_add_le _ _).trans (max_le ?_ ?_)
          · exact degree_X_pow_le m
          · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le m)
      _ < (2 * m : ℕ) := by exact_mod_cast (by omega : m < 2 * m)

lemma gfPoly_natDegree (m : ℕ) : (gfPoly m).natDegree = 2 * m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [gfPoly_zero]; simp
  · unfold gfPoly
    rw [add_assoc, natDegree_add_eq_left_of_degree_lt]
    · simp
    · rw [degree_X_pow]
      calc degree ((X : (ZMod 2)[X]) ^ m + 1) ≤ m := by
            refine (degree_add_le _ _).trans (max_le ?_ ?_)
            · exact degree_X_pow_le m
            · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le m)
        _ < (2 * m : ℕ) := by exact_mod_cast (by omega : m < 2 * m)

/-- The power basis `1, z, …, z^{2m-1}` of `GF m` over `𝔽₂`, indexed by `Fin (2m)`. -/
noncomputable def gfBasis (m : ℕ) : Module.Basis (Fin (2 * m)) (ZMod 2) (GF m) :=
  (AdjoinRoot.powerBasis' (gfPoly_monic m)).basis.reindex (finCongr (gfPoly_natDegree m))

lemma gfBasis_apply (m : ℕ) (i : Fin (2 * m)) : gfBasis m i = (rt m) ^ (i : ℕ) := by
  simp [gfBasis]; rfl

/-- Bits as `𝔽₂`-coordinates. -/
def bitVec (m : ℕ) (a : List Bool) : Fin (2 * m) → ZMod 2 :=
  fun i => if a.getD i false then 1 else 0

lemma gfDecode_eq_basis (m : ℕ) (a : List Bool) :
    gfDecode m a = (gfBasis m).equivFun.symm (bitVec m a) := by
  rw [Module.Basis.equivFun_symm_apply, gfDecode, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gfBasis_apply, bitVec]
  split_ifs <;> simp

lemma getD_map_range (n : ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma gfDecode_congr (m : ℕ) (a b : List Bool)
    (h : ∀ i < 2 * m, a.getD i false = b.getD i false) : gfDecode m a = gfDecode m b := by
  unfold gfDecode
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem gfDecode_zero (m : ℕ) : gfDecode m (gfZero m) = 0 := by
  unfold gfDecode
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [gfZero, getD_map_range _ _ _ (Finset.mem_range.1 hi)]
  simp

lemma gf_zero_subsingleton : Subsingleton (GF 0) := by
  refine subsingleton_of_zero_eq_one ?_
  have h1 : AdjoinRoot.mk (gfPoly 0) 1 = 0 := AdjoinRoot.mk_eq_zero.2 (by rw [gfPoly_zero])
  rw [map_one] at h1; exact h1.symm

theorem gfDecode_one (m : ℕ) : gfDecode m (gfOne m) = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact gf_zero_subsingleton.elim _ _
  unfold gfDecode
  rw [Finset.sum_eq_single 0]
  · rw [gfOne, getD_map_range _ _ _ (by omega)]; simp
  · intro i hi hi0
    rw [gfOne, getD_map_range _ _ _ (Finset.mem_range.1 hi)]; simp [hi0]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem gfDecode_add (m : ℕ) (a b : List Bool) :
    gfDecode m (gfAdd m a b) = gfDecode m a + gfDecode m b := by
  unfold gfDecode
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [gfAdd, getD_map_range _ _ _ (Finset.mem_range.1 hi)]
  cases a.getD i false <;> cases b.getD i false <;> simp [gf_add_self]

theorem gfDecode_neg (m : ℕ) (a : List Bool) : gfDecode m a = -gfDecode m a :=
  (gf_neg_eq m _).symm

theorem gfDecode_take (m : ℕ) (a : List Bool) :
    gfDecode m (a.take (2 * m)) = gfDecode m a := by
  apply gfDecode_congr
  intro i hi
  simp [List.getD_eq_getElem?_getD, hi]

theorem gfIsZero_iff (m : ℕ) (a : List Bool) :
    gfIsZero m a = true ↔ gfDecode m a = 0 := by
  rw [gfDecode_eq_basis, LinearEquiv.map_eq_zero_iff, gfIsZero, List.all_eq_true]
  simp only [List.mem_range, Bool.not_eq_true']
  constructor
  · intro h
    funext i
    simp only [bitVec, h i i.2, Bool.false_eq_true, if_false, Pi.zero_apply]
  · intro h i hi
    have := congrFun h ⟨i, hi⟩
    simp only [bitVec, Pi.zero_apply] at this
    revert this
    cases a.getD i false <;> simp

/-- `Bool ≃ 𝔽₂`. -/
def boolEquivZMod2 : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv := by decide
  right_inv := by decide

theorem gfDecode_bijective (m : ℕ) :
    Function.Bijective (fun v : Fin (2 * m) → Bool => gfDecode m (List.ofFn v)) := by
  have hf : (fun v : Fin (2 * m) → Bool => gfDecode m (List.ofFn v)) =
      (gfBasis m).equivFun.symm ∘ (Equiv.arrowCongr (Equiv.refl _) boolEquivZMod2) := by
    funext v
    rw [gfDecode_eq_basis]
    congr 1
    funext i
    simp [bitVec, boolEquivZMod2, List.getD_eq_getElem?_getD]
  rw [hf]
  exact (gfBasis m).equivFun.symm.bijective.comp (Equiv.bijective _)

theorem nat_card_GF (m : ℕ) : Nat.card (GF m) = 2 ^ (2 * m) := by
  rw [Nat.card_congr (gfBasis m).equivFun.toEquiv]
  simp

lemma gfPoly_ne_one_of_irreducible (m : ℕ) [Fact (Irreducible (gfPoly m))] : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := (Fact.out : Irreducible (gfPoly 0))
    rw [gfPoly_zero] at this
    exact absurd isUnit_one this.not_isUnit
  · exact hm

lemma gf_nontrivial (m : ℕ) (hm : 0 < m) : Nontrivial (GF m) := by
  apply AdjoinRoot.nontrivial
  rw [degree_eq_natDegree (gfPoly_monic m).ne_zero, gfPoly_natDegree]
  exact_mod_cast (by omega : 2 * m ≠ 0)

/-- `GF m` has characteristic two for `m ≥ 1`. (For `m = 0` the ring is trivial and
`CharP (GF 0) 2` is false.) -/
theorem charP_GF (m : ℕ) (hm : 0 < m) : CharP (GF m) 2 := by
  have := gf_nontrivial m hm
  exact charP_of_injective_algebraMap' (ZMod 2) 2

instance (m : ℕ) [NeZero m] : CharP (GF m) 2 := charP_GF m (Nat.pos_of_ne_zero (NeZero.ne m))

instance instCharPGFIrr (m : ℕ) [Fact (Irreducible (gfPoly m))] : CharP (GF m) 2 :=
  charP_GF m (gfPoly_ne_one_of_irreducible m)

theorem not_charP_GF_zero : ¬ CharP (GF 0) 2 := by
  intro h
  have := gf_zero_subsingleton
  have h1 := (CharP.cast_eq_zero_iff (GF 0) 2 1).1 (Subsingleton.elim _ _)
  norm_num at h1

lemma cast_length_filter {R : Type*} [CommSemiring R] {α : Type*} (L : List α) (p : α → Bool) :
    ((L.filter p).length : R) = (L.map (fun x => if p x then (1 : R) else 0)).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    by_cases h : p x
    · simp [h, ih, add_comm]
    · simp [h, ih]

lemma list_sum_map_range {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma list_sum_flatMap {R : Type*} [AddCommMonoid R] {α β : Type*} (l : List α)
    (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma cast_length_filter_pairs (m : ℕ) (p : ℕ × ℕ → Bool) :
    (((gfIndexPairs m).filter p).length : GF m) =
      ∑ j ∈ Finset.range (2 * m), ∑ l ∈ Finset.range (2 * m), if p (j, l) then (1 : GF m) else 0 := by
  rw [cast_length_filter, gfIndexPairs, list_sum_flatMap, list_sum_map_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.map_map, list_sum_map_range]
  rfl

lemma gf_parity (m n : ℕ) (y : GF m) : (if (n % 2 == 1) = true then y else 0) = (n : GF m) * y := by
  have hn : (n : GF m) = ((n % 2 : ℕ) : GF m) := by
    conv_lhs => rw [← Nat.mod_add_div n 2]
    push_cast
    rw [gf_two_eq_zero]; ring
  rw [hn]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

lemma gf_root_pow_reduce (m e : ℕ) (he : e < 3 * m) :
    (rt m) ^ e = ∑ i ∈ Finset.range (2 * m),
      if (e == i || e == (if i < m then i + 2 * m else i + m)) = true then (rt m) ^ i else 0 := by
  rcases Nat.lt_or_ge e (2 * m) with h | h
  · rw [Finset.sum_eq_single e]
    · simp
    · intro i hi hie
      rw [Finset.mem_range] at hi
      have : ¬ ((e == i || e == (if i < m then i + 2 * m else i + m)) = true) := by
        simp only [Bool.or_eq_true, beq_iff_eq]
        split_ifs <;> omega
      rw [if_neg this]
    · intro hn; exact absurd (Finset.mem_range.2 h) hn
  · rw [gf_root_pow_fold m e h]
    have key : ∀ i ∈ Finset.range (2 * m),
        (if (e == i || e == (if i < m then i + 2 * m else i + m)) = true then (rt m) ^ i else 0) =
        (if e - m = i then (rt m) ^ i else 0) + (if e - 2 * m = i then (rt m) ^ i else 0) := by
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [Bool.or_eq_true, beq_iff_eq]
      split_ifs <;> first | (exfalso; omega) | simp
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
      if_pos (Finset.mem_range.2 (by omega)), if_pos (Finset.mem_range.2 (by omega))]

theorem gfDecode_mul (m : ℕ) (a b : List Bool) :
    gfDecode m (gfMul m a b) = gfDecode m a * gfDecode m b := by
  -- left-hand side
  have hL : gfDecode m (gfMul m a b) = ∑ i ∈ Finset.range (2 * m),
      ∑ j ∈ Finset.range (2 * m), ∑ l ∈ Finset.range (2 * m),
        if (a.getD j false && b.getD l false &&
          ((j + l) % (3 * m) == i ||
            (j + l) % (3 * m) == (if i < m then i + 2 * m else i + m))) = true
        then (rt m) ^ i else 0 := by
    unfold gfDecode
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gfMul, getD_map_range _ _ _ (Finset.mem_range.1 hi), gf_parity,
      cast_length_filter_pairs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ite_mul, one_mul, zero_mul]
  have hR : gfDecode m a * gfDecode m b = ∑ j ∈ Finset.range (2 * m),
      ∑ l ∈ Finset.range (2 * m), ∑ i ∈ Finset.range (2 * m),
        if (a.getD j false && b.getD l false &&
          ((j + l) % (3 * m) == i ||
            (j + l) % (3 * m) == (if i < m then i + 2 * m else i + m))) = true
        then (rt m) ^ i else 0 := by
    unfold gfDecode
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hj hl
    have hm : 0 < 3 * m := by omega
    have hpow : (rt m) ^ (j + l) = (rt m) ^ ((j + l) % (3 * m)) := by
      conv_lhs => rw [← Nat.mod_add_div (j + l) (3 * m)]
      rw [pow_add, pow_mul, gf_root_pow_three, one_pow, mul_one]
    cases a.getD j false <;> cases b.getD l false <;>
      simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, if_false, zero_mul, mul_zero,
        if_true, Finset.sum_const_zero]
    rw [← pow_add, hpow, gf_root_pow_reduce m _ (Nat.mod_lt _ hm)]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

lemma gfInv_fold (m : ℕ) (a : List Bool) (n : ℕ) :
    gfDecode m ((List.range n).foldl
      (fun (st : List Bool × List Bool) (_ : ℕ) => (gfMul m st.1 st.1, gfMul m st.2 (gfMul m st.1 st.1)))
      (a, gfOne m)).1 = gfDecode m a ^ (2 ^ n) ∧
    gfDecode m ((List.range n).foldl
      (fun (st : List Bool × List Bool) (_ : ℕ) => (gfMul m st.1 st.1, gfMul m st.2 (gfMul m st.1 st.1)))
      (a, gfOne m)).2 = gfDecode m a ^ (2 ^ (n + 1) - 2) := by
  induction n with
  | zero => simp [gfDecode_one]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, gfDecode_mul, ih.1, ih.2]
    constructor
    · rw [← pow_add, ← two_mul, ← pow_succ']
    · rw [← pow_add, ← pow_add]
      congr 1
      have : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (by omega) 2
      rw [pow_succ 2 (n + 1)]
      omega

theorem gfDecode_inv (m : ℕ) [Fact (Irreducible (gfPoly m))] (a : List Bool) :
    gfDecode m (gfInv m a) = (gfDecode m a)⁻¹ := by
  have hm := gfPoly_ne_one_of_irreducible m
  have hfin : Finite (GF m) := Nat.finite_of_card_ne_zero (by rw [nat_card_GF]; positivity)
  let _ := Fintype.ofFinite (GF m)
  have hcard : Fintype.card (GF m) = 2 ^ (2 * m) := by
    rw [← Nat.card_eq_fintype_card, nat_card_GF]
  have h := (gfInv_fold m a (2 * m - 1)).2
  rw [gfInv, h, show 2 * m - 1 + 1 = 2 * m by omega]
  set x := gfDecode m a
  have h4 : 4 ≤ 2 ^ (2 * m) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hx : x = 0
  · rw [hx, inv_zero, zero_pow (by omega)]
  · have h1 := FiniteField.pow_card_sub_one_eq_one x hx
    rw [hcard, show 2 ^ (2 * m) - 1 = (2 ^ (2 * m) - 2) + 1 by omega, pow_succ] at h1
    exact eq_inv_of_mul_eq_one_left h1

/-! ### Length lemmas -/

lemma gfZero_length (m : ℕ) : (gfZero m).length = 2 * m := by simp [gfZero]

lemma gfOne_length (m : ℕ) : (gfOne m).length = 2 * m := by simp [gfOne]

lemma gfAdd_length (m : ℕ) (a b : List Bool) : (gfAdd m a b).length = 2 * m := by simp [gfAdd]

lemma gfMul_length (m : ℕ) (a b : List Bool) : (gfMul m a b).length = 2 * m := by simp [gfMul]

lemma gfInv_length (m : ℕ) (a : List Bool) : (gfInv m a).length = 2 * m := by
  unfold gfInv
  generalize 2 * m - 1 = n
  induction n with
  | zero => simp [gfOne_length]
  | succ n ih => rw [List.range_succ, List.foldl_append]; simp [gfMul_length]

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

-- ===== from Solutions/Lib/Det.lean =====
section

namespace PfaffianRecognition.CoRP.DetAux

open Finset

theorem det_char_two_symm {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CharP R 2]
    (B : Matrix ι ι R) (hB : ∀ i j, B i j = B j i) (hd : ∀ i, B i i = 0) :
    B.det = ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => ∀ i, σ (σ i) = i ∧ σ i ≠ i),
      ∏ i, B (σ i) i := by
  rw [Matrix.det_apply]
  have hsign : ∀ σ : Equiv.Perm ι, (Equiv.Perm.sign σ • ∏ i, B (σ i) i) = ∏ i, B (σ i) i := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
    · simp
    · rw [Units.neg_smul, one_smul, CharTwo.neg_eq]
  simp_rw [hsign]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun σ : Equiv.Perm ι => ∀ i, σ (σ i) = i ∧ σ i ≠ i)]
  have hinv : ∀ σ : Equiv.Perm ι, ∏ i, B (σ⁻¹ i) i = ∏ i, B (σ i) i := by
    intro σ
    rw [← Equiv.prod_comp σ (fun i => B (σ⁻¹ i) i)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show σ⁻¹ (σ i) = i from Equiv.Perm.inv_eq_iff_eq.mpr rfl]
    exact hB _ _
  rw [add_eq_left]
  refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
  · intro σ _
    rw [hinv, CharTwo.add_self_eq_zero]
  · intro σ hσ hne heq
    simp only [mem_filter, mem_univ, true_and, not_forall] at hσ
    obtain ⟨i, hi⟩ := hσ
    have hinvol : ∀ j, σ (σ j) = j := by
      intro j
      have : σ⁻¹ (σ j) = σ (σ j) := by rw [heq]
      simpa using this.symm
    have hfix : σ i = i := by
      by_contra h
      exact hi ⟨hinvol i, h⟩
    apply hne
    exact Finset.prod_eq_zero (mem_univ i) (by rw [hfix, hd])
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro h
    apply hσ
    have hinvol : ∀ j, σ⁻¹ (σ⁻¹ j) = j := fun j => (h j).1
    have heq : σ = σ⁻¹ := by
      ext j
      have h1 : σ⁻¹ (σ j) = j := Equiv.Perm.inv_eq_iff_eq.mpr rfl
      have := hinvol (σ j)
      rw [h1] at this
      exact this.symm
    intro j
    constructor
    · rw [heq]
      exact hinvol j
    · intro hj
      apply (h j).2
      rw [← heq, hj]
  · intro σ _
    exact inv_inv σ

variable {N : ℕ}

def IsPMOn (G : SimpleGraph (Fin N)) (p : Fin N → Prop) (M : Finset G.edgeSet) : Prop :=
  (∀ e ∈ M, ∀ v ∈ (e : Sym2 (Fin N)), p v) ∧
    ∀ v, p v → ∃! e, e ∈ M ∧ v ∈ (e : Sym2 (Fin N))

section partner

variable {G : SimpleGraph (Fin N)} {p : Fin N → Prop} {M : Finset G.edgeSet}

theorem exists_partner (hM : IsPMOn G p M) (i : {v // p v}) :
    ∃ j : {v // p v}, ∃ e ∈ M, (e : Sym2 (Fin N)) = s(i.val, j.val) := by
  obtain ⟨e, ⟨heM, hie⟩, _⟩ := hM.2 i.val i.2
  exact ⟨⟨Sym2.Mem.other hie, hM.1 e heM _ (Sym2.other_mem hie)⟩, e, heM,
    (Sym2.other_spec hie).symm⟩

noncomputable def partner (hM : IsPMOn G p M) (i : {v // p v}) : {v // p v} :=
  Classical.choose (exists_partner hM i)

theorem partner_spec (hM : IsPMOn G p M) (i : {v // p v}) :
    ∃ e ∈ M, (e : Sym2 (Fin N)) = s(i.val, (partner hM i).val) :=
  Classical.choose_spec (exists_partner hM i)

theorem partner_eq (hM : IsPMOn G p M) {i j : {v // p v}} (e : G.edgeSet) (he : e ∈ M)
    (h : (e : Sym2 (Fin N)) = s(i.val, j.val)) : partner hM i = j := by
  obtain ⟨e', he', h'⟩ := partner_spec hM i
  obtain ⟨_, _, huniq⟩ := hM.2 i.val i.2
  have h1 : e = e' := by
    have a := huniq e ⟨he, by rw [h]; exact Sym2.mem_mk_left _ _⟩
    have b := huniq e' ⟨he', by rw [h']; exact Sym2.mem_mk_left _ _⟩
    rw [a, b]
  subst h1
  rw [h] at h'
  exact Subtype.ext (Sym2.congr_right.mp h').symm

theorem partner_invol (hM : IsPMOn G p M) : Function.Involutive (partner hM) := by
  intro i
  obtain ⟨e, he, h⟩ := partner_spec hM i
  exact partner_eq hM e he (by rw [h, Sym2.eq_swap])

theorem partner_adj (hM : IsPMOn G p M) (i : {v // p v}) :
    G.Adj i.val (partner hM i).val := by
  obtain ⟨e, he, h⟩ := partner_spec hM i
  have := e.2
  rw [h] at this
  exact G.mem_edgeSet.mp this

theorem partner_ne (hM : IsPMOn G p M) (i : {v // p v}) : partner hM i ≠ i := by
  intro h
  have := partner_adj hM i
  rw [h] at this
  exact G.loopless.irrefl _ this

end partner

open Classical in
theorem det_submatrix_eq {R : Type*} [CommRing R] [CharP R 2] (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (w : G.edgeSet → R) (p : Fin N → Prop) [DecidablePred p] :
    ((Matrix.of fun i j : Fin N => if h : G.Adj i j then w ⟨s(i, j), G.mem_edgeSet.mpr h⟩ else 0).submatrix
      (Subtype.val : {v // p v} → Fin N) Subtype.val).det =
    ∑ M ∈ univ.filter (fun M : Finset G.edgeSet => IsPMOn G p M), ∏ e ∈ M, w e ^ 2 := by
  set A := (Matrix.of fun i j : Fin N => if h : G.Adj i j then w ⟨s(i, j), G.mem_edgeSet.mpr h⟩ else 0).submatrix
      (Subtype.val : {v // p v} → Fin N) Subtype.val with hA
  have hsymm : ∀ i j, A i j = A j i := by
    intro i j
    simp only [hA, Matrix.submatrix_apply, Matrix.of_apply]
    by_cases h : G.Adj i.val j.val
    · rw [dif_pos h, dif_pos h.symm]
      congr 2
      exact Sym2.eq_swap
    · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]
  have hdiag : ∀ i, A i i = 0 := by
    intro i
    simp only [hA, Matrix.submatrix_apply, Matrix.of_apply]
    rw [dif_neg (G.loopless.irrefl _)]
  rw [det_char_two_symm A hsymm hdiag]
  rw [← Finset.sum_filter_of_ne (p := fun σ : Equiv.Perm {v // p v} => ∀ i, G.Adj (σ i).val i.val)]
  swap
  · intro σ _ hne i
    by_contra h
    apply hne
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hA, h])
  rw [Finset.filter_filter]
  refine Finset.sum_bij'
    (fun σ _ => univ.filter (fun e : G.edgeSet => ∃ i : {v // p v}, (e : Sym2 (Fin N)) = s(i.val, (σ i).val)))
    (fun M hM => Function.Involutive.toPerm (partner (mem_filter.mp hM).2) (partner_invol _))
    ?_ ?_ ?_ ?_ ?_
  · -- forward lands in matchings
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    obtain ⟨h1, h2⟩ := hσ
    refine ⟨?_, ?_⟩
    · intro e he v hv
      simp only [mem_filter, mem_univ, true_and] at he
      obtain ⟨i, hi⟩ := he
      rw [hi, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact i.2
      · exact (σ i).2
    · intro v hv
      refine ⟨⟨s(v, (σ ⟨v, hv⟩).val), G.mem_edgeSet.mpr (h2 ⟨v, hv⟩).symm⟩,
        ⟨by simp only [mem_filter, mem_univ, true_and]; exact ⟨⟨v, hv⟩, rfl⟩,
          Sym2.mem_mk_left _ _⟩, ?_⟩
      rintro e' ⟨he', hve'⟩
      simp only [mem_filter, mem_univ, true_and] at he'
      obtain ⟨i', hi'⟩ := he'
      apply Subtype.ext
      simp only
      rw [hi'] at hve' ⊢
      rw [Sym2.mem_iff] at hve'
      rcases hve' with h | h
      · have : i' = ⟨v, hv⟩ := Subtype.ext h.symm
        rw [this]
      · have : (⟨v, hv⟩ : {v // p v}) = σ i' := Subtype.ext h
        rw [this, (h1 i').1, Sym2.eq_swap, h]
  · -- backward lands in involutions
    intro M hM
    simp only [mem_filter, mem_univ, true_and, Function.Involutive.coe_toPerm]
    refine ⟨fun i => ⟨partner_invol _ i, partner_ne _ i⟩, fun i => (partner_adj _ i).symm⟩
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    apply Equiv.ext
    intro i
    simp only [Function.Involutive.coe_toPerm]
    refine (partner_eq _ ⟨s(i.val, (σ i).val), G.mem_edgeSet.mpr (hσ.2 i).symm⟩ ?_ rfl)
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨i, rfl⟩
  · intro M hM
    have hM' := (mem_filter.mp hM).2

    apply Finset.ext
    intro e
    rw [Finset.mem_filter]
    simp only [mem_univ, true_and, Function.Involutive.coe_toPerm]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨e', he', h'⟩ := partner_spec hM' i
      have : e = e' := Subtype.ext (hi.trans h'.symm)
      rw [this]; exact he'
    · intro he
      have ha : e.val.out.1 ∈ (e : Sym2 (Fin N)) := Sym2.out_fst_mem _
      set i : {v // p v} := ⟨e.val.out.1, hM'.1 e he _ ha⟩
      obtain ⟨e', he', h'⟩ := partner_spec hM' i
      obtain ⟨_, _, huniq⟩ := hM'.2 i.val i.2
      have h1 : e = e' := by
        rw [huniq e ⟨he, ha⟩, huniq e' ⟨he', by rw [h']; exact Sym2.mem_mk_left _ _⟩]
      exact ⟨i, by rw [h1]; exact h'⟩
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    obtain ⟨h1, h2⟩ := hσ
    set E : {v // p v} → G.edgeSet :=
      fun i => ⟨s(i.val, (σ i).val), G.mem_edgeSet.mpr (h2 i).symm⟩ with hE
    have step1 : ∏ i, A (σ i) i = ∏ i, w (E i) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [hA, Matrix.submatrix_apply, Matrix.of_apply, hE]
      rw [dif_pos (h2 i)]
      congr 2
      exact Sym2.eq_swap
    rw [step1, Finset.prod_comp w E]
    have himg : univ.image E =
        univ.filter (fun e : G.edgeSet => ∃ i : {v // p v}, (e : Sym2 (Fin N)) = s(i.val, (σ i).val)) := by
      ext e
      simp only [mem_image, mem_univ, true_and, mem_filter, hE]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi.symm⟩
    rw [himg]
    refine Finset.prod_congr rfl (fun e he => ?_)
    congr 1
    simp only [mem_filter, mem_univ, true_and] at he
    obtain ⟨i₀, hi₀⟩ := he
    have hfil : univ.filter (fun i => E i = e) = {i₀, σ i₀} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hE]
      rw [Subtype.ext_iff, hi₀]
      simp only
      rw [Sym2.eq_iff]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, by rw [(h1 i₀).1]⟩
    rw [hfil, Finset.card_pair (h1 i₀).2.symm]

end PfaffianRecognition.CoRP.DetAux

namespace PfaffianRecognition.CoRP

open PfaffianRecognition.Recognition

/-- In characteristic two the determinant of an edge-weighted symmetric adjacency matrix is the sum,
over perfect matchings, of the squared weight products. -/
theorem det_weighted_adjacency_char_two {R : Type*} [CommRing R] [CharP R 2] {N : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (w : G.edgeSet → R) :
    (Matrix.of fun i j : Fin N => if h : G.Adj i j then w ⟨s(i, j), G.mem_edgeSet.mpr h⟩ else 0).det =
      ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G, ∏ e ∈ M, w e ^ 2 := by
  classical
  rw [← Matrix.det_submatrix_equiv_self
    (Equiv.subtypeUnivEquiv (p := fun _ : Fin N => True) (fun _ => trivial))]
  have h := DetAux.det_submatrix_eq G w (fun _ => True)
  convert h using 1
  · rfl
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext M
  rw [Finset.mem_filter]
  unfold MulmuleyVV.Matching.perfectMatchings
  rw [Finset.mem_filter]
  simp [DetAux.IsPMOn,
    MulmuleyVV.Matching.IsPerfectMatchingEdges]

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

-- ===== from Solutions/Main/SoundDefs.lean =====
section

/-! Definitions shared by the soundness proof. -/

namespace PfaffianRecognition.CoRP
open PfaffianRecognition.Recognition

variable {N : ℕ} {G : SimpleGraph (Fin N)}

/-- Position of an edge in the parsed edge list of `graphBits G`. -/
noncomputable def eIdx (e : G.edgeSet) : ℕ :=
  (encEdges (CatalyticMatching.General.graphBits G)).idxOf (toPair e)

/-- The field weight of the edge `e` in a weight list `β` (aligned with the parsed edge list). -/
noncomputable def wt (m : ℕ) (β : List (List Bool)) (e : G.edgeSet) : GF m :=
  gfDecode m (β.getD (eIdx e) [])

/-- Number of edges of `M` marked by `d` (aligned with the parsed edge list). -/
noncomputable def markCount (d : List Bool) (M : Finset G.edgeSet) : ℕ := by
  classical exact (M.filter (fun e => d.getD (eIdx e) false = true)).card

/-- `M` is inconsistent with `(d, s)`: `Σ_{e∈M} d_e + s ≠ cr(M)` in `𝔽₂`. -/
def Viol (d : List Bool) (s : Bool) (M : Finset G.edgeSet) : Prop :=
  (crossingParity M + markCount d M + (if s then 1 else 0)) % 2 = 1

end PfaffianRecognition.CoRP

end

-- ===== from Solutions/Main/SoundA.lean =====
section

namespace PfaffianRecognition.CoRP
open PfaffianRecognition.Recognition

variable {N : ℕ} {G : SimpleGraph (Fin N)}

theorem eIdx_lt (e : G.edgeSet) : eIdx e < (encEdges (CatalyticMatching.General.graphBits G)).length := by
  unfold eIdx
  exact List.idxOf_lt_length_of_mem ((mem_encEdges_graphBits _).2 ⟨e, rfl⟩)

theorem getElem_eIdx (e : G.edgeSet) :
    (encEdges (CatalyticMatching.General.graphBits G))[eIdx e]'(eIdx_lt e) = toPair e := by
  unfold eIdx
  exact List.getElem_idxOf _

namespace SA

theorem range_map_ofFn {β : Type} (n : ℕ) (f : ℕ → β) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i) := by
  apply List.ext_getElem <;> simp

theorem toPair_eq_minmax (i j : Fin N) (h : G.Adj i j) :
    toPair (⟨s(i, j), G.mem_edgeSet.2 h⟩ : G.edgeSet) = (min (i : ℕ) j, max (i : ℕ) j) := by
  rcases lt_or_gt_of_ne (G.ne_of_adj h) with hij | hij
  · obtain ⟨h1, h2⟩ := edgeLo_hi_of_eq (G := G) ⟨s(i, j), G.mem_edgeSet.2 h⟩ i j hij rfl
    simp only [toPair, h1, h2]
    have : (i : ℕ) < j := hij
    rw [min_eq_left this.le, max_eq_right this.le]
  · obtain ⟨h1, h2⟩ := edgeLo_hi_of_eq (G := G) ⟨s(i, j), G.mem_edgeSet.2 h⟩ j i hij Sym2.eq_swap
    simp only [toPair, h1, h2]
    have : (j : ℕ) < i := hij
    rw [min_eq_right this.le, max_eq_left this.le]

open Classical in
theorem entry_eq (m : ℕ) (β : List (List Bool))
    (hβ : β.length = (encEdges (CatalyticMatching.General.graphBits G)).length) (i j : Fin N) :
    gfDecode m (β.getD ((encEdges (CatalyticMatching.General.graphBits G)).findIdx
        (fun e => e == (min (i : ℕ) j, max (i : ℕ) j))) (gfZero m)) =
      if h : G.Adj i j then wt m β ⟨s(i, j), G.mem_edgeSet.2 h⟩ else 0 := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  split_ifs with h
  · set e : G.edgeSet := ⟨s(i, j), G.mem_edgeSet.2 h⟩
    have hidx : E.findIdx (fun x => x == (min (i : ℕ) j, max (i : ℕ) j)) = eIdx e := by
      rw [← toPair_eq_minmax i j h]; rfl
    rw [hidx, wt]
    have hl : eIdx e < β.length := hβ ▸ eIdx_lt e
    rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl]
  · have hnot : E.findIdx (fun x => x == (min (i : ℕ) j, max (i : ℕ) j)) = E.length := by
      rw [List.findIdx_eq_length]
      intro x hx
      simp only [beq_eq_false_iff_ne]
      rintro rfl
      obtain ⟨e, he⟩ := (mem_encEdges_graphBits _).1 hx
      apply h
      have hlt := toPair_lt e
      simp only [toPair, Prod.mk.injEq] at he
      have h1 : edgeLo e = min i j := Fin.ext (by rw [he.1]; simp)
      have h2 : edgeHi e = max i j := Fin.ext (by rw [he.2]; simp)
      have hadj := edge_adj e
      rw [h1, h2] at hadj
      rcases le_total i j with hij | hij
      · rwa [min_eq_left hij, max_eq_right hij] at hadj
      · rw [min_eq_right hij, max_eq_left hij] at hadj; exact hadj.symm
    rw [hnot, ← hβ, List.getD_eq_default _ _ le_rfl, gfDecode_zero]

open Classical in
theorem phi_decode (m : ℕ) [Fact (Irreducible (gfPoly m))] (β : List (List Bool))
    (hβ : β.length = (encEdges (CatalyticMatching.General.graphBits G)).length) :
    gfDecode m (phiVal m N (encEdges (CatalyticMatching.General.graphBits G)) β) =
      ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G, ∏ e ∈ M, wt m β e ^ 2 := by
  unfold phiVal
  rw [detAlg_map (gfOps m) (stdOps (GF m)) (gfDecode m) (gfDecode_zero m) (gfDecode_one m)
    (gfDecode_add m) (gfDecode_neg m) (gfDecode_mul m) (gfDecode_inv m)
    (fun a => Bool.eq_iff_iff.2 (by simp [gfOps, stdOps, gfIsZero_iff]))]
  have hmat : (weightMatrix m N (encEdges (CatalyticMatching.General.graphBits G)) β).map
      (List.map (gfDecode m)) = List.ofFn (fun i => List.ofFn
        ((Matrix.of fun i j : Fin N => if h : G.Adj i j then
          wt m β ⟨s(i, j), G.mem_edgeSet.mpr h⟩ else 0) i)) := by
    unfold weightMatrix
    rw [List.map_map, range_map_ofFn]
    congr 1; funext i
    simp only [Function.comp]
    rw [List.map_map, range_map_ofFn]
    congr 1; funext j
    simp only [Function.comp, Matrix.of_apply]
    exact entry_eq m β hβ i j
  rw [hmat, detAlg_stdOps, det_weighted_adjacency_char_two]

/-- Two pairs share an endpoint. -/
def share (p q : ℕ × ℕ) : Prop := p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2

theorem touches_iff (S : List (ℕ × ℕ)) (e : ℕ × ℕ) :
    touches S e = true ↔ ∃ f ∈ S, share f e := by
  simp [touches, share, List.any_eq_true, or_assoc]

theorem share_toPair (e f : G.edgeSet) :
    share (toPair e) (toPair f) ↔ ∃ v, v ∈ (e : Sym2 (Fin N)) ∧ v ∈ (f : Sym2 (Fin N)) := by
  simp only [share, toPair, mem_edge_iff]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨_, Or.inl rfl, Or.inl (Fin.ext h)⟩
    · exact ⟨_, Or.inl rfl, Or.inr (Fin.ext h)⟩
    · exact ⟨_, Or.inr rfl, Or.inl (Fin.ext h)⟩
    · exact ⟨_, Or.inr rfl, Or.inr (Fin.ext h)⟩
  · rintro ⟨v, h1 | h1, h2 | h2⟩ <;> subst h1 <;> simp_all

theorem pm_eq_of_mem {M : Finset G.edgeSet} (hM : MulmuleyVV.Matching.IsPerfectMatchingEdges G M)
    {e f : G.edgeSet} (he : e ∈ M) (hf : f ∈ M) (v : Fin N) (hve : v ∈ (e : Sym2 (Fin N)))
    (hvf : v ∈ (f : Sym2 (Fin N))) : e = f := by
  obtain ⟨g, -, hg⟩ := hM v
  rw [hg e ⟨he, hve⟩, hg f ⟨hf, hvf⟩]

theorem kill_length (m : ℕ) (E S : List (ℕ × ℕ)) (β : List (List Bool)) (hβ : β.length = E.length) :
    (kill m E S β).length = E.length := by
  simp [kill, hβ]

theorem wt_kill (m : ℕ) (S : List (ℕ × ℕ)) (β : List (List Bool))
    (hβ : β.length = (encEdges (CatalyticMatching.General.graphBits G)).length) (e : G.edgeSet) :
    wt m (kill m (encEdges (CatalyticMatching.General.graphBits G)) S β) e =
      if toPair e ∈ S then wt m β e else if touches S (toPair e) then 0 else wt m β e := by
  have hl : eIdx e < (kill m (encEdges (CatalyticMatching.General.graphBits G)) S β).length := by
    rw [kill_length _ _ _ _ hβ]; exact eIdx_lt e
  have hl2 : eIdx e < β.length := hβ ▸ eIdx_lt e
  unfold wt
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl2]
  simp only [kill, List.getElem_map, List.getElem_zip, getElem_eIdx, List.contains_iff_mem]
  split_ifs <;> simp [gfDecode_zero]

open Classical in
theorem prod_kill (m : ℕ) (S : List (ℕ × ℕ)) (β : List (List Bool))
    (hβ : β.length = (encEdges (CatalyticMatching.General.graphBits G)).length)
    (hS : ∀ p ∈ S, p ∈ encEdges (CatalyticMatching.General.graphBits G))
    (hd : ∀ p ∈ S, ∀ q ∈ S, share p q → p = q)
    (M : Finset G.edgeSet) (hM : MulmuleyVV.Matching.IsPerfectMatchingEdges G M) :
    ∏ e ∈ M, wt m (kill m (encEdges (CatalyticMatching.General.graphBits G)) S β) e ^ 2 =
      if (∀ e : G.edgeSet, toPair e ∈ S → e ∈ M) then ∏ e ∈ M, wt m β e ^ 2 else 0 := by
  classical
  split_ifs with hsub
  · refine Finset.prod_congr rfl (fun e he => ?_)
    rw [wt_kill m S β hβ e]
    split_ifs with h1 h2
    · rfl
    · exfalso
      obtain ⟨f, hf, hsh⟩ := (touches_iff S _).1 h2
      obtain ⟨f', rfl⟩ := (mem_encEdges_graphBits f).1 (hS f hf)
      obtain ⟨v, hv1, hv2⟩ := (share_toPair f' e).1 hsh
      have := pm_eq_of_mem hM (hsub f' hf) he v hv1 hv2
      subst this; exact h1 hf
    · rfl
  · push Not at hsub
    obtain ⟨f, hfS, hfM⟩ := hsub
    obtain ⟨g, ⟨hgM, hvg⟩, -⟩ := hM (edgeLo f)
    apply Finset.prod_eq_zero hgM
    rw [wt_kill m S β hβ g]
    have hgf : g ≠ f := fun h => hfM (h ▸ hgM)
    have hsh : share (toPair f) (toPair g) :=
      (share_toPair f g).2 ⟨edgeLo f, (mem_edge_iff f _).2 (Or.inl rfl), hvg⟩
    have hgS : toPair g ∉ S := fun hgS => hgf (toPair_injective (hd _ hfS _ hgS hsh).symm)
    have ht : touches S (toPair g) = true := (touches_iff S _).2 ⟨_, hfS, hsh⟩
    simp [hgS, ht]

theorem sum_swap {α β R : Type*} [CommSemiring R] (L : List α) (T : Finset β) (c : α → β → Prop)
    [∀ x y, Decidable (c x y)] (g : β → R) :
    (L.map (fun x => ∑ M ∈ T, if c x M then g M else 0)).sum =
      ∑ M ∈ T, ((L.filter (fun x => decide (c x M))).length : R) * g M := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    by_cases h : c x M
    · simp [h]; ring
    · simp [h]

open Classical in
theorem phi_kill_decode (m : ℕ) [Fact (Irreducible (gfPoly m))] (S : List (ℕ × ℕ))
    (β : List (List Bool))
    (hβ : β.length = (encEdges (CatalyticMatching.General.graphBits G)).length)
    (hS : ∀ p ∈ S, p ∈ encEdges (CatalyticMatching.General.graphBits G))
    (hd : ∀ p ∈ S, ∀ q ∈ S, share p q → p = q) :
    gfDecode m (phiVal m N (encEdges (CatalyticMatching.General.graphBits G))
        (kill m (encEdges (CatalyticMatching.General.graphBits G)) S β)) =
      ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G,
        if (∀ e : G.edgeSet, toPair e ∈ S → e ∈ M) then ∏ e ∈ M, wt m β e ^ 2 else 0 := by
  rw [phi_decode m _ (kill_length _ _ _ _ hβ)]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  have hM' : MulmuleyVV.Matching.IsPerfectMatchingEdges G M := by
    unfold MulmuleyVV.Matching.perfectMatchings at hM
    exact (Finset.mem_filter.1 hM).2
  exact prod_kill m S β hβ hS hd M hM'

theorem zip_nodup {α β : Type} (E : List α) (d : List β) (h : E.Nodup) : (E.zip d).Nodup := by
  induction E generalizing d with
  | nil => simp
  | cons a E ih =>
    cases d with
    | nil => simp
    | cons b d =>
      rw [List.zip_cons_cons, List.nodup_cons]
      rw [List.nodup_cons] at h
      exact ⟨fun hm => h.1 (List.of_mem_zip hm).1, ih d h.2⟩

open Classical in
theorem mark_count (d : List Bool) (M : Finset G.edgeSet) (q : ℕ × ℕ → Bool)
    (hq : ∀ p ∈ encEdges (CatalyticMatching.General.graphBits G),
      q p = true ↔ ∃ e ∈ M, toPair e = p) :
    (((encEdges (CatalyticMatching.General.graphBits G)).zip d).filter
      (fun ed => ed.2 && q ed.1)).length = markCount d M := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  have hEnd : E.Nodup := encEdges_nodup _
  have hnd := (zip_nodup E d hEnd).filter (fun ed => ed.2 && q ed.1)
  rw [← List.toFinset_card_of_nodup hnd, markCount]
  rw [← Finset.card_image_of_injective _ (f := fun e : G.edgeSet => (toPair e, true))
    (by intro a b h; simp only [Prod.mk.injEq] at h; exact toPair_injective h.1)]
  congr 1
  ext ⟨p, b⟩
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_image, Finset.mem_filter,
    Bool.and_eq_true, Prod.mk.injEq]
  constructor
  · rintro ⟨hm, hb, hqp⟩
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hm
    rw [List.getElem_zip, Prod.mk.injEq] at hget
    obtain ⟨e, heM, rfl⟩ := (hq p (List.of_mem_zip hm).1).1 hqp
    subst hb
    have hi1 : i < E.length := by simp at hi; omega
    have hi2 : i < d.length := by simp at hi; omega
    have hei : eIdx e = i := by
      have h1 : E[eIdx e]'(eIdx_lt e) = E[i] := by rw [getElem_eIdx, hget.1]
      exact (hEnd.getElem_inj_iff).1 h1
    refine ⟨e, ⟨heM, ?_⟩, rfl, rfl⟩
    rw [hei, List.getD_eq_getElem _ _ hi2, hget.2]
  · rintro ⟨e, ⟨heM, hd⟩, rfl, rfl⟩
    have hi2 : eIdx e < d.length := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by omega)] at hd
      exact Bool.false_ne_true hd
    rw [List.getD_eq_getElem _ _ hi2] at hd
    refine ⟨List.mem_iff_getElem.2 ⟨eIdx e, by rw [List.length_zip]; exact lt_min (eIdx_lt e) hi2, ?_⟩, rfl,
      (hq _ ((mem_encEdges_graphBits _).2 ⟨e, rfl⟩)).2 ⟨e, heM, rfl⟩⟩
    rw [List.getElem_zip, getElem_eIdx, hd]

open Classical in
theorem cross_count (M : Finset G.edgeSet) (q : ℕ × ℕ → Bool)
    (hq : ∀ p ∈ encEdges (CatalyticMatching.General.graphBits G),
      q p = true ↔ ∃ e ∈ M, toPair e = p) :
    ((crossPairs (encEdges (CatalyticMatching.General.graphBits G))).filter
      (fun ef => q ef.1 && q ef.2)).length =
      ((crossingPairs G).filter (fun ef => ef.1 ∈ M ∧ ef.2 ∈ M)).card := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  unfold crossPairs
  rw [List.filter_filter]
  have hnd := (product_nodup E (encEdges_nodup _)).filter (fun ef => (q ef.1 && q ef.2) &&
    (decide (ef.1.1 < ef.2.1) && decide (ef.2.1 < ef.1.2) && decide (ef.1.2 < ef.2.2)))
  rw [← List.toFinset_card_of_nodup hnd]
  rw [← Finset.card_image_of_injective _ (f := fun ef : G.edgeSet × G.edgeSet => (toPair ef.1, toPair ef.2))
    (by intro a b h; simp only [Prod.mk.injEq] at h; exact Prod.ext (toPair_injective h.1) (toPair_injective h.2))]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, List.mem_flatMap, List.mem_map, Finset.mem_image,
    Finset.mem_filter, crossingPairs, Finset.mem_univ, true_and, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, ⟨hqa, hqb⟩, hc⟩
    obtain ⟨e, heM, rfl⟩ := (hq a ha).1 hqa
    obtain ⟨f, hfM, rfl⟩ := (hq b hb).1 hqb
    refine ⟨(e, f), ⟨(crossCond_iff e f).1 ?_, heM, hfM⟩, rfl⟩
    simpa only [Bool.and_eq_true] using hc
  · rintro ⟨⟨e, f⟩, ⟨hc, he, hf⟩, rfl⟩
    have hmem := fun g : G.edgeSet => (mem_encEdges_graphBits (G := G) (toPair g)).2 ⟨g, rfl⟩
    refine ⟨⟨toPair e, hmem e, toPair f, hmem f, rfl⟩,
      ⟨(hq _ (hmem e)).2 ⟨e, he, rfl⟩, (hq _ (hmem f)).2 ⟨f, hf, rfl⟩⟩, ?_⟩
    simpa only [Bool.and_eq_true] using (crossCond_iff e f).2 hc

end SA

open SA

open Classical in
/-- (A) The value computed by `qVal` is the wrong-sign sum at the weights `β`. -/
theorem qVal_decode (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (β : List (List Bool)) (hβ : β.length = (encEdges (CatalyticMatching.General.graphBits G)).length) :
    gfDecode m (qVal m N (encEdges (CatalyticMatching.General.graphBits G)) d s β) =
      ∑ M ∈ (MulmuleyVV.Matching.perfectMatchings G).filter (fun M => Viol d s M),
        ∏ e ∈ M, wt m β e ^ 2 := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  have hmemE : ∀ g : G.edgeSet, toPair g ∈ E := fun g => (mem_encEdges_graphBits _).2 ⟨g, rfl⟩
  set q : Finset G.edgeSet → ℕ × ℕ → Bool :=
    fun M p => decide (∀ g : G.edgeSet, toPair g = p → g ∈ M) with hqdef
  have hq : ∀ M, ∀ p ∈ E, q M p = true ↔ ∃ e ∈ M, toPair e = p := by
    intro M p hp
    simp only [q, decide_eq_true_eq]
    obtain ⟨e, rfl⟩ := (mem_encEdges_graphBits p).1 hp
    constructor
    · intro h; exact ⟨e, h e rfl, rfl⟩
    · rintro ⟨e', he', h'⟩ g hg
      rw [toPair_injective (hg.trans h'.symm)]; exact he'
  set P : Finset G.edgeSet → GF m := fun M => ∏ e ∈ M, wt m β e ^ 2 with hP
  have h0 : gfDecode m (if s then phiVal m N E β else gfZero m) =
      ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G, (((if s then 1 else 0 : ℕ)) : GF m) * P M := by
    cases s
    · simp [gfDecode_zero]
    · simpa [P] using phi_decode m β hβ
  have h1 : ((((E.zip d).filter (fun ed => ed.2)).map
      (fun ed => phiVal m N E (kill m E [ed.1] β))).map (gfDecode m)).sum =
      ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G, (markCount d M : GF m) * P M := by
    rw [List.map_map]
    rw [List.map_congr_left (g := fun ed => ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G,
      if (∀ e : G.edgeSet, toPair e ∈ [ed.1] → e ∈ M) then P M else 0)]
    · rw [sum_swap]
      refine Finset.sum_congr rfl (fun M _ => ?_)
      congr 2
      rw [List.filter_filter, ← mark_count d M (q M) (hq M)]
      congr 1
      apply List.filter_congr
      intro x _
      simp [q, Bool.and_comm]
    · intro ed hed
      simp only [Function.comp]
      apply phi_kill_decode m [ed.1] β hβ
      · intro p hp
        rw [List.mem_singleton] at hp; subst hp
        exact (List.of_mem_zip (List.mem_filter.1 hed).1).1
      · intro p hp r hr _
        rw [List.mem_singleton] at hp hr; rw [hp, hr]
  have h2 : (((crossPairs E).map
      (fun ef => phiVal m N E (kill m E [ef.1, ef.2] β))).map (gfDecode m)).sum =
      ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G,
        (((crossingPairs G).filter (fun ef => ef.1 ∈ M ∧ ef.2 ∈ M)).card : GF m) * P M := by
    rw [List.map_map]
    rw [List.map_congr_left (g := fun ef => ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G,
      if (∀ e : G.edgeSet, toPair e ∈ [ef.1, ef.2] → e ∈ M) then P M else 0)]
    · rw [sum_swap]
      refine Finset.sum_congr rfl (fun M _ => ?_)
      congr 2
      rw [← cross_count M (q M) (hq M)]
      congr 1
      apply List.filter_congr
      intro x _
      simp only [q, List.mem_cons, List.not_mem_nil, or_false]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq, Bool.and_eq_true]
      constructor
      · intro h; exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩
      · rintro ⟨h1, h2⟩ g (hg | hg)
        · exact h1 g hg
        · exact h2 g hg
    · intro ef hef
      simp only [Function.comp]
      unfold crossPairs at hef
      simp only [List.mem_filter, List.mem_flatMap, List.mem_map, Bool.and_eq_true,
        decide_eq_true_eq] at hef
      obtain ⟨⟨a, ha, b, hb, rfl⟩, ⟨h12, h23⟩, h34⟩ := hef
      obtain ⟨ea, rfl⟩ := (mem_encEdges_graphBits _).1 ha
      obtain ⟨eb, rfl⟩ := (mem_encEdges_graphBits _).1 hb
      have hla := toPair_lt ea
      have hlb := toPair_lt eb
      apply phi_kill_decode m _ β hβ
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact ha
        · exact hb
      · intro p hp r hr hsh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hr
        simp only at h12 h23 h34
        unfold share at hsh
        rcases hp with rfl | rfl <;> rcases hr with rfl | rfl
        · rfl
        · exfalso; omega
        · exfalso; omega
        · rfl
  unfold qVal
  rw [listSum_map (gfOps m) (stdOps (GF m)) (gfDecode m) (gfDecode_zero m) (gfDecode_add m),
    listSum_stdOps, List.map_append, List.map_append, List.sum_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, h0, h1, h2,
    Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  rw [← add_mul, ← add_mul]
  have hcast : (((if s then 1 else 0 : ℕ)) : GF m) + (markCount d M : GF m) +
      (((crossingPairs G).filter (fun ef => ef.1 ∈ M ∧ ef.2 ∈ M)).card : GF m) =
      ((((crossingPairs G).filter (fun ef => ef.1 ∈ M ∧ ef.2 ∈ M)).card + markCount d M +
        (if s then 1 else 0) : ℕ) : GF m) := by
    push_cast; ring
  rw [hcast, ← gf_parity]
  apply if_congr _ rfl rfl
  have hc : crossingParity M =
      ((crossingPairs G).filter (fun ef => ef.1 ∈ M ∧ ef.2 ∈ M)).card % 2 := by
    unfold crossingParity; congr
  simp only [Viol, hc, beq_iff_eq]
  omega

namespace SA

/-! ### Greedy search -/

theorem share_symm {p q : ℕ × ℕ} (h : share p q) : share q p := by
  unfold share at *; omega

theorem pairwise_eq {S : List (ℕ × ℕ)} (h : S.Pairwise (fun p q => ¬ share p q)) :
    ∀ p ∈ S, ∀ q ∈ S, share p q → p = q := by
  induction S with
  | nil => simp
  | cons a S ih =>
    rw [List.pairwise_cons] at h
    intro p hp q hq hpq
    simp only [List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exact absurd hpq (h.1 q hq)
    · exact absurd (share_symm hpq) (h.1 p hp)
    · exact ih h.2 p hp q hq hpq

/-- Invariant on partial matchings: edges of `E`, pairwise vertex-disjoint. -/
def Inv (E S : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, p ∈ E) ∧ S.Pairwise (fun p q => ¬ share p q)

open Classical in
/-- The wrong-sign sum restricted to perfect matchings containing `S`. -/
noncomputable def W {N : ℕ} (G : SimpleGraph (Fin N)) (m : ℕ) (d : List Bool) (s : Bool)
    (α : List (List Bool)) (S : List (ℕ × ℕ)) : GF m :=
  ∑ M ∈ (MulmuleyVV.Matching.perfectMatchings G).filter (fun M => Viol d s M),
    if (∀ e : G.edgeSet, toPair e ∈ S → e ∈ M) then ∏ e ∈ M, wt m α e ^ 2 else 0

open Classical in
theorem mem_pm {M : Finset G.edgeSet} {d : List Bool} {s : Bool}
    (hM : M ∈ (MulmuleyVV.Matching.perfectMatchings G).filter (fun M => Viol d s M)) :
    MulmuleyVV.Matching.IsPerfectMatchingEdges G M ∧ Viol d s M := by
  classical
  rw [Finset.mem_filter] at hM
  unfold MulmuleyVV.Matching.perfectMatchings at hM
  exact ⟨(Finset.mem_filter.1 hM.1).2, hM.2⟩

theorem V_eq (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (α : List (List Bool)) (hα : α.length = (encEdges (CatalyticMatching.General.graphBits G)).length)
    (S : List (ℕ × ℕ)) (hS : Inv (encEdges (CatalyticMatching.General.graphBits G)) S) :
    gfDecode m (qVal m N (encEdges (CatalyticMatching.General.graphBits G)) d s
      (kill m (encEdges (CatalyticMatching.General.graphBits G)) S α)) = W G m d s α S := by
  classical
  rw [qVal_decode m d s _ (kill_length _ _ _ _ hα), W]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  exact prod_kill m S α hα hS.1 (pairwise_eq hS.2) M (mem_pm hM).1

theorem W_nil (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (α : List (List Bool)) (hα : α.length = (encEdges (CatalyticMatching.General.graphBits G)).length) :
    W G m d s α [] = gfDecode m (qVal m N (encEdges (CatalyticMatching.General.graphBits G)) d s α) := by
  classical
  rw [qVal_decode m d s _ hα, W]
  simp

/-- Smallest vertex not covered by `S`. -/
def vtx (N : ℕ) (S : List (ℕ × ℕ)) : ℕ := (List.range N).findIdx (fun u => !touches S (u, u))

/-- Candidate edges at `v`, disjoint from `S`. -/
def cands (E S : List (ℕ × ℕ)) (v : ℕ) : List (ℕ × ℕ) :=
  E.filter (fun e => (e.1 == v || e.2 == v) && !touches S e)

theorem searchStep_eq (m N : ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool)
    (α : List (List Bool)) (S : List (ℕ × ℕ)) :
    searchStep m N E d s α S =
      if (cands E S (vtx N S)).findIdx
          (fun e => !gfIsZero m (qVal m N E d s (kill m E (S ++ [e]) α))) <
          (cands E S (vtx N S)).length then
        S ++ [(cands E S (vtx N S)).getD ((cands E S (vtx N S)).findIdx
          (fun e => !gfIsZero m (qVal m N E d s (kill m E (S ++ [e]) α)))) (0, 0)]
      else S := rfl

theorem inv_append {E S : List (ℕ × ℕ)} (hS : Inv E S) {e : ℕ × ℕ} (he : e ∈ E)
    (ht : touches S e = false) : Inv E (S ++ [e]) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hS.1 p hp
    · exact he
  · rw [List.pairwise_append]
    refine ⟨hS.2, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb; subst hb
    have : touches S b = true := (touches_iff S b).2 ⟨a, ha, hab⟩
    rw [ht] at this; exact Bool.noConfusion this

theorem mem_cands {E S : List (ℕ × ℕ)} {v : ℕ} {e : ℕ × ℕ} :
    e ∈ cands E S v ↔ e ∈ E ∧ (e.1 = v ∨ e.2 = v) ∧ touches S e = false := by
  simp [cands, List.mem_filter]

theorem step_inv (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (α : List (List Bool)) (hα : α.length = (encEdges (CatalyticMatching.General.graphBits G)).length)
    (S : List (ℕ × ℕ)) (hS : Inv (encEdges (CatalyticMatching.General.graphBits G)) S)
    (hW : W G m d s α S ≠ 0) :
    (searchStep m N (encEdges (CatalyticMatching.General.graphBits G)) d s α S = S ∨
      ∃ e, searchStep m N (encEdges (CatalyticMatching.General.graphBits G)) d s α S = S ++ [e] ∧
        (e.1 = vtx N S ∨ e.2 = vtx N S)) ∧
    Inv (encEdges (CatalyticMatching.General.graphBits G))
      (searchStep m N (encEdges (CatalyticMatching.General.graphBits G)) d s α S) ∧
    W G m d s α (searchStep m N (encEdges (CatalyticMatching.General.graphBits G)) d s α S) ≠ 0 := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  rw [searchStep_eq]
  split_ifs with hk
  · set C := cands E S (vtx N S)
    set k := C.findIdx (fun e => !gfIsZero m (qVal m N E d s (kill m E (S ++ [e]) α)))
    rw [List.getD_eq_getElem _ _ hk]
    have hpr := List.findIdx_getElem (w := hk)
    have hmem := (mem_cands.1 (List.getElem_mem hk))
    have hinv := inv_append hS hmem.1 hmem.2.2
    refine ⟨Or.inr ⟨_, rfl, hmem.2.1⟩, hinv, ?_⟩
    rw [← V_eq m d s α hα _ hinv, Ne, ← gfIsZero_iff]
    simpa using hpr
  · exact ⟨Or.inl rfl, hS, hW⟩

theorem filter_length_one {α : Type} (l : List α) (p : α → Bool) (hl : l.Nodup) (a : α)
    (ha : a ∈ l) (hpa : p a = true) (huniq : ∀ b ∈ l, p b = true → b = a) :
    (l.filter p).length = 1 := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [List.filter_cons]
    by_cases hxa : x = a
    · subst hxa
      rw [if_pos hpa, List.length_cons]
      have : l.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hpb
        exact hl.1 (huniq b (List.mem_cons_of_mem _ hb) hpb ▸ hb)
      rw [this]; rfl
    · have hpx : p x = false := by
        cases h : p x
        · rfl
        · exact absurd (huniq x List.mem_cons_self h) hxa
      rw [hpx]
      simp only [Bool.false_eq_true, if_false]
      exact ih hl.2 (by simpa [Ne.symm hxa] using ha)
        (fun b hb hpb => huniq b (List.mem_cons_of_mem _ hb) hpb)

theorem W_decomp (m : ℕ) (d : List Bool) (s : Bool) (α : List (List Bool))
    (S : List (ℕ × ℕ)) (hS : Inv (encEdges (CatalyticMatching.General.graphBits G)) S)
    (hv : vtx N S < N) (hvt : touches S (vtx N S, vtx N S) = false) :
    W G m d s α S = ((cands (encEdges (CatalyticMatching.General.graphBits G)) S (vtx N S)).map
      (fun e => W G m d s α (S ++ [e]))).sum := by
  classical
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  set C := cands E S (vtx N S) with hC
  unfold W
  rw [sum_swap]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  obtain ⟨hPM, -⟩ := mem_pm hM
  by_cases hc : ∀ e : G.edgeSet, toPair e ∈ S → e ∈ M
  · rw [if_pos hc]
    obtain ⟨g, ⟨hgM, hvg⟩, -⟩ := hPM ⟨vtx N S, hv⟩
    have hlen : (C.filter (fun x => decide (∀ e : G.edgeSet, toPair e ∈ S ++ [x] → e ∈ M))).length
        = 1 := by
      apply filter_length_one C _ ((encEdges_nodup _).filter _) (toPair g)
      · rw [mem_cands]
        refine ⟨(mem_encEdges_graphBits _).2 ⟨g, rfl⟩, ?_, ?_⟩
        · rcases (mem_edge_iff g _).1 hvg with h | h
          · left; simp [toPair, ← h]
          · right; simp [toPair, ← h]
        · cases ht : touches S (toPair g)
          · rfl
          · exfalso
            obtain ⟨f, hf, hsh⟩ := (touches_iff S _).1 ht
            obtain ⟨f', rfl⟩ := (mem_encEdges_graphBits f).1 (hS.1 f hf)
            obtain ⟨w, hw1, hw2⟩ := (share_toPair f' g).1 hsh
            have hfg := pm_eq_of_mem hPM (hc f' hf) hgM w hw1 hw2
            subst hfg
            have : touches S (vtx N S, vtx N S) = true := by
              refine (touches_iff S _).2 ⟨_, hf, ?_⟩
              rcases (mem_edge_iff f' _).1 hvg with h | h
              · left; simp [toPair, ← h]
              · right; simp [toPair, ← h]
            rw [hvt] at this; exact Bool.noConfusion this
      · simp only [decide_eq_true_eq, List.mem_append, List.mem_singleton]
        rintro e (he | he)
        · exact hc e he
        · rw [toPair_injective he]; exact hgM
      · intro b hb hpb
        simp only [decide_eq_true_eq, List.mem_append, List.mem_singleton] at hpb
        obtain ⟨hbE, hbv, -⟩ := mem_cands.1 hb
        obtain ⟨b', rfl⟩ := (mem_encEdges_graphBits b).1 hbE
        have hb'M := hpb b' (Or.inr rfl)
        have hvb' : (⟨vtx N S, hv⟩ : Fin N) ∈ (b' : Sym2 (Fin N)) := by
          rw [mem_edge_iff]
          rcases hbv with h | h
          · left; exact Fin.ext h.symm
          · right; exact Fin.ext h.symm
        rw [pm_eq_of_mem hPM hb'M hgM _ hvb' hvg]
    rw [hlen]; simp
  · rw [if_neg hc]
    have : C.filter (fun x => decide (∀ e : G.edgeSet, toPair e ∈ S ++ [x] → e ∈ M)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x _ hx
      simp only [decide_eq_true_eq] at hx
      exact hc (fun e he => hx e (List.mem_append_left _ he))
    rw [this]; simp

theorem vtx_spec (S : List (ℕ × ℕ)) (h : ∃ u < N, touches S (u, u) = false) :
    vtx N S < N ∧ touches S (vtx N S, vtx N S) = false := by
  have hlt : vtx N S < (List.range N).length := by
    unfold vtx
    apply List.findIdx_lt_length_of_exists
    obtain ⟨u, hu, ht⟩ := h
    exact ⟨u, List.mem_range.2 hu, by simp [ht]⟩
  refine ⟨by simpa using hlt, ?_⟩
  have := List.findIdx_getElem (w := hlt)
  change (!touches S ((List.range N)[vtx N S]'hlt, (List.range N)[vtx N S]'hlt)) = true at this
  rw [List.getElem_range] at this
  simpa using this

theorem step_progress (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (α : List (List Bool)) (hα : α.length = (encEdges (CatalyticMatching.General.graphBits G)).length)
    (S : List (ℕ × ℕ)) (hS : Inv (encEdges (CatalyticMatching.General.graphBits G)) S)
    (hW : W G m d s α S ≠ 0) (hunc : ∃ u < N, touches S (u, u) = false) :
    searchStep m N (encEdges (CatalyticMatching.General.graphBits G)) d s α S ≠ S := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  obtain ⟨hv, hvt⟩ := vtx_spec S hunc
  rw [W_decomp m d s α S hS hv hvt] at hW
  obtain ⟨x, hx, hx0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hW
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  have hmem := mem_cands.1 he
  have hinv := inv_append hS hmem.1 hmem.2.2
  rw [searchStep_eq, if_pos]
  · intro h
    have := congrArg List.length h
    simp at this
  · apply List.findIdx_lt_length_of_exists
    refine ⟨e, he, ?_⟩
    rw [← V_eq m d s α hα _ hinv, Ne, ← gfIsZero_iff] at hx0
    simpa using hx0

theorem filter_length_lt {α : Type} (l : List α) (p q : α → Bool) (hpq : ∀ x ∈ l, p x = true → q x = true)
    (x : α) (hx : x ∈ l) (hqx : q x = true) (hpx : p x = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    have hpq' : ∀ x ∈ l, p x = true → q x = true := fun x hx => hpq x (List.mem_cons_of_mem _ hx)
    have hle : (l.filter p).length ≤ (l.filter q).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact List.countP_mono_left (fun x hx h => hpq' x hx h)
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [hqx, hpx]; omega
    · have := ih hpq' hx
      cases hpy : p y <;> cases hqy : q y <;> simp [hpy, hqy] <;> try omega
      exact absurd (hpq y List.mem_cons_self hpy) (by simp [hqy])

/-- Number of covered vertices. -/
def cov (N : ℕ) (S : List (ℕ × ℕ)) : ℕ := ((List.range N).filter (fun u => touches S (u, u))).length

theorem touches_append (S T : List (ℕ × ℕ)) (x : ℕ × ℕ) (h : touches S x = true) :
    touches (S ++ T) x = true := by
  unfold touches at *; rw [List.any_append, h]; rfl

theorem iter (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (α : List (List Bool)) (hα : α.length = (encEdges (CatalyticMatching.General.graphBits G)).length)
    (h0 : W G m d s α [] ≠ 0) (k : ℕ) :
    Inv (encEdges (CatalyticMatching.General.graphBits G))
        ((searchStep m N (encEdges (CatalyticMatching.General.graphBits G)) d s α)^[k] []) ∧
      W G m d s α ((searchStep m N (encEdges (CatalyticMatching.General.graphBits G)) d s α)^[k] [])
        ≠ 0 ∧
      ((∀ u < N, touches ((searchStep m N (encEdges (CatalyticMatching.General.graphBits G))
          d s α)^[k] []) (u, u) = true) ∨
        k ≤ cov N ((searchStep m N (encEdges (CatalyticMatching.General.graphBits G)) d s α)^[k] [])) := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  induction k with
  | zero => exact ⟨⟨by simp, List.Pairwise.nil⟩, h0, Or.inr (Nat.zero_le _)⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set S := (searchStep m N E d s α)^[k] [] with hSdef
    obtain ⟨hS, hW, hcov⟩ := ih
    obtain ⟨hshape, hS', hW'⟩ := step_inv m d s α hα S hS hW
    refine ⟨hS', hW', ?_⟩
    by_cases hall : ∀ u < N, touches S (u, u) = true
    · left
      intro u hu
      rcases hshape with h | ⟨e, h, -⟩
      · rw [h]; exact hall u hu
      · rw [h]; exact touches_append _ _ _ (hall u hu)
    · right
      have hunc : ∃ u < N, touches S (u, u) = false := by
        push Not at hall
        obtain ⟨u, hu, ht⟩ := hall
        exact ⟨u, hu, by simpa using ht⟩
      have hk : k ≤ cov N S := by
        rcases hcov with h | h
        · exact absurd h hall
        · exact h
      obtain ⟨hv, hvt⟩ := vtx_spec S hunc
      have hne := step_progress m d s α hα S hS hW hunc
      rcases hshape with h | ⟨e, h, he⟩
      · exact absurd h hne
      · rw [h]
        have : cov N S < cov N (S ++ [e]) := by
          unfold cov
          apply filter_length_lt _ _ _ (fun x _ hx => touches_append _ _ _ hx) (vtx N S)
            (List.mem_range.2 hv)
          · refine (touches_iff _ _).2 ⟨e, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
            unfold share; simp only; omega
          · exact hvt
        omega

theorem len_one (L : List (ℕ × ℕ)) (hL : L.Pairwise (fun p q => ¬ share p q)) (v : ℕ)
    (hv : ∀ f ∈ L, f.1 = v ∨ f.2 = v) (f₀ : ℕ × ℕ) (hf₀ : f₀ ∈ L) : L.length = 1 := by
  match L, hL, hv, hf₀ with
  | [], _, _, h => simp at h
  | [_], _, _, _ => rfl
  | a :: b :: t, hL, hv, _ =>
    exfalso
    rw [List.pairwise_cons] at hL
    have h1 := hL.1 b (List.mem_cons_self ..)
    have ha := hv a (List.mem_cons_self ..)
    have hb := hv b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    apply h1
    unfold share; omega

theorem sa_crossCount_mod (S : List (ℕ × ℕ))
    (h : isPMList N (encEdges (CatalyticMatching.General.graphBits G)) S = true) :
    crossCount S % 2 = crossingParity (pmSet (G := G) S) := by
  classical
  obtain ⟨-, hnd, himg⟩ := isPMList_spec S h
  rw [crossCount_eq S hnd himg]
  unfold crossingParity
  congr 2

end SA

/-- (B) If `Q(α) ≠ 0`, the greedy search returns a perfect matching inconsistent with `(d, s)`. -/
theorem greedy_correct (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (α : List (List Bool)) (hα : α.length = (encEdges (CatalyticMatching.General.graphBits G)).length)
    (hd : d.length = (encEdges (CatalyticMatching.General.graphBits G)).length)
    (hQ : gfIsZero m (qVal m N (encEdges (CatalyticMatching.General.graphBits G)) d s α) = false) :
    isPMList N (encEdges (CatalyticMatching.General.graphBits G))
        (greedySearch m N (encEdges (CatalyticMatching.General.graphBits G)) d s α) = true ∧
      violates (encEdges (CatalyticMatching.General.graphBits G)) d s
        (greedySearch m N (encEdges (CatalyticMatching.General.graphBits G)) d s α) = true := by
  classical
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  have h0 : W G m d s α [] ≠ 0 := by
    rw [W_nil m d s α hα, Ne, ← gfIsZero_iff, hQ]; simp
  have hgs : greedySearch m N E d s α = (searchStep m N E d s α)^[N] [] := by
    unfold greedySearch; rw [foldl_range_iterate]
  rw [hgs]
  set S := (searchStep m N E d s α)^[N] [] with hSdef
  obtain ⟨hS, hW, hcov⟩ : Inv E S ∧ W G m d s α S ≠ 0 ∧
      ((∀ u < N, touches S (u, u) = true) ∨ N ≤ cov N S) := iter m d s α hα h0 N
  have hall : ∀ u < N, touches S (u, u) = true := by
    rcases hcov with h | h
    · exact h
    · by_contra hc
      push Not at hc
      obtain ⟨u, hu, ht⟩ := hc
      have : cov N S < N := by
        have := List.length_filter_lt_length_iff_exists.2
          (⟨u, List.mem_range.2 hu, ht⟩ : ∃ x ∈ List.range N, ¬ touches S (x, x) = true)
        simpa [cov] using this
      omega
  have hpmL : isPMList N E S = true := by
    unfold isPMList
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨?_, fun f hf => by simpa using hS.1 f hf⟩
    intro v hv
    rw [List.mem_range] at hv
    obtain ⟨f, hf, hsh⟩ := (touches_iff S _).1 (hall v hv)
    rw [beq_iff_eq]
    apply len_one _ (hS.2.filter _) v
    · intro g hg
      simpa using (List.mem_filter.1 hg).2
    · exact List.mem_filter.2 ⟨hf, by unfold share at hsh; simp only at hsh; simp; omega⟩
  refine ⟨hpmL, ?_⟩
  obtain ⟨hpmS, -, -⟩ := isPMList_spec S hpmL
  have hV : Viol d s (pmSet (G := G) S) := by
    by_contra hV
    apply hW
    unfold W
    apply Finset.sum_eq_zero
    intro M hM
    obtain ⟨hPM, hVM⟩ := mem_pm hM
    rw [if_neg]
    intro hc
    apply hV
    have hMS : M = pmSet S := by
      ext e
      constructor
      · intro he
        obtain ⟨f, ⟨hf, hvf⟩, -⟩ := hpmS (edgeLo e)
        have hfM := hc f ((mem_pmSet S f).1 hf)
        rw [pm_eq_of_mem hPM he hfM (edgeLo e) ((mem_edge_iff e _).2 (Or.inl rfl)) hvf]
        exact hf
      · intro he; exact hc e ((mem_pmSet S e).1 he)
    rw [← hMS]; exact hVM
  have hdc : dCount E d S = markCount d (pmSet (G := G) S) := by
    unfold dCount
    apply mark_count d (pmSet S) (fun p => S.contains p)
    intro p hp
    simp only [List.contains_iff_mem]
    constructor
    · intro hpS
      obtain ⟨e, rfl⟩ := (mem_encEdges_graphBits p).1 hp
      exact ⟨e, (mem_pmSet S e).2 hpS, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact (mem_pmSet S e).1 he
  have hcc := sa_crossCount_mod S hpmL
  unfold violates
  rw [beq_iff_eq, hdc]
  unfold Viol at hV
  omega

end PfaffianRecognition.CoRP

end

-- ===== from Solutions/Main/SoundC.lean =====
section

namespace PfaffianRecognition.CoRP
open PfaffianRecognition.Recognition

variable {N : ℕ} {G : SimpleGraph (Fin N)}



namespace SC

/-- The edge-index map into the variable type. -/
noncomputable def eVar (e : G.edgeSet) : Fin (encEdges (CatalyticMatching.General.graphBits G)).length :=
  ⟨eIdx e, eIdx_lt e⟩

theorem eVar_injective : Function.Injective (eVar (G := G)) := by
  intro e f h
  apply toPair_injective
  have h' : eIdx e = eIdx f := congrArg Fin.val h
  rw [← getElem_eIdx e, ← getElem_eIdx f]
  simp only [h']

theorem sum_monomials_ne_zero (K : Type*) [CommRing K] [Nontrivial K] {σ : Type*}
    (T : Finset (Finset σ)) (M₀ : Finset σ) (hM₀ : M₀ ∈ T) :
    ∑ M ∈ T, ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial σ K) ^ 2 ≠ 0 := by
  classical
  intro h
  have hmon : ∀ M : Finset σ, ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial σ K) ^ 2 =
      MvPolynomial.monomial (∑ e ∈ M, Finsupp.single e 2) 1 := by
    intro M
    rw [MvPolynomial.monomial_sum_one]
    simp [MvPolynomial.X_pow_eq_monomial]
  have happ : ∀ (M : Finset σ) (x : σ), (∑ e ∈ M, Finsupp.single e 2) x = if x ∈ M then 2 else 0 := by
    intro M x
    rw [Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  have hinj : ∀ M : Finset σ, (∑ e ∈ M, Finsupp.single e 2) = (∑ e ∈ M₀, Finsupp.single e 2) ↔
      M = M₀ := by
    intro M
    constructor
    · intro hM
      ext x
      have := congrArg (fun m => m x) hM
      simp only [happ] at this
      by_cases h1 : x ∈ M <;> by_cases h2 : x ∈ M₀ <;> simp_all
    · rintro rfl; rfl
  have := congrArg (MvPolynomial.coeff (∑ e ∈ M₀, Finsupp.single e 2)) h
  simp only [MvPolynomial.coeff_sum, hmon, MvPolynomial.coeff_monomial, hinj,
    MvPolynomial.coeff_zero] at this
  rw [Finset.sum_ite_eq' T M₀ (fun _ => (1 : K)), if_pos hM₀] at this
  exact one_ne_zero this

/-- A perfect matching has exactly `N / 2` edges: `2 |M| = N`. -/
theorem two_mul_card (M : Finset G.edgeSet) (hM : MulmuleyVV.Matching.IsPerfectMatchingEdges G M) :
    M.card * 2 = N := by
  classical
  have h1 : ∀ v : Fin N, (M.filter (fun e : G.edgeSet => v ∈ e.val)).card = 1 := by
    intro v
    obtain ⟨e, ⟨he, hv⟩, huniq⟩ := hM v
    rw [Finset.card_eq_one]
    refine ⟨e, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun hf => huniq f hf, fun hf => hf ▸ ⟨he, hv⟩⟩
  have h2 : ∀ e : G.edgeSet, (Finset.univ.filter (fun v : Fin N => v ∈ (e : Sym2 (Fin N)))).card = 2 := by
    intro e
    have : Finset.univ.filter (fun v : Fin N => v ∈ (e : Sym2 (Fin N))) = {edgeLo e, edgeHi e} := by
      ext v; simp [mem_edge_iff]
    rw [this, Finset.card_pair (edgeLo_lt_edgeHi e).ne]
  calc M.card * 2 = ∑ e ∈ M, (Finset.univ.filter (fun v : Fin N => v ∈ (e : Sym2 (Fin N)))).card := by
        rw [Finset.sum_congr rfl (fun e _ => h2 e)]; simp
    _ = ∑ v : Fin N, (M.filter (fun e : G.edgeSet => v ∈ e.val)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ = N := by rw [Finset.sum_congr rfl (fun v _ => h1 v)]; simp

/-- The orientation determined by the marks `d`: edge `{i,j}`, `i < j`, goes `j → i` iff marked. -/
def orientRel (d : List Bool) (u v : Fin N) : Prop :=
  ∃ h : G.Adj u v, (d.getD (eIdx (⟨s(u, v), G.mem_edgeSet.2 h⟩ : G.edgeSet)) false = true ↔ v < u)

theorem orientRel_isOrientation (d : List Bool) :
    SparseDisc.IsOrientation G (orientRel (G := G) d) := by
  refine ⟨fun u v h => h.1, fun u v huv => ?_⟩
  have hsw : (⟨s(v, u), G.mem_edgeSet.2 huv.symm⟩ : G.edgeSet) = ⟨s(u, v), G.mem_edgeSet.2 huv⟩ :=
    Subtype.ext Sym2.eq_swap
  have hne : u ≠ v := G.ne_of_adj huv
  have e1 : orientRel d u v ↔
      (d.getD (eIdx (⟨s(u, v), G.mem_edgeSet.2 huv⟩ : G.edgeSet)) false = true ↔ v < u) :=
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨huv, h⟩⟩
  have e2 : orientRel d v u ↔
      (d.getD (eIdx (⟨s(u, v), G.mem_edgeSet.2 huv⟩ : G.edgeSet)) false = true ↔ u < v) :=
    ⟨fun ⟨_, h⟩ => by rwa [hsw] at h, fun h => ⟨huv.symm, by rwa [hsw]⟩⟩
  rw [e1, e2]
  generalize d.getD (eIdx (⟨s(u, v), G.mem_edgeSet.2 huv⟩ : G.edgeSet)) false = b
  rcases lt_or_gt_of_ne hne with h | h
  · cases b <;> simp [h, h.not_gt]
  · cases b <;> simp [h, h.not_gt]

/-- The orientation `D_d`. -/
def orient (d : List Bool) : Orientation G := ⟨orientRel d, orientRel_isOrientation d⟩

theorem backward_iff (d : List Bool) (e : G.edgeSet) :
    (orient (G := G) d).val (edgeHi e) (edgeLo e) ↔ d.getD (eIdx e) false = true := by
  have hlt := edgeLo_lt_edgeHi e
  have he : (⟨s(edgeHi e, edgeLo e), G.mem_edgeSet.2 (edge_adj e).symm⟩ : G.edgeSet) = e :=
    Subtype.ext (by
      show s(edgeHi e, edgeLo e) = e.val
      rw [Sym2.eq_swap]; exact (edge_eq_lo_hi e).symm)
  show orientRel d (edgeHi e) (edgeLo e) ↔ _
  unfold orientRel
  simp only [he, hlt, iff_true]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(edge_adj e).symm, h⟩⟩

theorem backwardParity_orient (d : List Bool) (M : Finset G.edgeSet) :
    backwardParity (orient (G := G) d) M = markCount d M % 2 := by
  classical
  unfold backwardParity markCount
  congr 2
  ext e
  simp [backwardEdges, backward_iff]

end SC

open SC

/-- (C) A non-Pfaffian graph has, for every `(d, s)`, an inconsistent perfect matching. -/
theorem exists_viol_of_not_pfaffian (hG : ¬ IsPfaffianGraph G) (d : List Bool) (s : Bool) :
    ∃ M : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G M ∧ Viol d s M := by
  by_contra hcon
  push Not at hcon
  apply hG
  refine ⟨orient d, ?_⟩
  have key : ∀ M, MulmuleyVV.Matching.IsPerfectMatchingEdges G M →
      matchingSign (orient (G := G) d) M = (-1 : ℤ) ^ (if s then 1 else 0) := by
    intro M hM
    rw [matching_sign_parity G _ M hM, backwardParity_orient, neg_one_pow_eq_pow_mod_two,
      neg_one_pow_eq_pow_mod_two (n := if s then 1 else 0)]
    have hv := hcon M hM
    unfold Viol at hv
    have hs : (if s then 1 else 0) ≤ 1 := by split_ifs <;> omega
    congr 1
    omega
  intro M₁ M₂ h1 h2
  rw [key M₁ h1, key M₂ h2]

open Classical in
/-- The wrong-sign polynomial in the edge-position variables. -/
noncomputable def violPoly (m : ℕ) (d : List Bool) (s : Bool) :
    MvPolynomial (Fin (encEdges (CatalyticMatching.General.graphBits G)).length) (GF m) :=
  ∑ M ∈ (MulmuleyVV.Matching.perfectMatchings G).filter (fun M => Viol d s M),
    ∏ e ∈ M, (MvPolynomial.X ⟨eIdx e, eIdx_lt e⟩) ^ 2

theorem violPoly_ne_zero (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (h : ∃ M : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G M ∧ Viol d s M) :
    violPoly (G := G) m d s ≠ 0 := by
  classical
  obtain ⟨M₀, hM₀, hv⟩ := h
  have hren : violPoly (G := G) m d s = MvPolynomial.rename (eVar (G := G))
      (∑ M ∈ (MulmuleyVV.Matching.perfectMatchings G).filter (fun M => Viol d s M),
        ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial G.edgeSet (GF m)) ^ 2) := by
    unfold violPoly
    simp only [map_sum, map_prod, map_pow, MvPolynomial.rename_X]
    rfl
  rw [hren]
  intro h0
  have h0' := (map_eq_zero_iff _ (MvPolynomial.rename_injective _ (eVar_injective (G := G)))).1 h0
  refine sum_monomials_ne_zero (GF m) _ M₀ ?_ h0'
  rw [Finset.mem_filter]
  refine ⟨?_, hv⟩
  unfold MulmuleyVV.Matching.perfectMatchings
  simpa using hM₀

theorem violPoly_totalDegree (m : ℕ) (d : List Bool) (s : Bool) :
    (violPoly (G := G) m d s).totalDegree ≤ N := by
  classical
  unfold violPoly
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun M hM => ?_)
  have hpm : MulmuleyVV.Matching.IsPerfectMatchingEdges G M := by
    have := (Finset.mem_filter.1 hM).1
    unfold MulmuleyVV.Matching.perfectMatchings at this
    simpa using this
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ e ∈ M, ((MvPolynomial.X ⟨eIdx e, eIdx_lt e⟩ :
          MvPolynomial (Fin (encEdges (CatalyticMatching.General.graphBits G)).length) (GF m)) ^ 2).totalDegree
      ≤ ∑ e ∈ M, 2 := Finset.sum_le_sum fun e _ => by
        rcases subsingleton_or_nontrivial (GF m) with hs | hs
        · simp [Subsingleton.elim (_ : MvPolynomial _ (GF m)) 0]
        · rw [MvPolynomial.totalDegree_X_pow]
    _ = N := by rw [Finset.sum_const, smul_eq_mul]; exact two_mul_card M hpm

theorem violPoly_eval (m : ℕ) [Fact (Irreducible (gfPoly m))] (d : List Bool) (s : Bool)
    (β : List (List Bool)) (hβ : β.length = (encEdges (CatalyticMatching.General.graphBits G)).length) :
    MvPolynomial.eval (fun i => gfDecode m (β.getD i.val [])) (violPoly (G := G) m d s) =
      gfDecode m (qVal m N (encEdges (CatalyticMatching.General.graphBits G)) d s β) := by
  rw [qVal_decode m d s β hβ]
  unfold violPoly
  simp only [map_sum, map_prod, map_pow, MvPolynomial.eval_X]
  rfl

end PfaffianRecognition.CoRP

end

-- ===== from Solutions/Main/Prob.lean =====
section

namespace PfaffianRecognition.CoRP
open HypergraphUnreliability.FPRAS

/-- Replace block `r` (positions `r*b ≤ i < r*b + b`) of a tape by `v`. -/
def replaceBlock {T b : ℕ} (ω : Fin T → Bool) (r : ℕ) (v : Fin b → Bool) : Fin T → Bool :=
  fun i => if h : r * b ≤ i.val ∧ i.val < r * b + b then v ⟨i.val - r * b, by omega⟩ else ω i

/-- The `n` chunks of `t` bits of a block `v`. -/
def chunks (n t : ℕ) (v : Fin (n * t) → Bool) : List (List Bool) :=
  (List.range n).map (fun i => ((List.ofFn v).drop (i * t)).take t)

/-! ### 1. Union bound over blocks -/

/-- The contents of block `r` of a tape (requires the block to fit). -/
def getBlock {T b : ℕ} (r : ℕ) (hr : r * b + b ≤ T) (ω : Fin T → Bool) : Fin b → Bool :=
  fun j => ω ⟨r * b + j.val, by omega⟩

lemma replaceBlock_getBlock {T b : ℕ} (r : ℕ) (hr : r * b + b ≤ T) (ω : Fin T → Bool)
    (v : Fin b → Bool) : replaceBlock (replaceBlock ω r v) r (getBlock r hr ω) = ω := by
  funext i
  unfold replaceBlock getBlock
  by_cases h : r * b ≤ i.val ∧ i.val < r * b + b
  · rw [dif_pos h]
    congr 1; ext; simp only; omega
  · rw [dif_neg h, dif_neg h]

lemma getBlock_replaceBlock {T b : ℕ} (r : ℕ) (hr : r * b + b ≤ T) (ω : Fin T → Bool)
    (v : Fin b → Bool) : getBlock r hr (replaceBlock ω r v) = v := by
  funext j
  unfold replaceBlock getBlock
  dsimp only
  rw [dif_pos (by omega)]
  congr 1; ext; simp only; omega

open Classical in
lemma card_bad_le (T b r : ℕ) (hr : r * b + b ≤ T) (B : (Fin T → Bool) → Prop) (ε : ℝ)
    (hε : ∀ ω : Fin T → Bool,
      ((Finset.univ.filter (fun v : Fin b → Bool => B (replaceBlock ω r v))).card : ℝ) ≤ ε * 2 ^ b) :
    ((Finset.univ.filter B).card : ℝ) ≤ ε * 2 ^ T := by
  let Φ : (Fin T → Bool) × (Fin b → Bool) → (Fin T → Bool) × (Fin b → Bool) :=
    fun p => (replaceBlock p.1 r p.2, getBlock r hr p.1)
  have hΦ : ∀ p, Φ (Φ p) = p := by
    rintro ⟨ω, v⟩
    simp only [Φ, replaceBlock_getBlock, getBlock_replaceBlock]
  have h1 : (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin b → Bool) =>
      B (replaceBlock p.1 r p.2))).card =
      (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin b → Bool) => B p.1)).card := by
    apply Finset.card_nbij' Φ Φ
    · intro p hp; simpa [Φ] using hp
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      have := hΦ p
      rw [← this] at hp
      exact hp
    · intro p _; exact hΦ p
    · intro p _; exact hΦ p
  have h2 : (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin b → Bool) => B p.1)).card =
      (Finset.univ.filter B).card * 2 ^ b := by
    rw [show (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin b → Bool) => B p.1)) =
      (Finset.univ.filter B) ×ˢ (Finset.univ : Finset (Fin b → Bool)) by
        ext p; simp, Finset.card_product]
    simp
  have h3 : (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin b → Bool) =>
      B (replaceBlock p.1 r p.2))).card =
      ∑ ω : Fin T → Bool, (Finset.univ.filter (fun v : Fin b → Bool => B (replaceBlock ω r v))).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [Finset.card_filter]
  have h4 : ((Finset.univ.filter B).card : ℝ) * 2 ^ b ≤ (ε * 2 ^ T) * 2 ^ b := by
    have : ((Finset.univ.filter B).card : ℝ) * 2 ^ b =
        ∑ ω : Fin T → Bool,
          ((Finset.univ.filter (fun v : Fin b → Bool => B (replaceBlock ω r v))).card : ℝ) := by
      rw [← Nat.cast_sum, ← h3, h1, h2]; push_cast; ring
    rw [this]
    calc _ ≤ ∑ _ω : Fin T → Bool, ε * 2 ^ b := Finset.sum_le_sum fun ω _ => hε ω
      _ = (ε * 2 ^ T) * 2 ^ b := by simp; ring
  exact le_of_mul_le_mul_right h4 (by positivity)

open Classical in
theorem fairProb_exists_block_le (T R b : ℕ) (hT : R * b ≤ T) (bad : ℕ → (Fin T → Bool) → Prop)
    (ε : ℝ) (hε : ∀ r < R, ∀ ω : Fin T → Bool,
      ((Finset.univ.filter (fun v : Fin b → Bool => bad r (replaceBlock ω r v))).card : ℝ) ≤ ε * 2 ^ b) :
    fairProb T (fun ω => ∃ r < R, bad r ω) ≤ R * ε := by
  unfold fairProb
  rw [div_le_iff₀ (by positivity)]
  have key : ∀ r ∈ Finset.range R, ((Finset.univ.filter (bad r)).card : ℝ) ≤ ε * 2 ^ T := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hr' : r * b + b ≤ T := by
      have := Nat.mul_le_mul_right b hr
      rw [Nat.succ_mul] at this; omega
    exact card_bad_le T b r hr' (bad r) ε (hε r hr)
  calc (_ : ℝ)
      ≤ (((Finset.range R).biUnion (fun r => Finset.univ.filter (bad r))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (fun ω hω => by simp at hω ⊢; exact hω)
    _ ≤ ∑ r ∈ Finset.range R, ((Finset.univ.filter (bad r)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.range R, ε * 2 ^ T := Finset.sum_le_sum key
    _ = R * ε * 2 ^ T := by simp; ring

/-! ### 2. Chunk/tape compatibility -/

lemma take_drop_congr (L1 L2 : List Bool) (k len : ℕ) (hl : L1.length = L2.length)
    (h : ∀ p (h1 : p < L1.length) (h2 : p < L2.length), k ≤ p → p < k + len → L1[p] = L2[p]) :
    (L1.drop k).take len = (L2.drop k).take len := by
  apply List.ext_getElem
  · simp [hl]
  · intro j h1 h2
    simp only [List.getElem_take, List.getElem_drop]
    simp only [List.length_take, List.length_drop] at h1 h2
    exact h _ (by omega) (by omega) (by omega) (by omega)

lemma chunk_replaceBlock_self (T n t r i : ℕ) (ω : Fin T → Bool) (v : Fin (n * t) → Bool)
    (hi : i < n) (hT : (r + 1) * (n * t) ≤ T) :
    ((tapeList (replaceBlock ω r v)).drop ((r * n + i) * t)).take t =
      ((List.ofFn v).drop (i * t)).take t := by
  have hle : (i + 1) * t ≤ n * t := Nat.mul_le_mul_right t hi
  rw [add_one_mul] at hle hT
  have e1 : (r * n + i) * t = r * (n * t) + i * t := by ring
  rw [e1]
  apply List.ext_getElem
  · simp only [tapeList, List.length_take, List.length_drop, List.length_ofFn]
    generalize n * t = B at *
    generalize r * B = rB at *
    generalize i * t = it at *
    omega
  · intro j h1 h2
    simp only [List.getElem_take, List.getElem_drop, tapeList, List.getElem_ofFn, replaceBlock]
    simp only [List.length_take, List.length_drop, List.length_ofFn] at h2
    have hc : r * (n * t) ≤ r * (n * t) + i * t + j ∧
        r * (n * t) + i * t + j < r * (n * t) + n * t := by
      generalize n * t = B at *
      generalize r * B = rB at *
      generalize i * t = it at *
      omega
    rw [dif_pos hc]
    congr 1
    ext
    show r * (n * t) + i * t + j - r * (n * t) = i * t + j
    omega

lemma chunk_replaceBlock_ne (T n t r r' i : ℕ) (ω : Fin T → Bool) (v : Fin (n * t) → Bool)
    (hi : i < n) (h : r' ≠ r) :
    ((tapeList (replaceBlock ω r v)).drop ((r' * n + i) * t)).take t =
      ((tapeList ω).drop ((r' * n + i) * t)).take t := by
  have hle : (i + 1) * t ≤ n * t := Nat.mul_le_mul_right t hi
  rw [add_one_mul] at hle
  have e1 : (r' * n + i) * t = r' * (n * t) + i * t := by ring
  have hsep : r' * (n * t) + n * t ≤ r * (n * t) ∨ r * (n * t) + n * t ≤ r' * (n * t) := by
    rcases Nat.lt_or_gt_of_ne h with hr | hr
    · left; have := Nat.mul_le_mul_right (n * t) hr; rwa [Nat.succ_mul] at this
    · right; have := Nat.mul_le_mul_right (n * t) hr; rwa [Nat.succ_mul] at this
  rw [e1]
  apply take_drop_congr
  · simp [tapeList]
  · intro p h1 h2 hp1 hp2
    simp only [tapeList, List.getElem_ofFn, replaceBlock]
    rw [dif_neg]
    show ¬(r * (n * t) ≤ p ∧ p < r * (n * t) + n * t)
    generalize n * t = B at *
    generalize r * B = rB at *
    generalize r' * B = rB' at *
    generalize i * t = it at *
    omega

theorem roundPoint_replaceBlock_self (m T : ℕ) (E : List (ℕ × ℕ)) (ω : Fin T → Bool) (r : ℕ)
    (v : Fin (E.length * (2 * m)) → Bool) (hT : (r + 1) * (E.length * (2 * m)) ≤ T) :
    roundPoint m E (tapeList (replaceBlock ω r v)) r = chunks E.length (2 * m) v := by
  unfold roundPoint chunks
  exact List.map_congr_left fun i hi =>
    chunk_replaceBlock_self T _ _ r i ω v (List.mem_range.1 hi) hT

theorem roundPoint_replaceBlock_ne (m T : ℕ) (E : List (ℕ × ℕ)) (ω : Fin T → Bool) (r r' : ℕ)
    (v : Fin (E.length * (2 * m)) → Bool) (h : r' ≠ r) :
    roundPoint m E (tapeList (replaceBlock ω r v)) r' = roundPoint m E (tapeList ω) r' := by
  unfold roundPoint
  exact List.map_congr_left fun i hi =>
    chunk_replaceBlock_ne T _ _ r r' i ω v (List.mem_range.1 hi) h

/-! ### 3. Schwartz–Zippel on chunks (GF facts copied from scratch/gf/GF.lean) -/

open Polynomial in
lemma gfPoly_zero_pb : gfPoly 0 = 1 := by
  simp only [gfPoly, mul_zero, pow_zero, CharTwo.add_self_eq_zero, zero_add]

open Polynomial in
lemma gfPoly_monic_pb (m : ℕ) : (gfPoly m).Monic := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [gfPoly_zero_pb]; exact monic_one
  · unfold gfPoly
    rw [add_assoc]
    apply monic_X_pow_add
    calc degree ((X : (ZMod 2)[X]) ^ m + 1) ≤ m := by
          refine (degree_add_le _ _).trans (max_le ?_ ?_)
          · exact degree_X_pow_le m
          · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le m)
      _ < (2 * m : ℕ) := by exact_mod_cast (by omega : m < 2 * m)

open Polynomial in
lemma gfPoly_natDegree_pb (m : ℕ) : (gfPoly m).natDegree = 2 * m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [gfPoly_zero_pb]; simp
  · unfold gfPoly
    rw [add_assoc, natDegree_add_eq_left_of_degree_lt]
    · simp
    · rw [degree_X_pow]
      calc degree ((X : (ZMod 2)[X]) ^ m + 1) ≤ m := by
            refine (degree_add_le _ _).trans (max_le ?_ ?_)
            · exact degree_X_pow_le m
            · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le m)
        _ < (2 * m : ℕ) := by exact_mod_cast (by omega : m < 2 * m)

/-- The power basis `1, z, …, z^{2m-1}` of `GF m` over `𝔽₂`, indexed by `Fin (2m)`. -/
noncomputable def gfBasis_pb (m : ℕ) : Module.Basis (Fin (2 * m)) (ZMod 2) (GF m) :=
  (AdjoinRoot.powerBasis' (gfPoly_monic_pb m)).basis.reindex (finCongr (gfPoly_natDegree_pb m))

lemma gfBasis_apply_pb (m : ℕ) (i : Fin (2 * m)) : gfBasis_pb m i = (AdjoinRoot.root (gfPoly m)) ^ (i : ℕ) := by
  simp [gfBasis_pb]; rfl

/-- Bits as `𝔽₂`-coordinates. -/
def bitVec_pb (m : ℕ) (a : List Bool) : Fin (2 * m) → ZMod 2 :=
  fun i => if a.getD i false then 1 else 0

lemma gfDecode_eq_basis_pb (m : ℕ) (a : List Bool) :
    gfDecode m a = (gfBasis_pb m).equivFun.symm (bitVec_pb m a) := by
  rw [Module.Basis.equivFun_symm_apply, gfDecode, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gfBasis_apply_pb, bitVec_pb]
  split_ifs <;> simp

/-- `Bool ≃ 𝔽₂`. -/
def boolEquivZMod2_pb : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv := by decide
  right_inv := by decide

theorem gfDecode_bijective_pb (m : ℕ) :
    Function.Bijective (fun v : Fin (2 * m) → Bool => gfDecode m (List.ofFn v)) := by
  have hf : (fun v : Fin (2 * m) → Bool => gfDecode m (List.ofFn v)) =
      (gfBasis_pb m).equivFun.symm ∘ (Equiv.arrowCongr (Equiv.refl _) boolEquivZMod2_pb) := by
    funext v
    rw [gfDecode_eq_basis_pb]
    congr 1
    funext i
    simp [bitVec_pb, boolEquivZMod2_pb, List.getD_eq_getElem?_getD]
  rw [hf]
  exact (gfBasis_pb m).equivFun.symm.bijective.comp (Equiv.bijective _)

theorem nat_card_GF_pb (m : ℕ) : Nat.card (GF m) = 2 ^ (2 * m) := by
  rw [Nat.card_congr (gfBasis_pb m).equivFun.toEquiv]
  simp


lemma chunks_getD (n t : ℕ) (v : Fin (n * t) → Bool) (i : Fin n) :
    (chunks n t v).getD i.val [] = List.ofFn (fun j : Fin t => v (finProdFinEquiv (i, j))) := by
  have hle : (i.val + 1) * t ≤ n * t := Nat.mul_le_mul_right t i.2
  rw [add_one_mul] at hle
  unfold chunks
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2]
  simp only [Option.map_some, Option.getD_some]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]; omega
  · intro j h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    congr 1
    ext
    simp only [finProdFinEquiv_apply_val]
    ring

theorem card_chunks_root_le (m n : ℕ) [Fact (Irreducible (gfPoly m))]
    (P : MvPolynomial (Fin n) (GF m)) (hP : P ≠ 0) :
    ((Finset.univ.filter (fun v : Fin (n * (2 * m)) → Bool =>
        MvPolynomial.eval (fun i : Fin n => gfDecode m ((chunks n (2 * m) v).getD i.val [])) P = 0)).card : ℝ)
      ≤ (P.totalDegree : ℝ) / 2 ^ (2 * m) * 2 ^ (n * (2 * m)) := by
  classical
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have := (Fact.out : Irreducible (gfPoly 0))
      rw [gfPoly_zero_pb] at this
      exact absurd isUnit_one this.not_isUnit
    · exact hm
  have hfin : Finite (GF m) := Nat.finite_of_card_ne_zero (by rw [nat_card_GF_pb]; positivity)
  let _ : Fintype (GF m) := Fintype.ofFinite (GF m)
  have hcard : (Finset.univ : Finset (GF m)).card = 2 ^ (2 * m) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, nat_card_GF_pb]
  let e : (Fin (n * (2 * m)) → Bool) ≃ (Fin n → GF m) :=
    ((finProdFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.curry _ _ _)).trans
      (Equiv.piCongrRight fun _ => Equiv.ofBijective _ (gfDecode_bijective_pb m))
  have he : ∀ v, e v = fun i : Fin n => gfDecode m ((chunks n (2 * m) v).getD i.val []) := by
    intro v; funext i
    rw [chunks_getD]
    rfl
  have hc : (Finset.univ.filter (fun v : Fin (n * (2 * m)) → Bool =>
        MvPolynomial.eval (fun i : Fin n => gfDecode m ((chunks n (2 * m) v).getD i.val [])) P = 0)).card
      = (Finset.univ.filter (fun x : Fin n → GF m => MvPolynomial.eval x P = 0)).card := by
    apply Finset.card_equiv e
    intro v
    simp [he]
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hP (Finset.univ : Finset (GF m))
  rw [Fintype.piFinset_univ, hcard] at hsz
  have hpos : (0 : ℚ≥0) < 2 ^ (2 * m) := by positivity
  push_cast at hsz
  rw [div_le_div_iff₀ (by positivity) hpos] at hsz
  have hnat : (Finset.univ.filter (fun x : Fin n → GF m => MvPolynomial.eval x P = 0)).card * 2 ^ (2 * m)
      ≤ P.totalDegree * (2 ^ (2 * m)) ^ n := by
    exact_mod_cast hsz
  have h' : ((Finset.univ.filter (fun x : Fin n → GF m => MvPolynomial.eval x P = 0)).card : ℝ) *
      2 ^ (2 * m) ≤ (P.totalDegree : ℝ) * (2 ^ (2 * m)) ^ n := by
    exact_mod_cast hnat
  rw [hc, div_mul_eq_mul_div, le_div_iff₀ (by positivity),
    show (2 : ℝ) ^ (n * (2 * m)) = (2 ^ (2 * m)) ^ n by rw [← pow_mul, mul_comm]]
  exact h'

end PfaffianRecognition.CoRP

end

-- ===== from Solutions/Main/Sound.lean =====
section

namespace PfaffianRecognition.CoRP
open PfaffianRecognition.Recognition HypergraphUnreliability.FPRAS

/-- State before round `r`. -/
def stAt (m N : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) (r : ℕ) : List Eqn × (Bool × Bool) :=
  (List.range r).foldl (roundStep m N E ρ) ([], (false, false))

theorem stAt_succ (m N : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) (r : ℕ) :
    stAt m N E ρ (r + 1) = roundStep m N E ρ (stAt m N E ρ r) r := by
  simp [stAt, List.range_succ, List.foldl_append]

/-- `roundStep` with the sampled point as an explicit argument. -/
def roundStepPt (m N : ℕ) (E : List (ℕ × ℕ)) (α : List (List Bool)) (st : List Eqn × (Bool × Bool)) :
    List Eqn × (Bool × Bool) :=
  if st.2.1 then st
  else if !(solveF2 (E.length + 1) st.1).1 then (st.1, (true, false))
  else if gfIsZero m (qVal m N E ((solveF2 (E.length + 1) st.1).2.take E.length)
      ((solveF2 (E.length + 1) st.1).2.getD E.length false) α) then
    (st.1, (true, true))
  else if isPMList N E (greedySearch m N E ((solveF2 (E.length + 1) st.1).2.take E.length)
        ((solveF2 (E.length + 1) st.1).2.getD E.length false) α) &&
      violates E ((solveF2 (E.length + 1) st.1).2.take E.length)
        ((solveF2 (E.length + 1) st.1).2.getD E.length false)
        (greedySearch m N E ((solveF2 (E.length + 1) st.1).2.take E.length)
          ((solveF2 (E.length + 1) st.1).2.getD E.length false) α) then
    (st.1 ++ [matchEqn E (greedySearch m N E ((solveF2 (E.length + 1) st.1).2.take E.length)
        ((solveF2 (E.length + 1) st.1).2.getD E.length false) α)],
      (false, false))
  else (st.1, (true, true))

theorem roundStep_eq_pt (m N : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) (st : List Eqn × (Bool × Bool))
    (r : ℕ) : roundStep m N E ρ st r = roundStepPt m N E (roundPoint m E ρ r) st := rfl

theorem roundStep_congr (m N : ℕ) (E : List (ℕ × ℕ)) (ρ ρ' : List Bool) (st : List Eqn × (Bool × Bool))
    (r : ℕ) (h : roundPoint m E ρ r = roundPoint m E ρ' r) :
    roundStep m N E ρ st r = roundStep m N E ρ' st r := by
  rw [roundStep_eq_pt, roundStep_eq_pt, h]

theorem foldl_range_congr {β : Type} (f g : β → ℕ → β) (b : β) (r : ℕ)
    (h : ∀ st, ∀ r' < r, f st r' = g st r') :
    (List.range r).foldl f b = (List.range r).foldl g b := by
  apply List.foldl_ext
  intro st r' hr'
  exact h st r' (List.mem_range.1 hr')

theorem stAt_congr (m N : ℕ) (E : List (ℕ × ℕ)) (ρ ρ' : List Bool) (r : ℕ)
    (h : ∀ r' < r, roundPoint m E ρ r' = roundPoint m E ρ' r') :
    stAt m N E ρ r = stAt m N E ρ' r := by
  unfold stAt
  exact foldl_range_congr _ _ _ r (fun st r' hr' => roundStep_congr m N E ρ ρ' st r' (h r' hr'))

/-- The solution reported in a round. -/
def solOf (n : ℕ) (eqs : List Eqn) : List Bool := (solveF2 (n + 1) eqs).2

/-- A bad round: reached while running, with a consistent system, and `Q` vanishes at the sample. -/
def badRound (m N : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) (r : ℕ) : Prop :=
  (stAt m N E ρ r).2.1 = false ∧ (solveF2 (E.length + 1) (stAt m N E ρ r).1).1 = true ∧
    gfIsZero m (qVal m N E ((solOf E.length (stAt m N E ρ r).1).take E.length)
      ((solOf E.length (stAt m N E ρ r).1).getD E.length false) (roundPoint m E ρ r)) = true

/-- Chain property of an equation list. -/
def Chain (eqs : List Eqn) : Prop :=
  ∀ i (hi : i < eqs.length), ∃ x : List Bool,
    (∀ j (hj : j < i), satisfiesEqn x (eqs[j]'(lt_trans hj hi)) = true) ∧
      satisfiesEqn x (eqs[i]'hi) = false


theorem Chain.take {eqs : List Eqn} (h : Chain eqs) (k : ℕ) : Chain (eqs.take k) := by
  intro i hi
  have hi' : i < eqs.length := by simp at hi; omega
  obtain ⟨x, hx1, hx2⟩ := h i hi'
  refine ⟨x, fun j hj => ?_, ?_⟩
  · simpa using hx1 j hj
  · simpa using hx2

/-- Invariant of the rounds on a non-Pfaffian graph when no round is bad. -/
def SInv (n r : ℕ) (st : List Eqn × (Bool × Bool)) : Prop :=
  (st.2.1 = true → st.2.2 = false) ∧
    (st.2.1 = false → st.1.length = r ∧ Chain st.1 ∧ ∀ e ∈ st.1, e.1.length = n + 1)

variable {N : ℕ} {G : SimpleGraph (Fin N)}

theorem SInv_step (m : ℕ) [Fact (Irreducible (gfPoly m))] (ρ : List Bool) (r : ℕ)
    (hbad : ¬ badRound m N (encEdges (CatalyticMatching.General.graphBits G)) ρ r)
    (h : SInv (encEdges (CatalyticMatching.General.graphBits G)).length r
      (stAt m N (encEdges (CatalyticMatching.General.graphBits G)) ρ r)) :
    SInv (encEdges (CatalyticMatching.General.graphBits G)).length (r + 1)
      (stAt m N (encEdges (CatalyticMatching.General.graphBits G)) ρ (r + 1)) := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  rw [stAt_succ]
  set st := stAt m N E ρ r with hst
  obtain ⟨hdone, hrun⟩ := h
  unfold badRound at hbad
  rw [← hst] at hbad
  unfold roundStep
  split_ifs with h1 h2 h3 h4
  · exact ⟨hdone, fun h => absurd h1 (by simp [h])⟩
  · exact ⟨fun _ => rfl, fun h => by simp at h⟩
  · exfalso
    apply hbad
    refine ⟨by simpa using h1, by simpa using h2, ?_⟩
    simpa [solOf] using h3
  · have hf : st.2.1 = false := by simpa using h1
    obtain ⟨hlen, hch, hel⟩ := hrun hf
    have hcon : (solveF2 (E.length + 1) st.1).1 = true := by simpa using h2
    obtain ⟨hxl, hxs⟩ := solveF2_sound (E.length + 1) st.1 (fun e he => (hel e he).le) hcon
    set x := (solveF2 (E.length + 1) st.1).2 with hx
    rw [Bool.and_eq_true] at h4
    refine ⟨fun h => by simp at h, fun _ => ⟨by simp [hlen], ?_, ?_⟩⟩
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hir : i < st.1.length
      · obtain ⟨y, hy1, hy2⟩ := hch i hir
        refine ⟨y, fun j hj => ?_, ?_⟩
        · rw [List.getElem_append_left (by omega)]; exact hy1 j hj
        · rw [List.getElem_append_left hir]; exact hy2
      · have hieq : i = st.1.length := by omega
        refine ⟨x, fun j hj => ?_, ?_⟩
        · rw [List.getElem_append_left (by omega)]; exact hxs _ (List.getElem_mem _)
        · rw [List.getElem_append_right (by omega)]
          simp only [hieq, Nat.sub_self, List.getElem_singleton]
          have hsplit : x = x.take E.length ++ [x.getD E.length false] := by
            apply List.ext_getElem
            · simp [hxl]
            · intro k hk1 hk2
              by_cases hk : k < E.length
              · rw [List.getElem_append_left (by simp; omega)]; simp
              · have : k = E.length := by omega
                subst this
                rw [List.getElem_append_right (by simp)]
                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]
          have key := satisfies_matchEqn E (greedySearch m N E (x.take E.length)
            (x.getD E.length false) (roundPoint m E ρ r)) (x.take E.length) (x.getD E.length false)
            (by simp [hxl])
          rw [h4.2] at key
          exact (congrArg (fun y => satisfiesEqn y _) hsplit).trans key
    · intro e he
      rw [List.mem_append] at he
      rcases he with he | he
      · exact hel e he
      · simp only [List.mem_singleton] at he
        rw [he, matchEqn_length]
  · exfalso
    have hcon : (solveF2 (E.length + 1) st.1).1 = true := by simpa using h2
    have hf : st.2.1 = false := by simpa using h1
    obtain ⟨hlen, hch, hel⟩ := hrun hf
    obtain ⟨hxl, -⟩ := solveF2_sound (E.length + 1) st.1 (fun e he => (hel e he).le) hcon
    have := greedy_correct (G := G) m ((solveF2 (E.length + 1) st.1).2.take E.length)
      ((solveF2 (E.length + 1) st.1).2.getD E.length false) (roundPoint m E ρ r)
      (by show (roundPoint m E ρ r).length = E.length; simp [roundPoint])
      (by show (List.take E.length _).length = E.length; simp [hxl]) (by simpa using h3)
    apply h4
    rw [this.1, this.2]; rfl


theorem runRounds_false_of_no_bad (m : ℕ) [Fact (Irreducible (gfPoly m))] (ρ : List Bool)
    (hno : ∀ r < (encEdges (CatalyticMatching.General.graphBits G)).length + 3,
      ¬ badRound m N (encEdges (CatalyticMatching.General.graphBits G)) ρ r) :
    runRounds m N (encEdges (CatalyticMatching.General.graphBits G)) ρ = false := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  have hinv : ∀ r ≤ E.length + 3, SInv E.length r (stAt m N E ρ r) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨fun h => by simp [stAt] at h, fun _ => ⟨by simp [stAt], ?_, by simp [stAt]⟩⟩
      intro i hi; simp [stAt] at hi
    | succ r ih =>
      intro hr
      exact SInv_step (G := G) m ρ r (hno r (by omega)) (ih (by omega))
  obtain ⟨hd, hr⟩ := hinv (E.length + 3) le_rfl
  have hrr : runRounds m N E ρ = (!(stAt m N E ρ (E.length + 3)).2.1 ||
      (stAt m N E ρ (E.length + 3)).2.2) := rfl
  rw [hrr]
  cases hdn : (stAt m N E ρ (E.length + 3)).2.1
  · exfalso
    obtain ⟨hlen, hch, hel⟩ := hr hdn
    set eqs := (stAt m N E ρ (E.length + 3)).1
    have hidx : E.length + 2 < eqs.length := by omega
    obtain ⟨x, hx1, -⟩ := hch (E.length + 2) hidx
    have hle := eqn_chain_length_le (E.length + 1) (eqs.take (E.length + 2))
      (fun e he => hel e (List.mem_of_mem_take he)) (hch.take _)
      ⟨x, fun e he => by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
        simp only [List.length_take] at hj
        simpa using hx1 j (by omega)⟩
    simp at hle; omega
  · simp [hd hdn]


theorem chunks_length (n t : ℕ) (v : Fin (n * t) → Bool) : (chunks n t v).length = n := by
  simp [chunks]

open Classical in
theorem bad_count (hG : ¬ IsPfaffianGraph G) (m : ℕ) [Fact (Irreducible (gfPoly m))] (T : ℕ)
    (ω : Fin T → Bool) (r : ℕ)
    (hT : (r + 1) * ((encEdges (CatalyticMatching.General.graphBits G)).length * (2 * m)) ≤ T) :
    ((Finset.univ.filter (fun v : Fin ((encEdges (CatalyticMatching.General.graphBits G)).length * (2 * m)) → Bool =>
        badRound m N (encEdges (CatalyticMatching.General.graphBits G))
          (tapeList (replaceBlock ω r v)) r)).card : ℝ) ≤
      (N : ℝ) / 2 ^ (2 * m) * 2 ^ ((encEdges (CatalyticMatching.General.graphBits G)).length * (2 * m)) := by
  set E := encEdges (CatalyticMatching.General.graphBits G) with hE
  have hst : ∀ v : Fin (E.length * (2 * m)) → Bool,
      stAt m N E (tapeList (replaceBlock ω r v)) r = stAt m N E (tapeList ω) r := fun v =>
    stAt_congr m N E _ _ r (fun r' hr' => roundPoint_replaceBlock_ne m T E ω r r' v (by omega))
  set st := stAt m N E (tapeList ω) r
  set x := solOf E.length st.1
  have hsub : (Finset.univ.filter (fun v : Fin (E.length * (2 * m)) → Bool =>
      badRound m N E (tapeList (replaceBlock ω r v)) r)) ⊆
      (Finset.univ.filter (fun v : Fin (E.length * (2 * m)) → Bool =>
        MvPolynomial.eval (fun i : Fin E.length => gfDecode m ((chunks E.length (2 * m) v).getD i.val []))
          (violPoly (G := G) m (x.take E.length) (x.getD E.length false)) = 0)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨-, -, hz⟩ := hv
    rw [hst v, roundPoint_replaceBlock_self m T E ω r v hT] at hz
    rw [violPoly_eval m _ _ _ (chunks_length _ _ v)]
    exact (gfIsZero_iff m _).1 hz
  have hne := violPoly_ne_zero (G := G) m (x.take E.length) (x.getD E.length false)
    (exists_viol_of_not_pfaffian hG _ _)
  have hdeg := violPoly_totalDegree (G := G) m (x.take E.length) (x.getD E.length false)
  calc ((Finset.univ.filter _).card : ℝ) ≤ ((Finset.univ.filter (fun v : Fin (E.length * (2 * m)) → Bool =>
        MvPolynomial.eval (fun i : Fin E.length => gfDecode m ((chunks E.length (2 * m) v).getD i.val []))
          (violPoly (G := G) m (x.take E.length) (x.getD E.length false)) = 0)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by
        convert card_chunks_root_le m E.length _ hne using 2
    _ ≤ (N : ℝ) / 2 ^ (2 * m) * 2 ^ (E.length * (2 * m)) := by
        gcongr


theorem fairProb_mono' (T : ℕ) (A B : (Fin T → Bool) → Prop) (h : ∀ ω, A ω → B ω) :
    fairProb T A ≤ fairProb T B := by
  classical
  unfold fairProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun ω hω => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢; exact h ω hω)

theorem fairProb_compl (T : ℕ) (A : (Fin T → Bool) → Prop) :
    fairProb T (fun ω => ¬ A ω) = 1 - fairProb T A := by
  classical
  unfold fairProb
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin T → Bool))) A
  have hu : (Finset.univ : Finset (Fin T → Bool)).card = 2 ^ T := by
    simp [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  rw [hu] at hcard
  have h2 : (2 : ℝ) ^ T ≠ 0 := by positivity
  field_simp
  have : ((Finset.univ.filter (fun ω => ¬ A ω)).card : ℝ) + (Finset.univ.filter A).card = 2 ^ T := by
    rw [add_comm]; exact_mod_cast hcard
  convert (eq_sub_of_add_eq this) using 2
  congr 1
  exact Finset.filter_congr_decidable _ _ _

theorem two_pow_size_le (N : ℕ) : 2 ^ Nat.size N ≤ 2 * N + 1 := by
  rcases Nat.eq_zero_or_pos (Nat.size N) with h | h
  · rw [h]; omega
  · by_contra hc
    push Not at hc
    have : N < 2 ^ (Nat.size N - 1) := by
      have e : 2 ^ Nat.size N = 2 * 2 ^ (Nat.size N - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have := (Nat.size_le).2 this
    omega

theorem fieldM_le (N : ℕ) : fieldM N ≤ (2 * N + 1) ^ 2 := by
  unfold fieldM
  calc 3 ^ Nat.size N ≤ 4 ^ Nat.size N := Nat.pow_le_pow_left (by norm_num) _
    _ = (2 ^ Nat.size N) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ (2 * N + 1) ^ 2 := Nat.pow_le_pow_left (two_pow_size_le N) 2

theorem lt_fieldM (N : ℕ) : N < fieldM N := by
  unfold fieldM
  exact lt_of_lt_of_le (Nat.lt_size_self N) (Nat.pow_le_pow_left (by norm_num) _)

theorem aux_ineq (N : ℕ) : 2 * N * (N * N + 3) ≤ 4 ^ (N + 1) := by
  induction N with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · have : 2 * (k + 1) * ((k + 1) * (k + 1) + 3) ≤ 4 * (2 * k * (k * k + 3)) := by nlinarith
      calc _ ≤ 4 * (2 * k * (k * k + 3)) := this
        _ ≤ 4 * 4 ^ (k + 1) := by omega
        _ = 4 ^ (k + 1 + 1) := by ring

theorem graphBits_length (G : SimpleGraph (Fin N)) :
    (CatalyticMatching.General.graphBits G).length = N + 1 + N * N := by
  unfold CatalyticMatching.General.graphBits
  simp [vertexPairs_length]; ring

theorem encEdges_length_le (G : SimpleGraph (Fin N)) :
    (encEdges (CatalyticMatching.General.graphBits G)).length ≤ N * N := by
  unfold encEdges
  calc _ ≤ (idxPairs (hdrN (CatalyticMatching.General.graphBits G))).length := List.length_filter_le _ _
    _ = N * N := by rw [hdrN_graphBits, idxPairs_length]


theorem tape_enough (N n m : ℕ) (hn : n ≤ N * N) (hm : m ≤ (2 * N + 1) ^ 2) :
    (n + 3) * (n * (2 * m)) ≤ ((N + 1 + N * N) + 2) ^ 8 := by
  set X := N * N + N + 3 with hX
  have h1 : n + 3 ≤ X := by omega
  have h2 : n ≤ X := by omega
  have h3 : 2 * m ≤ 8 * X := by nlinarith
  have hX3 : 3 ≤ X := by omega
  have e : (N + 1 + N * N) + 2 = X := by omega
  rw [e]
  calc (n + 3) * (n * (2 * m)) ≤ X * (X * (8 * X)) := by
        apply Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    _ = 8 * X ^ 3 := by ring
    _ ≤ X ^ 5 * X ^ 3 := by
        apply Nat.mul_le_mul_right
        calc 8 ≤ 3 ^ 5 := by norm_num
          _ ≤ X ^ 5 := Nat.pow_le_pow_left hX3 5
    _ = X ^ 8 := by ring

theorem err_small (N n m : ℕ) (hn : n ≤ N * N) (hm : N < m) :
    ((n + 3 : ℕ) : ℝ) * ((N : ℝ) / 2 ^ (2 * m)) ≤ 1 / 2 := by
  have h1 : 2 * N * (n + 3) ≤ 2 ^ (2 * m) := by
    calc 2 * N * (n + 3) ≤ 2 * N * (N * N + 3) := by
          apply Nat.mul_le_mul_left; omega
      _ ≤ 4 ^ (N + 1) := aux_ineq N
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      _ = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  have h1' : (2 : ℝ) * N * (n + 3) ≤ 2 ^ (2 * m) := by exact_mod_cast h1
  have hpos : (0 : ℝ) < 2 ^ (2 * m) := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ hpos (by norm_num)]
  push_cast
  nlinarith

theorem sound_graph (hG : ¬ IsPfaffianGraph G) :
    (1 / 2 : ℝ) ≤ fairProb (((CatalyticMatching.General.graphBits G).length + 2) ^ 8)
      (fun ω => pfAlg (tapeList ω, CatalyticMatching.General.graphBits G) = false) := by
  set w := CatalyticMatching.General.graphBits G with hw
  set T := (w.length + 2) ^ 8 with hT
  set E := encEdges w with hE
  set m := fieldM N with hmdef
  haveI : Fact (Irreducible (gfPoly m)) := ⟨gfPoly_irreducible (Nat.size N)⟩
  have hpf : ∀ ρ, pfAlg (ρ, w) = runRounds m N E ρ := by
    intro ρ
    unfold pfAlg
    simp only
    rw [hw, validEnc_graphBits, Bool.true_and, hdrN_graphBits]
  set b := E.length * (2 * m) with hb
  have hTb : (E.length + 3) * b ≤ T := by
    rw [hT, graphBits_length]
    exact tape_enough N E.length m (encEdges_length_le G) (fieldM_le N)
  have hunion := fairProb_exists_block_le T (E.length + 3) b hTb
    (fun r ω => badRound m N E (tapeList ω) r) ((N : ℝ) / 2 ^ (2 * m))
    (fun r hr ω => bad_count (G := G) hG m T ω r (by
      calc (r + 1) * b ≤ (E.length + 3) * b := Nat.mul_le_mul_right _ (by omega)
        _ ≤ T := hTb))
  have hmono : fairProb T (fun ω => ¬ ∃ r < E.length + 3, badRound m N E (tapeList ω) r) ≤
      fairProb T (fun ω => pfAlg (tapeList ω, w) = false) := by
    apply fairProb_mono'
    intro ω hω
    rw [hpf]
    push Not at hω
    exact runRounds_false_of_no_bad (G := G) m (tapeList ω) hω
  rw [fairProb_compl] at hmono
  have herr := err_small N E.length m (encEdges_length_le G) (lt_fieldM N)
  push_cast at herr hunion
  linarith

theorem pfAlg_sound_core (w : List Bool) (h : ¬ PfaffianRecognition.Recognition.pfaffianLanguage w) :
    (1 / 2 : ℝ) ≤ fairProb ((w.length + 2) ^ 8) (fun ω => pfAlg (tapeList ω, w) = false) := by
  by_cases hv : validEnc w = true
  · have hG : ¬ IsPfaffianGraph (encGraph w hv) := by
      intro hP
      exact h ⟨_, encGraph w hv, graphBits_encGraph w hv, hP⟩
    have := sound_graph hG
    rwa [graphBits_encGraph w hv] at this
  · have hall : ∀ ω : Fin ((w.length + 2) ^ 8) → Bool, pfAlg (tapeList ω, w) = false := by
      intro ω; unfold pfAlg; simp [hv]
    have h1 : fairProb ((w.length + 2) ^ 8) (fun ω => pfAlg (tapeList ω, w) = false) = 1 := by
      classical
      unfold fairProb
      simp [hall, Finset.card_univ, Fintype.card_bool]
    rw [h1]; norm_num

end PfaffianRecognition.CoRP

end

theorem solution (w : List Bool) (h : ¬ PfaffianRecognition.Recognition.pfaffianLanguage w) :
    (1 / 2 : ℝ) ≤ HypergraphUnreliability.FPRAS.fairProb ((w.length + 2) ^ 8)
      (fun ω => PfaffianRecognition.CoRP.pfAlg (HypergraphUnreliability.FPRAS.tapeList ω, w) = false) :=
  PfaffianRecognition.CoRP.pfAlg_sound_core w h

