-- Prove2me | solution 1 for SzemerediTrotter.Incidence.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T11:05:04.283238+00:00
-- url     : https://prove2.me/submissions/561b71ba-7b64-4d1c-9b97-ec672dbf96ee

import Mathlib
import Definitions.Def_SzemerediTrotter_Incidence_incidences

set_option autoImplicit false
set_option linter.unusedVariables false

-- 16b72252 child ST3 (incidence graph): consecutive points on each line, lex key order.
-- Definitions are copied from scratch/probe/16b72252_children.lean.

section SzemerediTrotterHelpers

open SzemerediTrotter.Incidence

/-- Closed segment of an unordered pair of points. -/
noncomputable def stSeg (e : Sym2 Plane) : Set Plane :=
  Sym2.lift ⟨fun a b => segment ℝ a b, fun a b => segment_symm ℝ a b⟩ e

/-- Two distinct edges cross: their segments share a point that is not a common endpoint. -/
def stCrosses (e f : Sym2 Plane) : Prop :=
  e ≠ f ∧ ∃ x, x ∈ stSeg e ∧ x ∈ stSeg f ∧ ¬ (x ∈ e ∧ x ∈ f)

/-- Ordered crossing pairs of an edge set. -/
noncomputable def stCrossingPairs (E : Finset (Sym2 Plane)) : Finset (Sym2 Plane × Sym2 Plane) :=
  by classical exact (E ×ˢ E).filter (fun p => stCrosses p.1 p.2)

/-- A straight-line drawing on `V`: proper edges with endpoints in `V`, and no vertex
in the relative interior of an edge. -/
def stDrawing (V : Finset Plane) (E : Finset (Sym2 Plane)) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag ∧ ∀ x ∈ e, x ∈ V) ∧ (∀ e ∈ E, ∀ v ∈ V, v ∈ stSeg e → v ∈ e)

/-- Lexicographic key on the plane. -/
noncomputable def stKey (p : Plane) : ℝ ×ₗ ℝ := toLex (p 0, p 1)

theorem stKey_inj : Function.Injective stKey := by
  intro p q h
  have h0 : p 0 = q 0 := congrArg (fun z => (ofLex z).1) h
  have h1 : p 1 = q 1 := congrArg (fun z => (ofLex z).2) h
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem stSeg_mk (a b : Plane) : stSeg s(a, b) = segment ℝ a b := rfl

theorem stKey_seg {p q x : Plane} (h : stKey p ≤ stKey q) (hx : x ∈ segment ℝ p q) :
    stKey p ≤ stKey x ∧ stKey x ≤ stKey q := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  have hx0 : (a • p + b • q) 0 = a * p 0 + b * q 0 := by simp
  have hx1 : (a • p + b • q) 1 = a * p 1 + b * q 1 := by simp
  unfold stKey at *
  rw [Prod.Lex.toLex_le_toLex] at h ⊢
  simp only [Prod.Lex.toLex_le_toLex, hx0, hx1] at *
  have ha' : a = 1 - b := by linarith
  subst ha'
  rcases h with h | ⟨h0, h1⟩
  · constructor
    · rcases eq_or_lt_of_le hb with hb0 | hbpos
      · right; subst hb0; constructor <;> simp
      · left; nlinarith
    · rcases eq_or_lt_of_le ha with ha0 | hapos
      · right
        have hb1 : b = 1 := by linarith
        subst hb1
        constructor <;> simp
      · left; nlinarith
  · constructor
    · right; constructor
      · rw [← h0]; nlinarith
      · nlinarith
    · right; constructor
      · rw [← h0]; nlinarith
      · nlinarith

theorem st_line_eq_span {l : AffineSubspace ℝ Plane} (hl : IsLine l) {p q : Plane}
    (hpq : p ≠ q) (hp : p ∈ l) (hq : q ∈ l) : affineSpan ℝ ({p, q} : Set Plane) = l := by
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
  · apply Submodule.eq_of_le_of_finrank_eq
    · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem hp hq)
    · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hpq)]
      exact hl.symm
  · exact (affineSpan_nonempty ℝ).mpr (Set.insert_nonempty _ _)
  · exact affineSpan_pair_le_of_mem_of_mem hp hq

theorem st_lines_eq {l₁ l₂ : AffineSubspace ℝ Plane} (h₁ : IsLine l₁) (h₂ : IsLine l₂)
    {p q : Plane} (hpq : p ≠ q) (hp₁ : p ∈ l₁) (hq₁ : q ∈ l₁) (hp₂ : p ∈ l₂) (hq₂ : q ∈ l₂) :
    l₁ = l₂ := by
  rw [← st_line_eq_span h₁ hpq hp₁ hq₁, st_line_eq_span h₂ hpq hp₂ hq₂]

open Classical in
/-- Edges on a line: pairs of consecutive (for the key order) points of `P` on `l`. -/
noncomputable def stEdgesOn (P : Finset Plane) (l : AffineSubspace ℝ Plane) : Finset (Sym2 Plane) :=
  (((P.filter (· ∈ l)) ×ˢ (P.filter (· ∈ l))).filter
    (fun pq => stKey pq.1 < stKey pq.2 ∧
      ∀ r ∈ P.filter (· ∈ l), ¬ (stKey pq.1 < stKey r ∧ stKey r < stKey pq.2))).image
    (fun pq => s(pq.1, pq.2))

theorem mem_stEdgesOn {P : Finset Plane} {l : AffineSubspace ℝ Plane} {e : Sym2 Plane} :
    e ∈ stEdgesOn P l ↔ ∃ p q, p ∈ P ∧ p ∈ l ∧ q ∈ P ∧ q ∈ l ∧ stKey p < stKey q ∧
      (∀ r, r ∈ P → r ∈ l → ¬ (stKey p < stKey r ∧ stKey r < stKey q)) ∧ e = s(p, q) := by
  classical
  unfold stEdgesOn
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨p, q, ⟨⟨⟨hpP, hpl⟩, hqP, hql⟩, hlt, hall⟩, rfl⟩
    exact ⟨p, q, hpP, hpl, hqP, hql, hlt, fun r hr hrl => hall r ⟨hr, hrl⟩, rfl⟩
  · rintro ⟨p, q, hpP, hpl, hqP, hql, hlt, hall, rfl⟩
    exact ⟨p, q, ⟨⟨⟨hpP, hpl⟩, hqP, hql⟩, hlt, fun r hr => hall r hr.1 hr.2⟩, rfl⟩

theorem st_edgesOn_overlap {P : Finset Plane} {l : AffineSubspace ℝ Plane} {e e' : Sym2 Plane}
    (he : e ∈ stEdgesOn P l) (he' : e' ∈ stEdgesOn P l) (hne : e ≠ e') {x : Plane}
    (hx : x ∈ stSeg e) (hx' : x ∈ stSeg e') : x ∈ e ∧ x ∈ e' := by
  obtain ⟨p, q, hpP, hpl, hqP, hql, hlt, hall, rfl⟩ := mem_stEdgesOn.mp he
  obtain ⟨p', q', hpP', hpl', hqP', hql', hlt', hall', rfl⟩ := mem_stEdgesOn.mp he'
  rw [stSeg_mk] at hx hx'
  obtain ⟨hpx, hxq⟩ := stKey_seg hlt.le hx
  obtain ⟨hpx', hxq'⟩ := stKey_seg hlt'.le hx'
  have key : stKey q ≤ stKey p' ∨ stKey q' ≤ stKey p := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases lt_trichotomy (stKey p) (stKey p') with hlt1 | heq1 | hgt1
    · exact hall p' hpP' hpl' ⟨hlt1, h1⟩
    · have hpp : p = p' := stKey_inj heq1
      subst hpp
      rcases lt_trichotomy (stKey q) (stKey q') with hlt2 | heq2 | hgt2
      · exact hall' q hqP hql ⟨hlt, hlt2⟩
      · have : q = q' := stKey_inj heq2
        subst this
        exact hne rfl
      · exact hall q' hqP' hql' ⟨hlt', hgt2⟩
    · exact hall' p hpP hpl ⟨hgt1, h2⟩
  rcases key with k | k
  · have h1 : stKey x = stKey q := le_antisymm hxq (k.trans hpx')
    have h2 : stKey q = stKey p' := le_antisymm k (h1 ▸ hpx')
    have hxq0 : x = q := stKey_inj h1
    have hqp : q = p' := stKey_inj h2
    exact ⟨hxq0 ▸ Sym2.mem_mk_right p q, (hxq0.trans hqp) ▸ Sym2.mem_mk_left p' q'⟩
  · have h1 : stKey x = stKey p := le_antisymm (hxq'.trans k) hpx
    have h2 : stKey q' = stKey p := le_antisymm k (h1 ▸ hxq')
    have hxp : x = p := stKey_inj h1
    have hqp : q' = p := stKey_inj h2
    exact ⟨hxp ▸ Sym2.mem_mk_left p q, (hxp.trans hqp.symm) ▸ Sym2.mem_mk_right p' q'⟩

open Classical in
theorem st_card_edgesOn_ge (P : Finset Plane) (l : AffineSubspace ℝ Plane) :
    (P.filter (· ∈ l)).card ≤ (stEdgesOn P l).card + 1 := by
  classical
  set S := P.filter (· ∈ l) with hS
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]; simp
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S stKey hne
  have h : ∀ p ∈ S.erase m, ∃ q ∈ S, stKey p < stKey q ∧
      ∀ r ∈ S, stKey p < stKey r → stKey q ≤ stKey r := by
    intro p hp
    rw [Finset.mem_erase] at hp
    obtain ⟨hpm, hpS⟩ := hp
    have hlt : stKey p < stKey m := lt_of_le_of_ne (hmax p hpS) (fun h => hpm (stKey_inj h))
    obtain ⟨q, hqT, hqmin⟩ := Finset.exists_min_image (S.filter (fun r => stKey p < stKey r))
      stKey ⟨m, Finset.mem_filter.mpr ⟨hm, hlt⟩⟩
    rw [Finset.mem_filter] at hqT
    exact ⟨q, hqT.1, hqT.2, fun r hr hpr => hqmin r (Finset.mem_filter.mpr ⟨hr, hpr⟩)⟩
  choose! g hgS hgl hgmin using h
  have hcard : (S.erase m).card ≤ (stEdgesOn P l).card := by
    apply Finset.card_le_card_of_injOn (fun p => s(p, g p))
    · intro p hp
      have hp' : p ∈ S.erase m := Finset.mem_coe.mp hp
      have hpS : p ∈ S := (Finset.mem_erase.mp hp').2
      have hpS' := Finset.mem_filter.mp hpS
      have hqS' := Finset.mem_filter.mp (hgS p hp')
      rw [Finset.mem_coe]
      refine mem_stEdgesOn.mpr ⟨p, g p, hpS'.1, hpS'.2, hqS'.1, hqS'.2, hgl p hp', ?_, rfl⟩
      intro r hrP hrl ⟨h1, h2⟩
      have hrS : r ∈ S := Finset.mem_filter.mpr ⟨hrP, hrl⟩
      exact absurd (hgmin p hp' r hrS h1) (not_le.mpr h2)
    · intro p hp p' hp' heq
      have hpe : p ∈ S.erase m := Finset.mem_coe.mp hp
      have hpe' : p' ∈ S.erase m := Finset.mem_coe.mp hp'
      simp only [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso
        have a1 := hgl p hpe
        have a2 := hgl p' hpe'
        rw [← h1] at a2
        rw [h2] at a1
        exact lt_asymm a1 a2
  have := Finset.card_erase_of_mem hm
  omega

theorem st_card_edges (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane))
    (hL : ∀ l ∈ L, IsLine l) :
    (L.biUnion (stEdgesOn P)).card = ∑ l ∈ L, (stEdgesOn P l).card := by
  classical
  rw [Finset.card_biUnion]
  intro l hl l' hl' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro e he he'
  obtain ⟨p, q, hpP, hpl, hqP, hql, hlt, _, rfl⟩ := mem_stEdgesOn.mp he
  obtain ⟨p', q', hpP', hpl', hqP', hql', hlt', _, heq⟩ := mem_stEdgesOn.mp he'
  have hp' : p ∈ s(p', q') := heq ▸ Sym2.mem_mk_left p q
  have hq' : q ∈ s(p', q') := heq ▸ Sym2.mem_mk_right p q
  rw [Sym2.mem_iff] at hp' hq'
  have hpl2 : p ∈ l' := by
    rcases hp' with h | h
    · rw [h]; exact hpl'
    · rw [h]; exact hql'
  have hql2 : q ∈ l' := by
    rcases hq' with h | h
    · rw [h]; exact hpl'
    · rw [h]; exact hql'
  exact hne (st_lines_eq (hL l hl) (hL l' hl') (fun h => hlt.ne (congrArg stKey h))
    hpl hql hpl2 hql2)

open Classical in
/-- The edge set of the incidence graph. -/
noncomputable def stEdges (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)) :
    Finset (Sym2 Plane) := L.biUnion (stEdgesOn P)

theorem mem_stEdges {P : Finset Plane} {L : Finset (AffineSubspace ℝ Plane)} {e : Sym2 Plane} :
    e ∈ stEdges P L ↔ ∃ l ∈ L, e ∈ stEdgesOn P l := by
  classical
  unfold stEdges
  rw [Finset.mem_biUnion]

theorem st_seg_sub {P : Finset Plane} {l : AffineSubspace ℝ Plane} {e : Sym2 Plane} {x : Plane}
    (he : e ∈ stEdgesOn P l) (hx : x ∈ stSeg e) : x ∈ l := by
  obtain ⟨p, q, hpP, hpl, hqP, hql, hlt, _, rfl⟩ := mem_stEdgesOn.mp he
  rw [stSeg_mk] at hx
  exact (l.convex).segment_subset hpl hql hx

theorem st_drawing (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)) :
    stDrawing P (stEdges P L) := by
  constructor
  · intro e he
    obtain ⟨l, hl, he⟩ := mem_stEdges.mp he
    obtain ⟨p, q, hpP, hpl, hqP, hql, hlt, _, rfl⟩ := mem_stEdgesOn.mp he
    refine ⟨?_, ?_⟩
    · rw [Sym2.mk_isDiag_iff]; exact fun h => hlt.ne (congrArg stKey h)
    · intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with h | h
      · rw [h]; exact hpP
      · rw [h]; exact hqP
  · intro e he v hv hvs
    obtain ⟨l, hl, he⟩ := mem_stEdges.mp he
    obtain ⟨p, q, hpP, hpl, hqP, hql, hlt, hall, rfl⟩ := mem_stEdgesOn.mp he
    have hvl : v ∈ l := st_seg_sub he hvs
    rw [stSeg_mk] at hvs
    obtain ⟨h1, h2⟩ := stKey_seg hlt.le hvs
    rcases eq_or_lt_of_le h1 with h | h
    · have : p = v := stKey_inj h
      rw [← this]; exact Sym2.mem_mk_left p q
    rcases eq_or_lt_of_le h2 with h' | h'
    · have : v = q := stKey_inj h'
      rw [this]; exact Sym2.mem_mk_right p q
    exact absurd ⟨h, h'⟩ (hall v hv hvl)

theorem mem_stCrossingPairs {E : Finset (Sym2 Plane)} {ef : Sym2 Plane × Sym2 Plane} :
    ef ∈ stCrossingPairs E ↔ ef.1 ∈ E ∧ ef.2 ∈ E ∧ stCrosses ef.1 ef.2 := by
  classical
  unfold stCrossingPairs
  rw [Finset.mem_filter, Finset.mem_product, and_assoc]

theorem st_cross_unique (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane))
    (hL : ∀ l ∈ L, IsLine l) (lof : Sym2 Plane → AffineSubspace ℝ Plane)
    (hlof : ∀ e ∈ stEdges P L, lof e ∈ L ∧ e ∈ stEdgesOn P (lof e))
    {e f e' f' : Sym2 Plane} (he : e ∈ stEdges P L) (hf : f ∈ stEdges P L)
    (he' : e' ∈ stEdges P L) (hf' : f' ∈ stEdges P L)
    (hc : stCrosses e f) (hc' : stCrosses e' f') (h1 : lof e = lof e') (h2 : lof f = lof f') :
    e = e' ∧ f = f' := by
  have hD := st_drawing P L
  obtain ⟨hef, x, hxe, hxf, hxn⟩ := hc
  obtain ⟨hef', x', hxe', hxf', hxn'⟩ := hc'
  obtain ⟨hl, hel⟩ := hlof e he
  obtain ⟨hm, hfm⟩ := hlof f hf
  obtain ⟨_, hel'⟩ := hlof e' he'
  obtain ⟨_, hfm'⟩ := hlof f' hf'
  rw [← h1] at hel'
  rw [← h2] at hfm'
  have hlm : lof e ≠ lof f := by
    intro h
    rw [← h] at hfm
    exact hxn (st_edgesOn_overlap hel hfm hef hxe hxf)
  have hxl : x ∈ lof e := st_seg_sub hel hxe
  have hxm : x ∈ lof f := st_seg_sub hfm hxf
  have hxl' : x' ∈ lof e := st_seg_sub hel' hxe'
  have hxm' : x' ∈ lof f := st_seg_sub hfm' hxf'
  have hxx : x = x' := by
    by_contra hne
    exact hlm (st_lines_eq (hL _ hl) (hL _ hm) hne hxl hxl' hxm hxm')
  subst hxx
  constructor
  · by_contra hne
    obtain ⟨hxe1, _⟩ := st_edgesOn_overlap hel hel' hne hxe hxe'
    have hxP : x ∈ P := (hD.1 e he).2 x hxe1
    exact hxn ⟨hxe1, hD.2 f hf x hxP hxf⟩
  · by_contra hne
    obtain ⟨hxf1, _⟩ := st_edgesOn_overlap hfm hfm' hne hxf hxf'
    have hxP : x ∈ P := (hD.1 f hf).2 x hxf1
    exact hxn ⟨hD.2 e he x hxP hxe, hxf1⟩

open Classical in
theorem st_inc_eq (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)) :
    incidences P L = ∑ l ∈ L, (P.filter (· ∈ l)).card := by
  classical
  unfold incidences
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.card_filter]

theorem st3_incidence_graph (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane))
    (hL : ∀ l ∈ L, IsLine l) :
    ∃ E : Finset (Sym2 Plane), stDrawing P E ∧
      (incidences P L : ℝ) - L.card ≤ E.card ∧
      ((stCrossingPairs E).card : ℝ) ≤ (L.card : ℝ) ^ 2 := by
  classical
  refine ⟨stEdges P L, st_drawing P L, ?_, ?_⟩
  · have h1 := st_inc_eq P L
    have h2 : (stEdges P L).card = ∑ l ∈ L, (stEdgesOn P l).card := st_card_edges P L hL
    have h3 : incidences P L ≤ (stEdges P L).card + L.card := by
      rw [h1, h2]
      calc ∑ l ∈ L, (P.filter (· ∈ l)).card ≤ ∑ l ∈ L, ((stEdgesOn P l).card + 1) :=
            Finset.sum_le_sum (fun l _ => st_card_edgesOn_ge P l)
        _ = ∑ l ∈ L, (stEdgesOn P l).card + L.card := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    have h4 : (incidences P L : ℝ) ≤ (stEdges P L).card + L.card := by exact_mod_cast h3
    linarith
  · have hex : ∀ e ∈ stEdges P L, ∃ l, l ∈ L ∧ e ∈ stEdgesOn P l := by
      intro e he
      obtain ⟨l, hl, hel⟩ := mem_stEdges.mp he
      exact ⟨l, hl, hel⟩
    choose! lof hlofL hlofE using hex
    have hlof : ∀ e ∈ stEdges P L, lof e ∈ L ∧ e ∈ stEdgesOn P (lof e) :=
      fun e he => ⟨hlofL e he, hlofE e he⟩
    have hc : (stCrossingPairs (stEdges P L)).card ≤ (L ×ˢ L).card := by
      apply Finset.card_le_card_of_injOn (fun ef : Sym2 Plane × Sym2 Plane => (lof ef.1, lof ef.2))
      · intro ef hef
        have hef' : ef ∈ stCrossingPairs (stEdges P L) := by simpa using hef
        obtain ⟨h1, h2, _⟩ := mem_stCrossingPairs.mp hef'
        rw [Finset.mem_coe, Finset.mem_product]
        exact ⟨hlofL _ h1, hlofL _ h2⟩
      · intro ef hef ef' hef' heq
        have hef1 : ef ∈ stCrossingPairs (stEdges P L) := by simpa using hef
        have hef2 : ef' ∈ stCrossingPairs (stEdges P L) := by simpa using hef'
        obtain ⟨a1, a2, a3⟩ := mem_stCrossingPairs.mp hef1
        obtain ⟨b1, b2, b3⟩ := mem_stCrossingPairs.mp hef2
        simp only [Prod.mk.injEq] at heq
        obtain ⟨r1, r2⟩ := st_cross_unique P L hL lof hlof a1 a2 b1 b2 a3 b3 heq.1 heq.2
        exact Prod.ext r1 r2
    rw [Finset.card_product] at hc
    have : (stCrossingPairs (stEdges P L)).card ≤ L.card * L.card := hc
    have h5 : ((stCrossingPairs (stEdges P L)).card : ℝ) ≤ (L.card : ℝ) * (L.card : ℝ) := by
      exact_mod_cast this
    nlinarith

theorem stDrawing_mono {V : Finset Plane} {E E' : Finset (Sym2 Plane)} (hD : stDrawing V E)
    (h : E' ⊆ E) : stDrawing V E' :=
  ⟨fun e he => hD.1 e (h he), fun e he => hD.2 e (h he)⟩

theorem stCrossingPairs_mono {E E' : Finset (Sym2 Plane)} (h : E' ⊆ E) :
    stCrossingPairs E' ⊆ stCrossingPairs E := by
  intro ef hef
  obtain ⟨a, b, c⟩ := mem_stCrossingPairs.mp hef
  exact mem_stCrossingPairs.mpr ⟨h a, h b, c⟩

/-- ST2a: deleting one edge per crossing pair, from the planar bound. -/
theorem st2a
    (h1 : ∀ (V : Finset Plane) (E : Finset (Sym2 Plane)), stDrawing V E →
      stCrossingPairs E = ∅ → E.card ≤ 4 * V.card)
    (V : Finset Plane) (E : Finset (Sym2 Plane)) (hD : stDrawing V E) :
    E.card ≤ 4 * V.card + (stCrossingPairs E).card := by
  classical
  induction E using Finset.strongInduction with
  | H E ih =>
    by_cases hcr : stCrossingPairs E = ∅
    · have := h1 V E hD hcr
      omega
    · obtain ⟨⟨e, f⟩, hef⟩ := Finset.nonempty_iff_ne_empty.mpr hcr
      have hef' := mem_stCrossingPairs.mp hef
      have hsub : E.erase e ⊂ E := Finset.erase_ssubset hef'.1
      have hD' : stDrawing V (E.erase e) := stDrawing_mono hD (Finset.erase_subset _ _)
      have h2 := ih (E.erase e) hsub hD'
      have hcr' : (stCrossingPairs (E.erase e)).card < (stCrossingPairs E).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (stCrossingPairs_mono (Finset.erase_subset _ _))]
        refine ⟨(e, f), hef, fun hmem => ?_⟩
        have := (mem_stCrossingPairs.mp hmem).1
        simp at this
      have hcard : (E.erase e).card + 1 = E.card := Finset.card_erase_add_one hef'.1
      omega

/-- Crossing edges of a drawing have no common endpoint. -/
theorem st_cross_disjoint {V : Finset Plane} {E : Finset (Sym2 Plane)} (hD : stDrawing V E)
    {e f : Sym2 Plane} (he : e ∈ E) (hf : f ∈ E) (hc : stCrosses e f) {v : Plane}
    (hve : v ∈ e) (hvf : v ∈ f) : False := by
  obtain ⟨hne, x, hxe, hxf, hxn⟩ := hc
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp hve
  obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.mp hvf
  have hb : b ≠ v := by
    have := (hD.1 _ he).1
    rw [Sym2.mk_isDiag_iff] at this
    exact fun h => this h.symm
  have hc' : c ≠ v := by
    have := (hD.1 _ hf).1
    rw [Sym2.mk_isDiag_iff] at this
    exact fun h => this h.symm
  have hbV : b ∈ V := (hD.1 _ he).2 b (Sym2.mem_mk_right _ _)
  have hcV : c ∈ V := (hD.1 _ hf).2 c (Sym2.mem_mk_right _ _)
  rw [stSeg_mk] at hxe hxf
  have hxv : x ≠ v := by
    intro h
    exact hxn ⟨h ▸ Sym2.mem_mk_left _ _, h ▸ Sym2.mem_mk_left _ _⟩
  rw [segment_eq_image'] at hxe hxf
  obtain ⟨s, ⟨hs0, hs1⟩, hsx⟩ := hxe
  obtain ⟨t, ⟨ht0, ht1⟩, htx⟩ := hxf
  simp only at hsx htx
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hs0 with h | h
    · exfalso; apply hxv; rw [← hsx, ← h]; simp
    · exact h
  have htpos : 0 < t := by
    rcases eq_or_lt_of_le ht0 with h | h
    · exfalso; apply hxv; rw [← htx, ← h]; simp
    · exact h
  have key : s • (b - v) = t • (c - v) := by
    have : v + s • (b - v) = v + t • (c - v) := by rw [hsx, htx]
    exact add_left_cancel this
  rcases le_total t s with hts | hst
  · -- b ∈ segment v c
    have hbseg : b ∈ stSeg s(v, c) := by
      rw [stSeg_mk, segment_eq_image']
      refine ⟨t / s, ⟨by positivity, (div_le_one hspos).mpr hts⟩, ?_⟩
      have h2 : b - v = (t / s) • (c - v) := by
        have := congrArg (fun z => s⁻¹ • z) key
        simp only [smul_smul, inv_mul_cancel₀ hspos.ne', one_smul] at this
        rw [this, div_eq_inv_mul]
      simp only
      rw [← h2]; abel
    have := hD.2 _ hf b hbV hbseg
    rw [Sym2.mem_iff] at this
    rcases this with h | h
    · exact hb h
    · exact hne (by rw [h])
  · have hcseg : c ∈ stSeg s(v, b) := by
      rw [stSeg_mk, segment_eq_image']
      refine ⟨s / t, ⟨by positivity, (div_le_one htpos).mpr hst⟩, ?_⟩
      have h2 : c - v = (s / t) • (b - v) := by
        have := congrArg (fun z => t⁻¹ • z) key.symm
        simp only [smul_smul, inv_mul_cancel₀ htpos.ne', one_smul] at this
        rw [this, div_eq_inv_mul]
      simp only
      rw [← h2]; abel
    have := hD.2 _ he c hcV hcseg
    rw [Sym2.mem_iff] at this
    rcases this with h | h
    · exact hc' h
    · exact hne (by rw [h])

theorem st_weight (V S : Finset Plane) (hS : S ⊆ V) (p : ℝ) :
    ∑ U ∈ V.powerset, (if S ⊆ U then p ^ U.card * (1 - p) ^ (V.card - U.card) else 0)
      = p ^ S.card := by
  classical
  have h := Finset.prod_add (fun _ : Plane => p)
    (fun i => if i ∈ S then (0 : ℝ) else 1 - p) V
  have hL : ∏ i ∈ V, (p + (if i ∈ S then (0 : ℝ) else 1 - p)) = p ^ S.card := by
    have : ∀ i ∈ V, (p + (if i ∈ S then (0 : ℝ) else 1 - p)) = if i ∈ S then p else 1 := by
      intro i _
      split_ifs <;> ring
    rw [Finset.prod_congr rfl this, ← Finset.prod_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hS, Finset.prod_const]
  rw [hL] at h
  rw [h]
  refine Finset.sum_congr rfl (fun U hU => ?_)
  have hUV : U ⊆ V := Finset.mem_powerset.mp hU
  rw [Finset.prod_const]
  by_cases hSU : S ⊆ U
  · rw [if_pos hSU]
    have : ∏ i ∈ V \ U, (if i ∈ S then (0 : ℝ) else 1 - p) = (1 - p) ^ (V.card - U.card) := by
      rw [Finset.prod_congr rfl (g := fun _ => 1 - p), Finset.prod_const,
        Finset.card_sdiff_of_subset hUV]
      intro i hi
      have hiU : i ∉ U := (Finset.mem_sdiff.mp hi).2
      have : i ∉ S := fun h => hiU (hSU h)
      simp [this]
    rw [this]
  · rw [if_neg hSU]
    obtain ⟨i, hiS, hiU⟩ := Finset.not_subset.mp hSU
    have : ∏ i ∈ V \ U, (if i ∈ S then (0 : ℝ) else 1 - p) = 0 := by
      apply Finset.prod_eq_zero (i := i)
      · exact Finset.mem_sdiff.mpr ⟨hS hiS, hiU⟩
      · simp [hiS]
    rw [this, mul_zero]

theorem st_expect {ι : Type*} (V : Finset Plane) (I : Finset ι) (S : ι → Finset Plane)
    (hS : ∀ i ∈ I, S i ⊆ V) (p : ℝ) :
    ∑ U ∈ V.powerset, p ^ U.card * (1 - p) ^ (V.card - U.card) *
        ((I.filter (fun i => S i ⊆ U)).card : ℝ)
      = ∑ i ∈ I, p ^ (S i).card := by
  classical
  have h1 : ∀ U : Finset Plane, ((I.filter (fun i => S i ⊆ U)).card : ℝ)
      = ∑ i ∈ I, if S i ⊆ U then (1 : ℝ) else 0 := by
    intro U
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← st_weight V (S i) (hS i hi) p]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  split_ifs <;> simp

open Classical in
/-- The set of endpoints of an edge inside `V`. -/
noncomputable def stVt (V : Finset Plane) (e : Sym2 Plane) : Finset Plane := V.filter (· ∈ e)

theorem stVt_card {V : Finset Plane} {E : Finset (Sym2 Plane)} (hD : stDrawing V E)
    {e : Sym2 Plane} (he : e ∈ E) : (stVt V e).card = 2 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      have := (hD.1 _ he).1
      rwa [Sym2.mk_isDiag_iff] at this
    have haV : a ∈ V := (hD.1 _ he).2 a (Sym2.mem_mk_left _ _)
    have hbV : b ∈ V := (hD.1 _ he).2 b (Sym2.mem_mk_right _ _)
    have : stVt V s(a, b) = {a, b} := by
      ext x
      simp only [stVt, Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with rfl | rfl <;> assumption
    rw [this, Finset.card_pair hab]

theorem stVt_subset {V : Finset Plane} (e : Sym2 Plane) : stVt V e ⊆ V :=
  Finset.filter_subset _ _

theorem stVt_subset_iff {V : Finset Plane} {E : Finset (Sym2 Plane)} (hD : stDrawing V E)
    {e : Sym2 Plane} (he : e ∈ E) (U : Finset Plane) :
    stVt V e ⊆ U ↔ ∀ x ∈ e, x ∈ U := by
  constructor
  · intro h x hx
    exact h (Finset.mem_filter.mpr ⟨(hD.1 e he).2 x hx, hx⟩)
  · intro h x hx
    exact h x (Finset.mem_filter.mp hx).2

open Classical in
theorem stDrawing_induced {V U : Finset Plane} {E : Finset (Sym2 Plane)} (hD : stDrawing V E)
    (hUV : U ⊆ V) :
    stDrawing U (E.filter (fun e => ∀ x ∈ e, x ∈ U)) := by
  classical
  refine ⟨fun e he => ?_, fun e he v hv hvs => ?_⟩
  · obtain ⟨heE, hU⟩ := Finset.mem_filter.mp he
    exact ⟨(hD.1 e heE).1, hU⟩
  · obtain ⟨heE, _⟩ := Finset.mem_filter.mp he
    exact hD.2 e heE v (hUV hv) hvs

open Classical in
theorem st2_aux
    (h1 : ∀ (V : Finset Plane) (E : Finset (Sym2 Plane)), stDrawing V E →
      stCrossingPairs E = ∅ → E.card ≤ 4 * V.card)
    (V : Finset Plane) (E : Finset (Sym2 Plane)) (hD : stDrawing V E) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ 2 * (E.card : ℝ) ≤ 4 * (p * (V.card : ℝ)) + p ^ 4 * ((stCrossingPairs E).card : ℝ) := by
  obtain ⟨w, hw⟩ : ∃ w : Finset Plane → ℝ, ∀ U, w U = p ^ U.card * (1 - p) ^ (V.card - U.card) :=
    ⟨_, fun _ => rfl⟩
  have hw0 : ∀ U, 0 ≤ w U := fun U => by
    rw [hw]; exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  have hpt : ∀ U ∈ V.powerset,
      w U * ((E.filter (fun e => stVt V e ⊆ U)).card : ℝ)
        ≤ 4 * (w U * ((V.filter (fun x => ({x} : Finset Plane) ⊆ U)).card : ℝ))
          + w U * (((stCrossingPairs E).filter
              (fun ef => stVt V ef.1 ∪ stVt V ef.2 ⊆ U)).card : ℝ) := by
    intro U hU
    have hUV : U ⊆ V := Finset.mem_powerset.mp hU
    have hDU := stDrawing_induced hD hUV
    have ha := st2a h1 U _ hDU
    have e1 : (E.filter (fun e => ∀ x ∈ e, x ∈ U)) = E.filter (fun e => stVt V e ⊆ U) := by
      apply Finset.filter_congr
      intro e he
      exact (stVt_subset_iff hD he U).symm
    have e2 : V.filter (fun x => ({x} : Finset Plane) ⊆ U) = U := by
      ext x
      simp only [Finset.mem_filter, Finset.singleton_subset_iff]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hUV h, h⟩
    have e3 : stCrossingPairs (E.filter (fun e => ∀ x ∈ e, x ∈ U))
        = (stCrossingPairs E).filter (fun ef => stVt V ef.1 ∪ stVt V ef.2 ⊆ U) := by
      ext ⟨e, f⟩
      simp only [mem_stCrossingPairs, Finset.mem_filter, Finset.union_subset_iff]
      constructor
      · rintro ⟨⟨he, hu1⟩, ⟨hf, hu2⟩, hc⟩
        exact ⟨⟨he, hf, hc⟩, (stVt_subset_iff hD he U).mpr hu1, (stVt_subset_iff hD hf U).mpr hu2⟩
      · rintro ⟨⟨he, hf, hc⟩, h1', h2'⟩
        exact ⟨⟨he, (stVt_subset_iff hD he U).mp h1'⟩, ⟨hf, (stVt_subset_iff hD hf U).mp h2'⟩, hc⟩
    rw [e3, e1] at ha
    rw [e2]
    have ha' : ((E.filter (fun e => stVt V e ⊆ U)).card : ℝ) ≤ 4 * (U.card : ℝ)
        + (((stCrossingPairs E).filter
            (fun ef => stVt V ef.1 ∪ stVt V ef.2 ⊆ U)).card : ℝ) := by
      exact_mod_cast ha
    calc w U * ((E.filter (fun e => stVt V e ⊆ U)).card : ℝ)
        ≤ w U * (4 * (U.card : ℝ) + (((stCrossingPairs E).filter
            (fun ef => stVt V ef.1 ∪ stVt V ef.2 ⊆ U)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left ha' (hw0 U)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have eA := st_expect V E (stVt V) (fun e _ => stVt_subset e) p
  have eB := st_expect V V (fun x => ({x} : Finset Plane))
    (fun x hx => Finset.singleton_subset_iff.mpr hx) p
  have eC := st_expect V (stCrossingPairs E) (fun ef => stVt V ef.1 ∪ stVt V ef.2)
    (fun ef _ => Finset.union_subset (stVt_subset _) (stVt_subset _)) p
  simp_rw [hw] at hsum
  rw [eA, eB, eC] at hsum
  have sA : ∑ e ∈ E, p ^ (stVt V e).card = (E.card : ℝ) * p ^ 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => p ^ 2) (fun e he => by rw [stVt_card hD he])]
    simp
  have sB : ∑ x ∈ V, p ^ (({x} : Finset Plane)).card = (V.card : ℝ) * p := by
    simp
  have sC : ∑ ef ∈ stCrossingPairs E, p ^ (stVt V ef.1 ∪ stVt V ef.2).card
      = ((stCrossingPairs E).card : ℝ) * p ^ 4 := by
    rw [Finset.sum_congr rfl (g := fun _ => p ^ 4)]
    · simp
    · intro ef hef
      obtain ⟨he, hf, hc⟩ := mem_stCrossingPairs.mp hef
      have hdis : Disjoint (stVt V ef.1) (stVt V ef.2) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact st_cross_disjoint hD he hf hc (Finset.mem_filter.mp hx1).2
          (Finset.mem_filter.mp hx2).2
      rw [Finset.card_union_of_disjoint hdis, stVt_card hD he, stVt_card hD hf]
  rw [sA, sB, sC] at hsum
  linarith

/-- ST2: crossing lemma for straight-line drawings (ordered pairs), assuming ST1 (`|E| ≤ 4|V|`). -/
theorem st2_crossing_lemma
    (h1 : ∀ (V : Finset Plane) (E : Finset (Sym2 Plane)), stDrawing V E →
      stCrossingPairs E = ∅ → E.card ≤ 4 * V.card)
    (V : Finset Plane) (E : Finset (Sym2 Plane)) (hD : stDrawing V E)
    (hV : 8 * V.card ≤ E.card) :
    (E.card : ℝ) ^ 3 / (128 * (V.card : ℝ) ^ 2) ≤ (stCrossingPairs E).card := by
  by_cases hv : V.card = 0
  · have hV0 : V = ∅ := Finset.card_eq_zero.mp hv
    have hE0 : E = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have := (hD.1 _ he).2 a (Sym2.mem_mk_left _ _)
        rw [hV0] at this
        simp at this
    rw [hE0, hv]
    simp
  have hvpos : (0 : ℝ) < V.card := by exact_mod_cast Nat.pos_of_ne_zero hv
  have hepos : (0 : ℝ) < E.card := by
    have : 0 < E.card := by omega
    exact_mod_cast this
  have h4 : 8 * (V.card : ℝ) ≤ E.card := by exact_mod_cast hV
  set e : ℝ := (E.card : ℝ) with he_def
  set v : ℝ := (V.card : ℝ) with hv_def
  set c : ℝ := ((stCrossingPairs E).card : ℝ) with hc_def
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  set p : ℝ := 8 * v / e with hp_def
  have hppos : 0 < p := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one hepos]; exact h4
  have hpe : p * e = 8 * v := by
    rw [hp_def]; field_simp
  have key := st2_aux h1 V E hD p hppos.le hp1
  have key' : 4 * v ≤ p ^ 3 * c := by
    have h2 : p * (8 * v) ≤ p * (4 * v + p ^ 3 * c) := by
      have : p ^ 2 * e = p * (8 * v) := by rw [← hpe]; ring
      nlinarith
    have h3 := le_of_mul_le_mul_left h2 hppos
    nlinarith
  have key'' : e ^ 3 ≤ 128 * v ^ 2 * c := by
    have h5 : 4 * v * e ^ 3 ≤ (p * e) ^ 3 * c := by
      calc 4 * v * e ^ 3 ≤ p ^ 3 * c * e ^ 3 := mul_le_mul_of_nonneg_right key' (by positivity)
        _ = (p * e) ^ 3 * c := by ring
    rw [hpe] at h5
    have h6 : 4 * v * e ^ 3 ≤ 4 * v * (128 * v ^ 2 * c) := by nlinarith
    exact le_of_mul_le_mul_left h6 (by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- cross product of two plane vectors -/
def stCross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

/-- `w` lies strictly inside the open cone spanned by `u` and `v`. -/
def stInCone (u v w : Plane) : Prop := ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ w = α • u + β • v

/-- The segment `uw` is "free" for `M`: proper, no vertex in its relative interior, crossed by no edge. -/
def stFree (V : Finset Plane) (M : Finset (Sym2 Plane)) (u w : Plane) : Prop :=
  u ∈ V ∧ w ∈ V ∧ u ≠ w ∧ (∀ x ∈ V, x ∈ segment ℝ u w → x = u ∨ x = w) ∧
    ∀ g ∈ M, ¬ stCrosses s(u, w) g


theorem stCrosses_symm {e f : Sym2 Plane} (h : stCrosses e f) : stCrosses f e := by
  obtain ⟨hne, x, hx1, hx2, hx3⟩ := h
  exact ⟨fun h => hne h.symm, x, hx2, hx1, fun h' => hx3 ⟨h'.2, h'.1⟩⟩

/-- ST1a: every noncrossing drawing extends to a maximal one. -/
theorem st1a_maximal (V : Finset Plane) (E : Finset (Sym2 Plane)) (hD : stDrawing V E)
    (hnc : stCrossingPairs E = ∅) :
    ∃ M : Finset (Sym2 Plane), E ⊆ M ∧ stDrawing V M ∧ stCrossingPairs M = ∅ ∧
      ∀ u w, stFree V M u w → s(u, w) ∈ M := by
  classical
  have hEsub : E ⊆ V.sym2 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [Finset.mk_mem_sym2_iff]
      exact ⟨(hD.1 _ he).2 a (Sym2.mem_mk_left _ _), (hD.1 _ he).2 b (Sym2.mem_mk_right _ _)⟩
  let 𝒞 : Finset (Finset (Sym2 Plane)) :=
    V.sym2.powerset.filter (fun M => E ⊆ M ∧ stDrawing V M ∧ stCrossingPairs M = ∅)
  have hE𝒞 : E ∈ 𝒞 := by
    simp only [𝒞, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hEsub, Finset.Subset.refl _, hD, hnc⟩
  obtain ⟨M, hM𝒞, hMmax⟩ := Finset.exists_max_image 𝒞 Finset.card ⟨E, hE𝒞⟩
  simp only [𝒞, Finset.mem_filter, Finset.mem_powerset] at hM𝒞
  obtain ⟨hMsub, hEM, hDM, hncM⟩ := hM𝒞
  refine ⟨M, hEM, hDM, hncM, fun u w hfree => ?_⟩
  by_contra hnot
  obtain ⟨huV, hwV, huw, hvert, hfc⟩ := hfree
  have hM'𝒞 : insert s(u, w) M ∈ 𝒞 := by
    simp only [𝒞, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, hEM.trans (Finset.subset_insert _ _), ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · rw [Finset.mk_mem_sym2_iff]; exact ⟨huV, hwV⟩
      · exact hMsub he
    · constructor
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · refine ⟨?_, ?_⟩
          · rw [Sym2.mk_isDiag_iff]; exact huw
          · intro x hx
            rcases Sym2.mem_iff.mp hx with rfl | rfl
            · exact huV
            · exact hwV
        · exact hDM.1 e he
      · intro e he v hv hvs
        rcases Finset.mem_insert.mp he with rfl | he
        · rw [stSeg_mk] at hvs
          rcases hvert v hv hvs with rfl | rfl
          · exact Sym2.mem_mk_left _ _
          · exact Sym2.mem_mk_right _ _
        · exact hDM.2 e he v hv hvs
    · rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨e, f⟩ hef
      obtain ⟨he, hf, hc⟩ := mem_stCrossingPairs.mp hef
      simp only at he hf hc
      rcases Finset.mem_insert.mp he with rfl | he
      · rcases Finset.mem_insert.mp hf with rfl | hf
        · exact hc.1 rfl
        · exact hfc f hf hc
      · rcases Finset.mem_insert.mp hf with rfl | hf
        · exact hfc e he (stCrosses_symm hc)
        · have : (e, f) ∈ stCrossingPairs M := mem_stCrossingPairs.mpr ⟨he, hf, hc⟩
          rw [hncM] at this
          exact absurd this (Finset.notMem_empty _)
  have := hMmax _ hM'𝒞
  rw [Finset.card_insert_of_notMem hnot] at this
  omega


/-! ### ST1c : counting -/

/-- the linear functional `x + ε y` -/
def stF (ε : ℝ) (p : Plane) : ℝ := p 0 + ε * p 1

/-- slope of a vector in the sheared coordinates `(stF, y)` -/
noncomputable def stK (ε : ℝ) (u : Plane) : ℝ := u 1 / stF ε u

theorem stF_sub (ε : ℝ) (a m : Plane) : stF ε (a - m) = stF ε a - stF ε m := by
  simp [stF]; ring

theorem stF_add (ε : ℝ) (a m : Plane) : stF ε (a + m) = stF ε a + stF ε m := by
  simp [stF]; ring

theorem stF_smul (ε c : ℝ) (a : Plane) : stF ε (c • a) = c * stF ε a := by
  simp [stF]; ring

theorem stCross_F (ε : ℝ) (u v : Plane) : stCross u v = stF ε u * v 1 - u 1 * stF ε v := by
  unfold stCross stF; ring

theorem stCross_slope (ε : ℝ) {u v : Plane} (hu : stF ε u ≠ 0) (hv : stF ε v ≠ 0) :
    stCross u v = stF ε u * stF ε v * (stK ε v - stK ε u) := by
  rw [stCross_F ε u v]
  unfold stK
  field_simp

/-- vector with zero `stF` and zero second coordinate vanishes -/
theorem st_vec_zero (ε : ℝ) {w : Plane} (h1 : stF ε w = 0) (h2 : w 1 = 0) : w = 0 := by
  have h0 : w 0 = 0 := by unfold stF at h1; rw [h2] at h1; linarith
  ext i
  fin_cases i
  · exact h0
  · exact h2

/-- parallel vectors: `F(u) v = F(v) u` when the cross product vanishes -/
theorem st_parallel (ε : ℝ) {u v : Plane} (h : stCross u v = 0) :
    stF ε u • v = stF ε v • u := by
  apply sub_eq_zero.mp
  apply st_vec_zero ε
  · simp [stF_sub, stF_smul]; ring
  · have := stCross_F ε u v
    simp
    linarith

theorem st_vertex_on_seg {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    {p q x : Plane} (he : s(p, q) ∈ M) (hx : x ∈ V) (hxs : x ∈ segment ℝ p q) : x = p ∨ x = q := by
  have := hD.2 _ he x hx (by rw [stSeg_mk]; exact hxs)
  exact Sym2.mem_iff.mp this

/-- two distinct neighbours of `m` on the same side with the same slope do not exist -/
theorem st_slope_inj {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M) (ε : ℝ)
    {m a b : Plane} (ha : a ∈ V) (hb : b ∈ V) (hma : s(m, a) ∈ M) (hmb : s(m, b) ∈ M)
    (hsame : 0 < stF ε (a - m) * stF ε (b - m))
    (hk : stK ε (a - m) = stK ε (b - m)) : a = b := by
  have hFa' : stF ε (a - m) ≠ 0 := left_ne_zero_of_mul hsame.ne'
  have hFb' : stF ε (b - m) ≠ 0 := right_ne_zero_of_mul hsame.ne'
  have hcr : stCross (a - m) (b - m) = 0 := by
    rw [stCross_slope ε hFa' hFb', hk]; ring
  have hpar := st_parallel ε hcr
  set u := a - m with hu
  set v := b - m with hv
  by_contra hne
  have hlam : 0 < stF ε v / stF ε u := by
    have : stF ε v / stF ε u = (stF ε u * stF ε v) / (stF ε u) ^ 2 := by field_simp
    rw [this]; positivity
  rcases le_or_gt (stF ε v / stF ε u) 1 with hle | hgt
  · have hv' : v = (stF ε v / stF ε u) • u := by
      rw [div_eq_inv_mul, mul_smul, ← hpar, smul_smul, inv_mul_cancel₀ hFa', one_smul]
    have hbs : b ∈ segment ℝ m a := by
      rw [segment_eq_image']
      refine ⟨stF ε v / stF ε u, ⟨hlam.le, hle⟩, ?_⟩
      simp only
      rw [← hv', hv]; abel
    rcases st_vertex_on_seg hD hma hb hbs with h | h
    · apply hFb'; rw [hv, h]; simp [stF]
    · exact hne h.symm
  · have hu' : u = (stF ε u / stF ε v) • v := by
      rw [div_eq_inv_mul, mul_smul, hpar, smul_smul, inv_mul_cancel₀ hFb', one_smul]
    have hμ : stF ε u / stF ε v ≤ 1 := by
      have : stF ε u / stF ε v = (stF ε v / stF ε u)⁻¹ := by rw [inv_div]
      rw [this]; exact inv_le_one_of_one_le₀ hgt.le
    have hμ0 : 0 ≤ stF ε u / stF ε v := by
      have : stF ε u / stF ε v = (stF ε u * stF ε v) / (stF ε v) ^ 2 := by field_simp
      rw [this]; positivity
    have has : a ∈ segment ℝ m b := by
      rw [segment_eq_image']
      refine ⟨stF ε u / stF ε v, ⟨hμ0, hμ⟩, ?_⟩
      simp only
      rw [← hu', hu]; abel
    rcases st_vertex_on_seg hD hmb ha has with h | h
    · apply hFa'; rw [hu, h]; simp [stF]
    · exact hne h

theorem st_noncross {M : Finset (Sym2 Plane)} (hnc : stCrossingPairs M = ∅) {e f : Sym2 Plane}
    (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) {z : Plane} (hze : z ∈ stSeg e) (hzf : z ∈ stSeg f) :
    z ∈ e ∧ z ∈ f := by
  by_contra h
  have : (e, f) ∈ stCrossingPairs M := mem_stCrossingPairs.mpr ⟨he, hf, hne, z, hze, hzf, h⟩
  rw [hnc] at this
  exact absurd this (Finset.notMem_empty _)

theorem st_cross_comb (u v : Plane) (α β γ δ : ℝ) (h : α • u + β • v = γ • u + δ • v)
    (hcr : stCross u v ≠ 0) : α = γ ∧ β = δ := by
  have h0 := congrArg (fun w : Plane => w 0) h
  have h1 := congrArg (fun w : Plane => w 1) h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
  unfold stCross at hcr
  constructor
  · have : (α - γ) * (u 0 * v 1 - u 1 * v 0) = 0 := by
      linear_combination (v 1) * h0 - (v 0) * h1
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hcr
  · have : (β - δ) * (u 0 * v 1 - u 1 * v 0) = 0 := by
      linear_combination (u 0) * h1 - (u 1) * h0
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hcr

/-- Cramer's rule identity. -/
theorem st_cramer (u v w : Plane) :
    stCross u v • w = stCross w v • u + stCross u w • v := by
  ext i
  fin_cases i <;> simp [stCross] <;> ring

theorem st_cone_of_cross {u v w : Plane} (h1 : 0 < stCross u v * stCross w v)
    (h2 : 0 < stCross u v * stCross u w) : stInCone u v w := by
  have hcr : stCross u v ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  refine ⟨stCross w v / stCross u v, stCross u w / stCross u v, ?_, ?_, ?_⟩
  · rw [div_pos_iff]
    rcases lt_or_gt_of_ne hcr with h | h
    · right; constructor
      · nlinarith
      · exact h
    · left; constructor
      · nlinarith
      · exact h
  · rw [div_pos_iff]
    rcases lt_or_gt_of_ne hcr with h | h
    · right; constructor
      · nlinarith
      · exact h
    · left; constructor
      · nlinarith
      · exact h
  · have hc := st_cramer u v w
    calc w = (stCross u v)⁻¹ • (stCross u v • w) := by
          rw [smul_smul, inv_mul_cancel₀ hcr, one_smul]
      _ = (stCross u v)⁻¹ • (stCross w v • u + stCross u w • v) := by rw [hc]
      _ = _ := by rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

/-- Freeness at a corner: in an empty triangle with all three sides in `M`, no edge of `M` at the
corner `p` points strictly inside the cone. -/
theorem st_free_corner {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    (hnc : stCrossingPairs M = ∅) {p q r : Plane}
    (hpq : s(p, q) ∈ M) (hpr : s(p, r) ∈ M) (hqr : s(q, r) ∈ M)
    (hcr : stCross (q - p) (r - p) ≠ 0)
    (hempty : ∀ w ∈ V, w ∈ convexHull ℝ ({p, q, r} : Set Plane) → w = p ∨ w = q ∨ w = r)
    {x : Plane} (hx : s(p, x) ∈ M) : ¬ stInCone (q - p) (r - p) (x - p) := by
  rintro ⟨α, β, hα, hβ, hxe⟩
  have hxV : x ∈ V := (hD.1 _ hx).2 x (Sym2.mem_mk_right _ _)
  set u := q - p with hu
  set v := r - p with hv
  have hxdef : x = p + (α • u + β • v) := by rw [← hxe]; abel
  have hσ : 0 < α + β := by linarith
  have hb : (α / (α + β)) • q + (β / (α + β)) • r ∈ segment ℝ q r :=
    ⟨α / (α + β), β / (α + β), by positivity, by positivity, by field_simp, rfl⟩
  have hzeq : (α / (α + β)) • q + (β / (α + β)) • r = p + ((α / (α + β)) • u + (β / (α + β)) • v) := by
    rw [hu, hv]
    ext i
    fin_cases i <;> simp <;> field_simp <;> ring
  rcases le_or_gt (α + β) 1 with hle | hgt
  · -- x lies in the closed triangle
    have hxh : x ∈ convexHull ℝ ({p, q, r} : Set Plane) := by
      rw [convexHull_insert (by simp : ({q, r} : Set Plane).Nonempty), convexHull_pair,
        mem_convexJoin]
      refine ⟨p, Set.mem_singleton p, (α / (α + β)) • q + (β / (α + β)) • r, hb, ?_⟩
      refine ⟨1 - (α + β), α + β, by linarith, hσ.le, by ring, ?_⟩
      rw [hzeq, hxdef]
      ext i
      fin_cases i <;> simp <;> field_simp <;> ring
    rcases hempty x hxV hxh with h | h | h
    · -- x = p
      have h0 : α • u + β • v = (0 : ℝ) • u + (0 : ℝ) • v := by
        have : x - p = 0 := by rw [h]; simp
        rw [← hxe, this]; simp
      exact hα.ne' (st_cross_comb u v α β 0 0 h0 hcr).1
    · have h0 : α • u + β • v = (1 : ℝ) • u + (0 : ℝ) • v := by
        rw [← hxe, h]; simp [hu]
      exact hβ.ne' (st_cross_comb u v α β 1 0 h0 hcr).2
    · have h0 : α • u + β • v = (0 : ℝ) • u + (1 : ℝ) • v := by
        rw [← hxe, h]; simp [hv]
      exact hα.ne' (st_cross_comb u v α β 0 1 h0 hcr).1
  · -- the ray from p through x crosses the side qr
    have hzx : (α / (α + β)) • q + (β / (α + β)) • r ∈ segment ℝ p x := by
      refine ⟨1 - 1 / (α + β), 1 / (α + β), ?_, by positivity, by ring, ?_⟩
      · rw [sub_nonneg, div_le_one hσ]; exact hgt.le
      · rw [hzeq, hxdef]
        ext i
        fin_cases i <;> simp <;> field_simp <;> ring
    have hne : s(p, x) ≠ s(q, r) := by
      intro h
      have : p ∈ s(q, r) := by rw [← h]; exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.mp this with h' | h'
      · apply hcr
        have : u = 0 := by rw [hu, h']; simp
        simp [stCross, this]
      · apply hcr
        have : v = 0 := by rw [hv, h']; simp
        simp [stCross, this]
    obtain ⟨hz1, hz2⟩ := st_noncross hnc hx hqr hne (z := (α / (α + β)) • q + (β / (α + β)) • r)
      (by rw [stSeg_mk]; exact hzx) (by rw [stSeg_mk]; exact hb)
    rcases Sym2.mem_iff.mp hz1 with h | h
    · -- z = p
      have h0 : (α / (α + β)) • u + (β / (α + β)) • v = (0 : ℝ) • u + (0 : ℝ) • v := by
        have : p + ((α / (α + β)) • u + (β / (α + β)) • v) = p := by rw [← hzeq, h]
        have h2 := add_left_cancel (this.trans (add_zero p).symm)
        rw [h2]; simp
      have := (st_cross_comb u v _ _ 0 0 h0 hcr).1
      have : α / (α + β) > 0 := by positivity
      linarith
    · -- z = x
      have h0 : (α / (α + β)) • u + (β / (α + β)) • v = α • u + β • v := by
        have : p + ((α / (α + β)) • u + (β / (α + β)) • v) = p + (α • u + β • v) := by
          rw [← hzeq, h, ← hxdef]
        exact add_left_cancel this
      have h1 := (st_cross_comb u v _ _ α β h0 hcr).1
      field_simp at h1
      linarith

theorem st_sgn_pos {c b : ℝ} (hc : 0 < c) : (0 < c * b ↔ 0 < b) ∧ (c * b < 0 ↔ b < 0) := by
  refine ⟨⟨fun h => ?_, fun h => mul_pos hc h⟩, ⟨fun h => ?_, fun h => mul_neg_of_pos_of_neg hc h⟩⟩
  · by_contra hb; push Not at hb; nlinarith
  · by_contra hb; push Not at hb; nlinarith

theorem st_sgn_neg {c b : ℝ} (hc : c < 0) : (0 < c * b ↔ b < 0) ∧ (c * b < 0 ↔ 0 < b) := by
  refine ⟨⟨fun h => ?_, fun h => mul_pos_of_neg_of_neg hc h⟩,
    ⟨fun h => ?_, fun h => mul_neg_of_neg_of_pos hc h⟩⟩
  · by_contra hb; push Not at hb; nlinarith
  · by_contra hb; push Not at hb; nlinarith

theorem st_cross_LL (ε : ℝ) {u w : Plane} (hu : stF ε u < 0) (hw : stF ε w < 0) :
    (0 < stCross u w ↔ stK ε u < stK ε w) ∧ (stCross u w < 0 ↔ stK ε w < stK ε u) := by
  rw [stCross_slope ε hu.ne hw.ne]
  have hc : 0 < stF ε u * stF ε w := mul_pos_of_neg_of_neg hu hw
  have := st_sgn_pos (b := stK ε w - stK ε u) hc
  rw [this.1, this.2, sub_pos, sub_neg]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem st_cross_RR (ε : ℝ) {u w : Plane} (hu : 0 < stF ε u) (hw : 0 < stF ε w) :
    (0 < stCross u w ↔ stK ε u < stK ε w) ∧ (stCross u w < 0 ↔ stK ε w < stK ε u) := by
  rw [stCross_slope ε hu.ne' hw.ne']
  have hc : 0 < stF ε u * stF ε w := mul_pos hu hw
  have := st_sgn_pos (b := stK ε w - stK ε u) hc
  rw [this.1, this.2, sub_pos, sub_neg]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem st_cross_LR (ε : ℝ) {u v : Plane} (hu : stF ε u < 0) (hv : 0 < stF ε v) :
    (0 < stCross u v ↔ stK ε v < stK ε u) ∧ (stCross u v < 0 ↔ stK ε u < stK ε v) := by
  rw [stCross_slope ε hu.ne hv.ne']
  have hc : stF ε u * stF ε v < 0 := mul_neg_of_neg_of_pos hu hv
  have := st_sgn_neg (b := stK ε v - stK ε u) hc
  rw [this.1, this.2, sub_neg, sub_pos]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- Two ear triangles with the same middle vertex `c` and the same orientation coincide. -/
theorem st_tri_unique {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    (hnc : stCrossingPairs M = ∅) (ε : ℝ) {c d m d' m' : Plane}
    (hcd : s(c, d) ∈ M) (hcm : s(c, m) ∈ M) (hdm : s(d, m) ∈ M)
    (hcd' : s(c, d') ∈ M) (hcm' : s(c, m') ∈ M) (hdm' : s(d', m') ∈ M)
    (hemp : ∀ w ∈ V, w ∈ convexHull ℝ ({c, d, m} : Set Plane) → w = c ∨ w = d ∨ w = m)
    (hemp' : ∀ w ∈ V, w ∈ convexHull ℝ ({c, d', m'} : Set Plane) → w = c ∨ w = d' ∨ w = m')
    (hd : d ∈ V) (hd' : d' ∈ V) (hm : m ∈ V) (hm' : m' ∈ V)
    (hFd : stF ε d < stF ε c) (hFm : stF ε c < stF ε m)
    (hFd' : stF ε d' < stF ε c) (hFm' : stF ε c < stF ε m')
    (hcr : stCross (d - c) (m - c) ≠ 0) (hcr' : stCross (d' - c) (m' - c) ≠ 0)
    (hty : 0 < stCross (d - c) (m - c) ↔ 0 < stCross (d' - c) (m' - c)) :
    d = d' ∧ m = m' := by
  have hFu : stF ε (d - c) < 0 := by rw [stF_sub]; linarith
  have hFv : 0 < stF ε (m - c) := by rw [stF_sub]; linarith
  have hFu' : stF ε (d' - c) < 0 := by rw [stF_sub]; linarith
  have hFv' : 0 < stF ε (m' - c) := by rw [stF_sub]; linarith
  have free := fun x (hx : s(c, x) ∈ M) => st_free_corner hD hnc hcd hcm hdm hcr hemp hx
  have free' := fun x (hx : s(c, x) ∈ M) => st_free_corner hD hnc hcd' hcm' hdm' hcr' hemp' hx
  -- orientation cases
  have hcase : (0 < stCross (d - c) (m - c) ∧ 0 < stCross (d' - c) (m' - c)) ∨
      (stCross (d - c) (m - c) < 0 ∧ stCross (d' - c) (m' - c) < 0) := by
    rcases lt_or_gt_of_ne hcr with h | h
    · right
      refine ⟨h, ?_⟩
      rcases lt_or_gt_of_ne hcr' with h' | h'
      · exact h'
      · exact absurd (hty.mpr h') (not_lt.mpr h.le)
    · left; exact ⟨h, hty.mp h⟩
  have hdd : d = d' := by
    by_contra hne
    have hk : stK ε (d - c) ≠ stK ε (d' - c) := fun hk =>
      hne (st_slope_inj hD ε hd hd' hcd hcd' (mul_pos_of_neg_of_neg hFu hFu') hk)
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rcases hcase with ⟨hA, hA'⟩ | ⟨hB, hB'⟩
      · -- u' is inside cone(u, v)
        have e1 := ((st_cross_LR ε hFu hFv).1.mp hA)
        have c1 : 0 < stCross (d' - c) (m - c) := (st_cross_LR ε hFu' hFv).1.mpr (by linarith)
        have c2 : 0 < stCross (d - c) (d' - c) := (st_cross_LL ε hFu hFu').1.mpr hlt
        exact free d' hcd' (st_cone_of_cross (mul_pos hA c1) (mul_pos hA c2))
      · have e1 := ((st_cross_LR ε hFu hFv).2.mp hB)
        have e1' := ((st_cross_LR ε hFu' hFv').2.mp hB')
        have c1 : stCross (d - c) (m' - c) < 0 := (st_cross_LR ε hFu hFv').2.mpr (by linarith)
        have c2 : stCross (d' - c) (d - c) < 0 := (st_cross_LL ε hFu' hFu).2.mpr hlt
        exact free' d hcd (st_cone_of_cross (mul_pos_of_neg_of_neg hB' c1)
          (mul_pos_of_neg_of_neg hB' c2))
    · rcases hcase with ⟨hA, hA'⟩ | ⟨hB, hB'⟩
      · have e1' := ((st_cross_LR ε hFu' hFv').1.mp hA')
        have c1 : 0 < stCross (d - c) (m' - c) := (st_cross_LR ε hFu hFv').1.mpr (by linarith)
        have c2 : 0 < stCross (d' - c) (d - c) := (st_cross_LL ε hFu' hFu).1.mpr hgt
        exact free' d hcd (st_cone_of_cross (mul_pos hA' c1) (mul_pos hA' c2))
      · have e1 := ((st_cross_LR ε hFu hFv).2.mp hB)
        have c1 : stCross (d' - c) (m - c) < 0 := (st_cross_LR ε hFu' hFv).2.mpr (by linarith)
        have c2 : stCross (d - c) (d' - c) < 0 := (st_cross_LL ε hFu hFu').2.mpr hgt
        exact free d' hcd' (st_cone_of_cross (mul_pos_of_neg_of_neg hB c1)
          (mul_pos_of_neg_of_neg hB c2))
  subst hdd
  refine ⟨rfl, ?_⟩
  by_contra hne
  have hk : stK ε (m - c) ≠ stK ε (m' - c) := fun hk =>
    hne (st_slope_inj hD ε hm hm' hcm hcm' (mul_pos hFv hFv') hk)
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · rcases hcase with ⟨hA, hA'⟩ | ⟨hB, hB'⟩
    · -- v inside cone(u, v')
      have c2 : 0 < stCross (m - c) (m' - c) := (st_cross_RR ε hFv hFv').1.mpr hlt
      exact free' m hcm (st_cone_of_cross (mul_pos hA' c2) (mul_pos hA' hA))
    · have c2 : stCross (m' - c) (m - c) < 0 := (st_cross_RR ε hFv' hFv).2.mpr hlt
      exact free m' hcm' (st_cone_of_cross (mul_pos_of_neg_of_neg hB c2)
        (mul_pos_of_neg_of_neg hB hB'))
  · rcases hcase with ⟨hA, hA'⟩ | ⟨hB, hB'⟩
    · have c2 : 0 < stCross (m' - c) (m - c) := (st_cross_RR ε hFv' hFv).1.mpr hgt
      exact free m' hcm' (st_cone_of_cross (mul_pos hA c2) (mul_pos hA hA'))
    · have c2 : stCross (m - c) (m' - c) < 0 := (st_cross_RR ε hFv hFv').2.mpr hgt
      exact free' m hcm (st_cone_of_cross (mul_pos_of_neg_of_neg hB' c2)
        (mul_pos_of_neg_of_neg hB' hB))

theorem stCross_left_comb (u v : Plane) (α β : ℝ) :
    stCross u (α • u + β • v) = β * stCross u v ∧ stCross (α • u + β • v) v = α * stCross u v := by
  constructor <;> simp [stCross] <;> ring

/-- A vector strictly inside the cone of two left vectors has a slope strictly between. -/
theorem st_cone_left (ε : ℝ) {u v w : Plane} (hu : stF ε u < 0) (hv : stF ε v < 0)
    (hk : stK ε u < stK ε v) (hw : stInCone u v w) :
    stF ε w < 0 ∧ stK ε u < stK ε w ∧ stK ε w < stK ε v := by
  obtain ⟨α, β, hα, hβ, rfl⟩ := hw
  have hFw : stF ε (α • u + β • v) < 0 := by
    rw [stF_add, stF_smul, stF_smul]; nlinarith
  have hcr : 0 < stCross u v := (st_cross_LL ε hu hv).1.mpr hk
  obtain ⟨h1, h2⟩ := stCross_left_comb u v α β
  refine ⟨hFw, ?_, ?_⟩
  · exact ((st_cross_LL ε hu hFw).1).mp (by rw [h1]; exact mul_pos hβ hcr)
  · exact ((st_cross_LL ε hFw hv).1).mp (by rw [h2]; exact mul_pos hα hcr)

theorem st_pred_exists {V : Finset Plane} {M : Finset (Sym2 Plane)} (ε : ℝ) {m a : Plane}
    (h : ∃ x ∈ V, s(m, x) ∈ M ∧ stF ε x < stF ε m ∧ stK ε (x - m) < stK ε (a - m)) :
    ∃ x ∈ V, s(m, x) ∈ M ∧ stF ε x < stF ε m ∧ stK ε (x - m) < stK ε (a - m) ∧
      ∀ y ∈ V, s(m, y) ∈ M → stF ε y < stF ε m → stK ε (y - m) < stK ε (a - m) →
        stK ε (y - m) ≤ stK ε (x - m) := by
  classical
  obtain ⟨x0, hx0V, hx0M, hx0F, hx0K⟩ := h
  obtain ⟨x, hxS, hxmax⟩ := Finset.exists_max_image
    (V.filter (fun y => s(m, y) ∈ M ∧ stF ε y < stF ε m ∧ stK ε (y - m) < stK ε (a - m)))
    (fun y => stK ε (y - m)) ⟨x0, Finset.mem_filter.mpr ⟨hx0V, hx0M, hx0F, hx0K⟩⟩
  obtain ⟨hxV, hxM, hxF, hxK⟩ := Finset.mem_filter.mp hxS
  exact ⟨x, hxV, hxM, hxF, hxK, fun y hy hyM hyF hyK =>
    hxmax y (Finset.mem_filter.mpr ⟨hy, hyM, hyF, hyK⟩)⟩

/-- The ear triangle at the apex `m` for consecutive left neighbours `x`, `a`. -/
theorem st_ear_of_pred {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    (ε : ℝ)
    (hear : ∀ m a b : Plane, s(m, a) ∈ M → s(m, b) ∈ M → stCross (a - m) (b - m) ≠ 0 →
      (∀ x, s(m, x) ∈ M → ¬ stInCone (a - m) (b - m) (x - m)) →
      s(a, b) ∈ M ∧ ∀ w ∈ V, w ∈ convexHull ℝ ({m, a, b} : Set Plane) → w = m ∨ w = a ∨ w = b)
    {m x a : Plane} (hxM : s(m, x) ∈ M) (haM : s(m, a) ∈ M)
    (hxF : stF ε x < stF ε m) (haF : stF ε a < stF ε m)
    (hK : stK ε (x - m) < stK ε (a - m))
    (hmax : ∀ y ∈ V, s(m, y) ∈ M → stF ε y < stF ε m → stK ε (y - m) < stK ε (a - m) →
      stK ε (y - m) ≤ stK ε (x - m)) :
    s(x, a) ∈ M ∧ (∀ w ∈ V, w ∈ convexHull ℝ ({m, x, a} : Set Plane) → w = m ∨ w = x ∨ w = a) ∧
      stCross (x - m) (a - m) ≠ 0 := by
  have hFx : stF ε (x - m) < 0 := by rw [stF_sub]; linarith
  have hFa : stF ε (a - m) < 0 := by rw [stF_sub]; linarith
  have hcr : stCross (x - m) (a - m) ≠ 0 :=
    ((st_cross_LL ε hFx hFa).1.mpr hK).ne'
  have hcons : ∀ y, s(m, y) ∈ M → ¬ stInCone (x - m) (a - m) (y - m) := by
    intro y hy hcone
    obtain ⟨h1, h2, h3⟩ := st_cone_left ε hFx hFa hK hcone
    have hyV : y ∈ V := (hD.1 _ hy).2 y (Sym2.mem_mk_right _ _)
    rw [stF_sub] at h1
    have := hmax y hyV hy (by linarith) h3
    linarith
  obtain ⟨h1, h2⟩ := hear m x a hxM haM hcr hcons
  exact ⟨h1, h2, hcr⟩

theorem st_tri_data {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    (ε : ℝ) (hFinj : ∀ a ∈ V, ∀ b ∈ V, stF ε a = stF ε b → a = b)
    {m x a : Plane} (hxV : x ∈ V) (haV : a ∈ V) (hxM : s(m, x) ∈ M) (haM : s(m, a) ∈ M)
    (hxF : stF ε x < stF ε m) (haF : stF ε a < stF ε m)
    (hK : stK ε (x - m) < stK ε (a - m))
    (hxa : s(x, a) ∈ M)
    (hemp : ∀ w ∈ V, w ∈ convexHull ℝ ({m, x, a} : Set Plane) → w = m ∨ w = x ∨ w = a)
    (hcr : stCross (x - m) (a - m) ≠ 0) :
    ∃ c d : Plane, c ∈ V ∧ d ∈ V ∧ ((a = c ∧ x = d) ∨ (a = d ∧ x = c)) ∧ s(c, d) ∈ M ∧
      s(c, m) ∈ M ∧ s(d, m) ∈ M ∧
      (∀ w ∈ V, w ∈ convexHull ℝ ({c, d, m} : Set Plane) → w = c ∨ w = d ∨ w = m) ∧
      stCross (d - c) (m - c) ≠ 0 ∧ stF ε d < stF ε c ∧ stF ε c < stF ε m := by
  have hxa_ne : x ≠ a := by
    intro h; rw [h] at hK; exact lt_irrefl _ hK
  have hFne : stF ε x ≠ stF ε a := fun h => hxa_ne (hFinj x hxV a haV h)
  have hsx : s(x, m) ∈ M := by rw [Sym2.eq_swap]; exact hxM
  have hsa : s(a, m) ∈ M := by rw [Sym2.eq_swap]; exact haM
  rcases lt_or_gt_of_ne hFne with hlt | hgt
  · refine ⟨a, x, haV, hxV, Or.inl ⟨rfl, rfl⟩, ?_, hsa, hsx, ?_, ?_, hlt, haF⟩
    · rw [Sym2.eq_swap]; exact hxa
    · intro w hw hwh
      have : ({a, x, m} : Set Plane) = {m, x, a} := by ext; simp; tauto
      rw [this] at hwh
      rcases hemp w hw hwh with h | h | h <;> tauto
    · have : stCross (x - a) (m - a) = - stCross (x - m) (a - m) := by simp [stCross]; ring
      rw [this]; exact neg_ne_zero.mpr hcr
  · refine ⟨x, a, hxV, haV, Or.inr ⟨rfl, rfl⟩, hxa, hsx, hsa, ?_, ?_, hgt, hxF⟩
    · intro w hw hwh
      have : ({x, a, m} : Set Plane) = {m, x, a} := by ext; simp; tauto
      rw [this] at hwh
      rcases hemp w hw hwh with h | h | h <;> tauto
    · have : stCross (a - x) (m - x) = stCross (x - m) (a - m) := by simp [stCross]; ring
      rw [this]; exact hcr

/-- ST1c: counting. -/
theorem st1c_count (V : Finset Plane) (M : Finset (Sym2 Plane)) (hD : stDrawing V M)
    (hnc : stCrossingPairs M = ∅) (ε : ℝ) (hε : Set.InjOn (fun p : Plane => p 0 + ε * p 1) V)
    (hear : ∀ m a b : Plane, s(m, a) ∈ M → s(m, b) ∈ M → stCross (a - m) (b - m) ≠ 0 →
      (∀ x, s(m, x) ∈ M → ¬ stInCone (a - m) (b - m) (x - m)) →
      s(a, b) ∈ M ∧ ∀ w ∈ V, w ∈ convexHull ℝ ({m, a, b} : Set Plane) → w = m ∨ w = a ∨ w = b) :
    M.card ≤ 3 * V.card := by
  classical
  have hFinj : ∀ a ∈ V, ∀ b ∈ V, stF ε a = stF ε b → a = b := fun a ha b hb h => hε ha hb h
  set P : Finset (Plane × Plane) :=
    (V ×ˢ V).filter (fun ma => s(ma.1, ma.2) ∈ M ∧ stF ε ma.2 < stF ε ma.1) with hP
  have hC1 : M.card ≤ P.card := by
    apply Finset.card_le_card_of_surjOn (fun ma : Plane × Plane => s(ma.1, ma.2))
    intro e he
    have he' : e ∈ M := Finset.mem_coe.mp he
    induction e using Sym2.ind with
    | _ a b =>
      have haV := (hD.1 _ he').2 a (Sym2.mem_mk_left _ _)
      have hbV := (hD.1 _ he').2 b (Sym2.mem_mk_right _ _)
      have hab : a ≠ b := by
        have := (hD.1 _ he').1
        rwa [Sym2.mk_isDiag_iff] at this
      have hFne : stF ε a ≠ stF ε b := fun h => hab (hFinj a haV b hbV h)
      rcases lt_or_gt_of_ne hFne with h | h
      · refine ⟨(b, a), Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hbV, haV⟩, ?_, h⟩), ?_⟩
        · rw [Sym2.eq_swap]; exact he'
        · exact Sym2.eq_swap
      · refine ⟨(a, b), Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haV, hbV⟩, he', h⟩), rfl⟩
  set Npred : Plane × Plane → Prop := fun ma => ∃ x ∈ V, s(ma.1, x) ∈ M ∧ stF ε x < stF ε ma.1 ∧
    stK ε (x - ma.1) < stK ε (ma.2 - ma.1) with hNp
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) Npred
  have hC2 : (P.filter (fun ma => ¬ Npred ma)).card ≤ V.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro ma hma
      have hma' := Finset.mem_filter.mp (Finset.mem_coe.mp hma)
      have hmaP := Finset.mem_filter.mp hma'.1
      rw [Finset.mem_coe]
      exact (Finset.mem_product.mp hmaP.1).1
    · rintro ⟨m, a⟩ hma ⟨m', a'⟩ hma' hfst
      simp only at hfst
      subst hfst
      have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp hma)
      have h2 := Finset.mem_filter.mp (Finset.mem_coe.mp hma')
      have hP1 := Finset.mem_filter.mp h1.1
      have hP2 := Finset.mem_filter.mp h2.1
      simp only at hP1 hP2
      by_contra hne
      have haa : a ≠ a' := fun h => hne (by rw [h])
      have haV := (Finset.mem_product.mp hP1.1).2
      have ha'V := (Finset.mem_product.mp hP2.1).2
      have hFa : stF ε (a - m) < 0 := by rw [stF_sub]; linarith [hP1.2.2]
      have hFa' : stF ε (a' - m) < 0 := by rw [stF_sub]; linarith [hP2.2.2]
      have hk : stK ε (a - m) ≠ stK ε (a' - m) := fun hk =>
        haa (st_slope_inj hD ε haV ha'V hP1.2.1 hP2.2.1 (mul_pos_of_neg_of_neg hFa hFa') hk)
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · exact h2.2 ⟨a, haV, hP1.2.1, hP1.2.2, hlt⟩
      · exact h1.2 ⟨a', ha'V, hP2.2.1, hP2.2.2, hgt⟩
  have hex : ∀ ma ∈ P.filter Npred, ∃ x ∈ V, s(ma.1, x) ∈ M ∧ stF ε x < stF ε ma.1 ∧
      stK ε (x - ma.1) < stK ε (ma.2 - ma.1) ∧
      ∀ y ∈ V, s(ma.1, y) ∈ M → stF ε y < stF ε ma.1 → stK ε (y - ma.1) < stK ε (ma.2 - ma.1) →
        stK ε (y - ma.1) ≤ stK ε (x - ma.1) :=
    fun ma hma => st_pred_exists ε (Finset.mem_filter.mp hma).2
  choose! pr hprV hprM hprF hprK hprmax using hex
  have htri : ∀ ma ∈ P.filter Npred, ∃ c d : Plane, c ∈ V ∧ d ∈ V ∧
      ((ma.2 = c ∧ pr ma = d) ∨ (ma.2 = d ∧ pr ma = c)) ∧ s(c, d) ∈ M ∧
      s(c, ma.1) ∈ M ∧ s(d, ma.1) ∈ M ∧
      (∀ w ∈ V, w ∈ convexHull ℝ ({c, d, ma.1} : Set Plane) → w = c ∨ w = d ∨ w = ma.1) ∧
      stCross (d - c) (ma.1 - c) ≠ 0 ∧ stF ε d < stF ε c ∧ stF ε c < stF ε ma.1 := by
    intro ma hma
    obtain ⟨hmaP, hN⟩ := Finset.mem_filter.mp hma
    obtain ⟨hprod, haM, haF⟩ := Finset.mem_filter.mp hmaP
    obtain ⟨hmV, haV⟩ := Finset.mem_product.mp hprod
    obtain ⟨hs1, hs2, hs3⟩ := st_ear_of_pred hD ε hear (hprM ma hma) haM (hprF ma hma) haF
      (hprK ma hma) (hprmax ma hma)
    exact st_tri_data hD ε hFinj (hprV ma hma) haV (hprM ma hma) haM (hprF ma hma) haF
      (hprK ma hma) hs1 hs2 hs3
  choose! cc dd hccV hddV hcd hsM1 hsM2 hsM3 hemp hcr hFdc hFcm using htri
  have hC3 : (P.filter Npred).card ≤ 2 * V.card := by
    have hψ : (P.filter Npred).card ≤ (V ×ˢ (Finset.univ : Finset Bool)).card := by
      apply Finset.card_le_card_of_injOn (fun ma : Plane × Plane =>
        (cc ma, decide (0 < stCross (dd ma - cc ma) (ma.1 - cc ma))))
      · intro ma hma
        have hma' := Finset.mem_coe.mp hma
        rw [Finset.mem_coe, Finset.mem_product]
        exact ⟨hccV ma hma', Finset.mem_univ _⟩
      · intro ma hma ma' hma' heq
        have h1 := Finset.mem_coe.mp hma
        have h2 := Finset.mem_coe.mp hma'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hc, hty⟩ := heq
        have hty' : 0 < stCross (dd ma - cc ma) (ma.1 - cc ma) ↔
            0 < stCross (dd ma' - cc ma') (ma'.1 - cc ma') := by
          simpa using hty
        have hmV : ma.1 ∈ V := (Finset.mem_product.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).1).1
        have hmV' : ma'.1 ∈ V := (Finset.mem_product.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).1).1
        have e1 : s(cc ma, dd ma') ∈ M := by rw [hc]; exact hsM1 ma' h2
        have e2 : s(cc ma, ma'.1) ∈ M := by rw [hc]; exact hsM2 ma' h2
        have e3 : s(dd ma', ma'.1) ∈ M := hsM3 ma' h2
        have e4 : ∀ w ∈ V, w ∈ convexHull ℝ ({cc ma, dd ma', ma'.1} : Set Plane) →
            w = cc ma ∨ w = dd ma' ∨ w = ma'.1 := by rw [hc]; exact hemp ma' h2
        have e5 : stCross (dd ma' - cc ma) (ma'.1 - cc ma) ≠ 0 := by rw [hc]; exact hcr ma' h2
        have e6 : stF ε (dd ma') < stF ε (cc ma) := by rw [hc]; exact hFdc ma' h2
        have e7 : stF ε (cc ma) < stF ε ma'.1 := by rw [hc]; exact hFcm ma' h2
        have hty'' : 0 < stCross (dd ma - cc ma) (ma.1 - cc ma) ↔
            0 < stCross (dd ma' - cc ma) (ma'.1 - cc ma) := by rw [← hc] at hty'; exact hty'
        obtain ⟨hdd, hmm⟩ := st_tri_unique hD hnc ε (hsM1 ma h1) (hsM2 ma h1) (hsM3 ma h1)
          e1 e2 e3 (hemp ma h1) e4 (hddV ma h1) (hddV ma' h2) hmV hmV'
          (hFdc ma h1) (hFcm ma h1) e6 e7 (hcr ma h1) e5 hty''
        refine Prod.ext hmm ?_
        have hK := hprK ma h1
        have hK' := hprK ma' h2
        rcases hcd ma h1 with ⟨ha1, hx1⟩ | ⟨ha1, hx1⟩ <;>
          rcases hcd ma' h2 with ⟨ha2, hx2⟩ | ⟨ha2, hx2⟩
        · rw [ha1, ha2, hc]
        · exfalso
          have hxa' : pr ma = ma'.2 := by rw [hx1, hdd, ha2]
          have hxa : pr ma' = ma.2 := by rw [hx2, ← hc, ha1]
          rw [hxa'] at hK
          rw [hxa] at hK'
          have hm : ma'.1 = ma.1 := hmm.symm
          rw [hm] at hK'
          linarith
        · exfalso
          have hxa' : pr ma = ma'.2 := by rw [hx1, hc, ha2]
          have hxa : pr ma' = ma.2 := by rw [hx2, ← hdd, ha1]
          rw [hxa'] at hK
          rw [hxa] at hK'
          have hm : ma'.1 = ma.1 := hmm.symm
          rw [hm] at hK'
          linarith
        · rw [ha1, ha2, hdd]
    calc (P.filter Npred).card ≤ (V ×ˢ (Finset.univ : Finset Bool)).card := hψ
      _ = 2 * V.card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring
  omega

/-! ### ST1b : the ear lemma -/

/-- barycentric numerators with respect to the triangle `m a b` -/
def stA (m b p : Plane) : ℝ := stCross (p - m) (b - m)
def stB (m a p : Plane) : ℝ := stCross (a - m) (p - m)
def stH (m a b p : Plane) : ℝ := stCross (a - m) (b - m) - stA m b p - stB m a p

theorem stA_comb (m b p q : Plane) (α β : ℝ) (h : α + β = 1) :
    stA m b (α • p + β • q) = α * stA m b p + β * stA m b q := by
  obtain rfl : α = 1 - β := by linarith
  simp [stA, stCross]; ring

theorem stB_comb (m a p q : Plane) (α β : ℝ) (h : α + β = 1) :
    stB m a (α • p + β • q) = α * stB m a p + β * stB m a q := by
  obtain rfl : α = 1 - β := by linarith
  simp [stB, stCross]; ring

theorem stH_comb (m a b p q : Plane) (α β : ℝ) (h : α + β = 1) :
    stH m a b (α • p + β • q) = α * stH m a b p + β * stH m a b q := by
  unfold stH
  rw [stA_comb m b p q α β h, stB_comb m a p q α β h]
  have : stCross (a - m) (b - m) = α * stCross (a - m) (b - m) + β * stCross (a - m) (b - m) := by
    rw [← add_mul, h, one_mul]
  linarith

theorem stA_m (m b : Plane) : stA m b m = 0 := by simp [stA, stCross]
theorem stB_m (m a : Plane) : stB m a m = 0 := by simp [stB, stCross]
theorem stA_a (m a b : Plane) : stA m b a = stCross (a - m) (b - m) := rfl
theorem stB_a (m a : Plane) : stB m a a = 0 := by simp [stB, stCross]; ring
theorem stA_b (m b : Plane) : stA m b b = 0 := by simp [stA, stCross]; ring
theorem stB_b (m a b : Plane) : stB m a b = stCross (a - m) (b - m) := rfl

theorem stH_m (m a b : Plane) : stH m a b m = stCross (a - m) (b - m) := by
  simp [stH, stA_m, stB_m]
theorem stH_a (m a b : Plane) : stH m a b a = 0 := by
  simp [stH, stA_a, stB_a]
theorem stH_b (m a b : Plane) : stH m a b b = 0 := by
  simp [stH, stA_b, stB_b]

/-- the coordinates decompose a point -/
theorem st_decomp (m a b p : Plane) (hc : stCross (a - m) (b - m) ≠ 0) :
    p = m + ((stA m b p / stCross (a - m) (b - m)) • (a - m) +
      (stB m a p / stCross (a - m) (b - m)) • (b - m)) := by
  have h := st_cramer (a - m) (b - m) (p - m)
  have h2 : p - m = (stCross (a - m) (b - m))⁻¹ • (stCross (a - m) (b - m) • (p - m)) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [h] at h2
  rw [smul_add, smul_smul, smul_smul, ← div_eq_inv_mul, ← div_eq_inv_mul] at h2
  unfold stA stB
  rw [← h2]
  abel

/-- the closed triangle in coordinates -/
theorem st_hull_coords (m a b : Plane) (hc : 0 < stCross (a - m) (b - m)) {p : Plane}
    (hp : p ∈ convexHull ℝ ({m, a, b} : Set Plane)) :
    0 ≤ stA m b p ∧ 0 ≤ stB m a p ∧ 0 ≤ stH m a b p := by
  have hconv : Convex ℝ {p : Plane | 0 ≤ stA m b p ∧ 0 ≤ stB m a p ∧ 0 ≤ stH m a b p} := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · rw [stA_comb m b x y s t hst]; positivity
    · rw [stB_comb m a x y s t hst]; positivity
    · rw [stH_comb m a b x y s t hst]; positivity
  have hsub : ({m, a, b} : Set Plane) ⊆ {p : Plane | 0 ≤ stA m b p ∧ 0 ≤ stB m a p ∧ 0 ≤ stH m a b p} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · refine ⟨?_, ?_, ?_⟩ <;> simp [stA_m, stB_m, stH_m, hc.le]
    · refine ⟨?_, ?_, ?_⟩ <;> simp [stA_a, stB_a, stH_a, hc.le]
    · refine ⟨?_, ?_, ?_⟩ <;> simp [stA_b, stB_b, stH_b, hc.le]
  exact convexHull_min hsub hconv hp

theorem st_side_ma (m a b p : Plane) (hc : 0 < stCross (a - m) (b - m)) (hB : stB m a p = 0)
    (hA0 : 0 ≤ stA m b p) (hA1 : stA m b p ≤ stCross (a - m) (b - m)) :
    p ∈ segment ℝ m a := by
  have h := st_decomp m a b p hc.ne'
  rw [hB, zero_div, zero_smul, add_zero] at h
  rw [segment_eq_image']
  refine ⟨stA m b p / stCross (a - m) (b - m), ⟨div_nonneg hA0 hc.le, (div_le_one hc).mpr hA1⟩, ?_⟩
  simp only
  exact h.symm

theorem st_side_mb (m a b p : Plane) (hc : 0 < stCross (a - m) (b - m)) (hA : stA m b p = 0)
    (hB0 : 0 ≤ stB m a p) (hB1 : stB m a p ≤ stCross (a - m) (b - m)) :
    p ∈ segment ℝ m b := by
  have h := st_decomp m a b p hc.ne'
  rw [hA, zero_div, zero_smul, zero_add] at h
  rw [segment_eq_image']
  refine ⟨stB m a p / stCross (a - m) (b - m), ⟨div_nonneg hB0 hc.le, (div_le_one hc).mpr hB1⟩, ?_⟩
  simp only
  exact h.symm

theorem st_B_on_ma (m a b p : Plane) (hp : p ∈ segment ℝ m a) : stB m a p = 0 := by
  obtain ⟨α, β, _, _, h, rfl⟩ := hp
  rw [stB_comb m a m a α β h, stB_m, stB_a]; ring

theorem st_A_on_mb (m b p : Plane) (hp : p ∈ segment ℝ m b) : stA m b p = 0 := by
  obtain ⟨α, β, _, _, h, rfl⟩ := hp
  rw [stA_comb m b m b α β h, stA_m, stA_b]; ring

/-- A segment of `M` through a point of the open triangle that leaves the triangle through a side
other than the base would cross one of the edges `ma`, `mb`. -/
theorem st_exit {M : Finset (Sym2 Plane)} (hnc : stCrossingPairs M = ∅)
    {m a b : Plane} (hc : 0 < stCross (a - m) (b - m))
    (hma : s(m, a) ∈ M) (hmb : s(m, b) ∈ M)
    {p q z : Plane} (hg : s(p, q) ∈ M) (hzg : z ∈ segment ℝ p q)
    (hA : 0 < stA m b z) (hB : 0 < stB m a z) (hH : 0 ≤ stH m a b z)
    (hHq : stH m a b z ≤ stH m a b q) (hHq0 : 0 < stH m a b q)
    (hq : stA m b q < 0 ∨ stB m a q < 0) (hmp : m ≠ p) (hmq : m ≠ q) : False := by
  have hcont : Continuous (fun s : ℝ => min ((1 - s) * stA m b z + s * stA m b q)
      ((1 - s) * stB m a z + s * stB m a q)) := by fun_prop
  have hφ0 : 0 < min ((1 - 0) * stA m b z + 0 * stA m b q)
      ((1 - 0) * stB m a z + 0 * stB m a q) := by simpa using lt_min hA hB
  have hφ1 : min ((1 - 1) * stA m b z + 1 * stA m b q)
      ((1 - 1) * stB m a z + 1 * stB m a q) < 0 := by
    simp only [sub_self, zero_mul, zero_add, one_mul]
    rcases hq with h | h
    · exact lt_of_le_of_lt (min_le_left _ _) h
    · exact lt_of_le_of_lt (min_le_right _ _) h
  obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨hφ1.le, hφ0.le⟩)
  obtain ⟨hs0, hs1⟩ := hs
  simp only at hφs
  have hX : 0 ≤ (1 - s) * stA m b z + s * stA m b q := by
    have := le_min_iff.mp (le_of_eq hφs.symm); exact this.1
  have hY : 0 ≤ (1 - s) * stB m a z + s * stB m a q := by
    have := le_min_iff.mp (le_of_eq hφs.symm); exact this.2
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hs0 with h | h
    · exfalso; rw [← h] at hφs; simp at hφs; exact absurd hφs (lt_min hA hB).ne'
    · exact h
  have h1s : (1 - s) + s = 1 := by ring
  set y := (1 - s) • z + s • q with hy
  have hAy : stA m b y = (1 - s) * stA m b z + s * stA m b q := stA_comb m b z q _ _ h1s
  have hBy : stB m a y = (1 - s) * stB m a z + s * stB m a q := stB_comb m a z q _ _ h1s
  have hHy : stH m a b y = (1 - s) * stH m a b z + s * stH m a b q := stH_comb m a b z q _ _ h1s
  have hHypos : 0 < stH m a b y := by
    rw [hHy]; nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hH, mul_pos hspos hHq0]
  have hyseg : y ∈ segment ℝ p q :=
    (convex_segment p q) hzg (right_mem_segment ℝ p q) (sub_nonneg.mpr hs1) hs0 h1s
  have hdef : stH m a b y = stCross (a - m) (b - m) - stA m b y - stB m a y := rfl
  rcases min_choice ((1 - s) * stA m b z + s * stA m b q) ((1 - s) * stB m a z + s * stB m a q)
    with hmin | hmin
  · -- A y = 0 : y on the side mb
    have hAy0 : stA m b y = 0 := by rw [hAy]; linarith
    have hyseg' : y ∈ segment ℝ m b := by
      apply st_side_mb m a b y hc hAy0
      · rw [hBy]; exact hY
      · linarith
    have hne : s(p, q) ≠ s(m, b) := by
      intro h
      have hz' : z ∈ segment ℝ m b := by
        have := hzg; rw [← stSeg_mk, h, stSeg_mk] at this; exact this
      have := st_A_on_mb m b z hz'
      linarith
    obtain ⟨hy1, hy2⟩ := st_noncross hnc hg hmb hne (by rw [stSeg_mk]; exact hyseg)
      (by rw [stSeg_mk]; exact hyseg')
    rcases Sym2.mem_iff.mp hy2 with h | h
    · rcases Sym2.mem_iff.mp hy1 with h' | h'
      · exact hmp (h.symm.trans h')
      · exact hmq (h.symm.trans h')
    · rw [h, stH_b] at hHypos; exact lt_irrefl _ hHypos
  · have hBy0 : stB m a y = 0 := by rw [hBy]; linarith
    have hyseg' : y ∈ segment ℝ m a := by
      apply st_side_ma m a b y hc hBy0
      · rw [hAy]; exact hX
      · linarith
    have hne : s(p, q) ≠ s(m, a) := by
      intro h
      have hz' : z ∈ segment ℝ m a := by
        have := hzg; rw [← stSeg_mk, h, stSeg_mk] at this; exact this
      have := st_B_on_ma m a b z hz'
      linarith
    obtain ⟨hy1, hy2⟩ := st_noncross hnc hg hma hne (by rw [stSeg_mk]; exact hyseg)
      (by rw [stSeg_mk]; exact hyseg')
    rcases Sym2.mem_iff.mp hy2 with h | h
    · rcases Sym2.mem_iff.mp hy1 with h' | h'
      · exact hmp (h.symm.trans h')
      · exact hmq (h.symm.trans h')
    · rw [h, stH_a] at hHypos; exact lt_irrefl _ hHypos

theorem st_drawing_insert {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    {u w : Plane} (hu : u ∈ V) (hw : w ∈ V) (huw : u ≠ w)
    (hvert : ∀ x ∈ V, x ∈ segment ℝ u w → x = u ∨ x = w) : stDrawing V (insert s(u, w) M) := by
  classical
  constructor
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · refine ⟨?_, ?_⟩
      · rw [Sym2.mk_isDiag_iff]; exact huw
      · intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hu
        · exact hw
    · exact hD.1 e he
  · intro e he v hv hvs
    rcases Finset.mem_insert.mp he with rfl | he
    · rw [stSeg_mk] at hvs
      rcases hvert v hv hvs with rfl | rfl
      · exact Sym2.mem_mk_left _ _
      · exact Sym2.mem_mk_right _ _
    · exact hD.2 e he v hv hvs

theorem st_coords_hull (m a b : Plane) (hc : 0 < stCross (a - m) (b - m)) {q : Plane}
    (hA : 0 ≤ stA m b q) (hB : 0 ≤ stB m a q) (hH : 0 ≤ stH m a b q) :
    q ∈ convexHull ℝ ({m, a, b} : Set Plane) := by
  have hdec := st_decomp m a b q hc.ne'
  have hcne : stCross (a - m) (b - m) ≠ 0 := hc.ne'
  have hHc : stH m a b q / stCross (a - m) (b - m) =
      1 - stA m b q / stCross (a - m) (b - m) - stB m a q / stCross (a - m) (b - m) := by
    unfold stH; field_simp
  have hsum : stH m a b q / stCross (a - m) (b - m) + stA m b q / stCross (a - m) (b - m)
      + stB m a q / stCross (a - m) (b - m) = 1 := by rw [hHc]; ring
  have hmem := (convex_convexHull ℝ ({m, a, b} : Set Plane)).sum_mem
    (t := (Finset.univ : Finset (Fin 3)))
    (w := ![stH m a b q / stCross (a - m) (b - m), stA m b q / stCross (a - m) (b - m),
      stB m a q / stCross (a - m) (b - m)]) (z := ![m, a, b])
    (fun i _ => by fin_cases i <;> simp <;> positivity)
    (by simpa [Fin.sum_univ_three] using hsum)
    (fun i _ => by
      fin_cases i <;> simp <;> apply subset_convexHull <;> simp)
  have heq : q = (stH m a b q / stCross (a - m) (b - m)) • m +
      (stA m b q / stCross (a - m) (b - m)) • a + (stB m a q / stCross (a - m) (b - m)) • b := by
    calc q = m + ((stA m b q / stCross (a - m) (b - m)) • (a - m) +
          (stB m a q / stCross (a - m) (b - m)) • (b - m)) := hdec
      _ = _ := by rw [hHc]; module
  rw [heq]
  simpa [Fin.sum_univ_three] using hmem

/-- Step A: the closed triangle of an ear contains no further vertex. -/
theorem st_ear_empty {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    (hnc : stCrossingPairs M = ∅) (hmax : ∀ u w, stFree V M u w → s(u, w) ∈ M)
    {m a b : Plane} (hc : 0 < stCross (a - m) (b - m))
    (hma : s(m, a) ∈ M) (hmb : s(m, b) ∈ M)
    (hcons : ∀ x, s(m, x) ∈ M → ¬ stInCone (a - m) (b - m) (x - m)) :
    ∀ w ∈ V, w ∈ convexHull ℝ ({m, a, b} : Set Plane) → w = m ∨ w = a ∨ w = b := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨w0, hw0V, hw0h, hw0m, hw0a, hw0b⟩ := hcon
  have hmV : m ∈ V := (hD.1 _ hma).2 m (Sym2.mem_mk_left _ _)
  have haV : a ∈ V := (hD.1 _ hma).2 a (Sym2.mem_mk_right _ _)
  have hbV : b ∈ V := (hD.1 _ hmb).2 b (Sym2.mem_mk_right _ _)
  have hmhull : m ∈ convexHull ℝ ({m, a, b} : Set Plane) := subset_convexHull ℝ _ (by simp)
  obtain ⟨w, hwW, hwmax⟩ := Finset.exists_max_image
    (V.filter (fun w => w ∈ convexHull ℝ ({m, a, b} : Set Plane) ∧ w ≠ m ∧ w ≠ a ∧ w ≠ b))
    (stH m a b) ⟨w0, Finset.mem_filter.mpr ⟨hw0V, hw0h, hw0m, hw0a, hw0b⟩⟩
  obtain ⟨hwV, hwh, hwm, hwa, hwb⟩ := Finset.mem_filter.mp hwW
  obtain ⟨hA0, hB0, hH0⟩ := st_hull_coords m a b hc hwh
  have hHdef : ∀ p, stH m a b p = stCross (a - m) (b - m) - stA m b p - stB m a p := fun p => rfl
  have hA : 0 < stA m b w := by
    rcases eq_or_lt_of_le hA0 with h | h
    · exfalso
      have hseg : w ∈ segment ℝ m b :=
        st_side_mb m a b w hc h.symm hB0 (by have := hH0; rw [hHdef] at this; linarith)
      rcases st_vertex_on_seg hD hmb hwV hseg with h' | h'
      · exact hwm h'
      · exact hwb h'
    · exact h
  have hB : 0 < stB m a w := by
    rcases eq_or_lt_of_le hB0 with h | h
    · exfalso
      have hseg : w ∈ segment ℝ m a :=
        st_side_ma m a b w hc h.symm hA0 (by have := hH0; rw [hHdef] at this; linarith)
      rcases st_vertex_on_seg hD hma hwV hseg with h' | h'
      · exact hwm h'
      · exact hwa h'
    · exact h
  have hHlt : stH m a b w < stCross (a - m) (b - m) := by rw [hHdef]; linarith
  have hcone : stInCone (a - m) (b - m) (w - m) :=
    st_cone_of_cross (mul_pos hc hA) (mul_pos hc hB)
  have hne : m ≠ w := fun h => hwm h.symm
  -- no vertex on the open segment mw
  have hvert : ∀ x ∈ V, x ∈ segment ℝ m w → x = m ∨ x = w := by
    intro x hxV hxs
    by_contra hx
    push Not at hx
    obtain ⟨hxm, hxw⟩ := hx
    have hxh : x ∈ convexHull ℝ ({m, a, b} : Set Plane) :=
      (convex_convexHull ℝ _).segment_subset hmhull hwh hxs
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hxs
    have hβ0 : β ≠ 0 := by
      intro h; apply hxm
      have : α = 1 := by linarith
      rw [h, this]; simp
    have hβ1 : β ≠ 1 := by
      intro h; apply hxw
      have : α = 0 := by linarith
      rw [h, this]; simp
    have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
    have hβlt : β < 1 := by
      rcases eq_or_lt_of_le (show β ≤ 1 by linarith) with h | h
      · exact absurd h hβ1
      · exact h
    have hAx : stA m b (α • m + β • w) = β * stA m b w := by
      rw [stA_comb m b m w α β hαβ, stA_m]; ring
    have hBx : stB m a (α • m + β • w) = β * stB m a w := by
      rw [stB_comb m a m w α β hαβ, stB_m]; ring
    have hHx : stH m a b (α • m + β • w) = α * stCross (a - m) (b - m) + β * stH m a b w := by
      rw [stH_comb m a b m w α β hαβ, stH_m]
    have hxa : α • m + β • w ≠ a := by
      intro h; have := congrArg (stB m a) h; rw [hBx, stB_a] at this; nlinarith
    have hxb : α • m + β • w ≠ b := by
      intro h; have := congrArg (stA m b) h; rw [hAx, stA_b] at this; nlinarith
    have hxW : α • m + β • w ∈ V.filter (fun w => w ∈ convexHull ℝ ({m, a, b} : Set Plane) ∧
        w ≠ m ∧ w ≠ a ∧ w ≠ b) := Finset.mem_filter.mpr ⟨hxV, hxh, hxm, hxa, hxb⟩
    have := hwmax _ hxW
    rw [hHx] at this
    have hα' : α = 1 - β := by linarith
    rw [hα'] at this
    nlinarith
  -- no edge crosses mw
  have hnocross : ∀ g ∈ M, ¬ stCrosses s(m, w) g := by
    intro g hg hcr
    have hD' := st_drawing_insert hD hmV hwV hne hvert
    obtain ⟨hne', z, hz1, hz2, hz3⟩ := hcr
    have hmg : m ∉ g := fun hm => st_cross_disjoint hD' (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem hg) ⟨hne', z, hz1, hz2, hz3⟩ (Sym2.mem_mk_left _ _) hm
    induction g using Sym2.ind with
    | _ p q =>
      have hpV := (hD.1 _ hg).2 p (Sym2.mem_mk_left _ _)
      have hqV := (hD.1 _ hg).2 q (Sym2.mem_mk_right _ _)
      have hmp : m ≠ p := fun h => hmg (h ▸ Sym2.mem_mk_left _ _)
      have hmq : m ≠ q := fun h => hmg (h ▸ Sym2.mem_mk_right _ _)
      have hz1' : z ∈ segment ℝ m w := by rw [stSeg_mk] at hz1; exact hz1
      have hz2' : z ∈ segment ℝ p q := by rw [stSeg_mk] at hz2; exact hz2
      have hzm : z ≠ m := fun h => hmg (hD.2 _ hg m hmV (by rw [← h]; exact hz2))
      have hzw : z ≠ w := by
        intro h
        have hwq : w ∈ s(p, q) := hD.2 _ hg w hwV (by rw [← h]; exact hz2)
        exact hz3 ⟨by rw [h]; exact Sym2.mem_mk_right _ _, by rw [h]; exact hwq⟩
      obtain ⟨α, β, hα, hβ, hαβ, hzeq⟩ := hz1'
      have hβ0 : β ≠ 0 := by
        intro h; apply hzm
        have : α = 1 := by linarith
        rw [← hzeq, h, this]; simp
      have hβ1 : β ≠ 1 := by
        intro h; apply hzw
        have : α = 0 := by linarith
        rw [← hzeq, h, this]; simp
      have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      have hβlt : β < 1 := lt_of_le_of_ne (by linarith) hβ1
      have hAz : stA m b z = β * stA m b w := by
        rw [← hzeq, stA_comb m b m w α β hαβ, stA_m]; ring
      have hBz : stB m a z = β * stB m a w := by
        rw [← hzeq, stB_comb m a m w α β hαβ, stB_m]; ring
      have hHz : stH m a b z = α * stCross (a - m) (b - m) + β * stH m a b w := by
        rw [← hzeq, stH_comb m a b m w α β hαβ, stH_m]
      have hα' : α = 1 - β := by linarith
      have hHzw : stH m a b w < stH m a b z := by
        rw [hHz, hα']; nlinarith
      have hAzpos : 0 < stA m b z := by rw [hAz]; exact mul_pos hβpos hA
      have hBzpos : 0 < stB m a z := by rw [hBz]; exact mul_pos hβpos hB
      have claim : ∀ p q : Plane, s(p, q) ∈ M → z ∈ segment ℝ p q → q ∈ V → m ≠ p → m ≠ q →
          stH m a b z ≤ stH m a b q → False := by
        intro p q hg' hzpq hqV' hmp' hmq' hHq
        have hHqpos : 0 < stH m a b q := by
          have : 0 ≤ stH m a b w := hH0
          linarith
        by_cases hqcoords : 0 ≤ stA m b q ∧ 0 ≤ stB m a q
        · have hqh := st_coords_hull m a b hc hqcoords.1 hqcoords.2 hHqpos.le
          by_cases hq3 : q = m ∨ q = a ∨ q = b
          · rcases hq3 with h | h | h
            · exact hmq' h.symm
            · rw [h, stH_a] at hHqpos; exact lt_irrefl _ hHqpos
            · rw [h, stH_b] at hHqpos; exact lt_irrefl _ hHqpos
          · push Not at hq3
            have := hwmax q (Finset.mem_filter.mpr ⟨hqV', hqh, hq3.1, hq3.2.1, hq3.2.2⟩)
            linarith
        · have hq' : stA m b q < 0 ∨ stB m a q < 0 := by
            by_contra hh
            push Not at hh
            exact hqcoords hh
          exact st_exit hnc hc hma hmb hg' hzpq hAzpos hBzpos (by linarith) hHq hHqpos hq' hmp' hmq'
      obtain ⟨α', β', hα', hβ', hαβ', hzeq'⟩ := hz2'
      have hHz' : stH m a b z = α' * stH m a b p + β' * stH m a b q := by
        rw [← hzeq', stH_comb m a b p q α' β' hαβ']
      rcases le_total (stH m a b p) (stH m a b q) with hpq | hpq
      · exact claim p q hg ⟨α', β', hα', hβ', hαβ', hzeq'⟩ hqV hmp hmq (by nlinarith)
      · refine claim q p (by rw [Sym2.eq_swap]; exact hg) ?_ hpV hmq hmp (by nlinarith)
        rw [segment_symm]; exact ⟨α', β', hα', hβ', hαβ', hzeq'⟩
  have hfree : stFree V M m w := ⟨hmV, hwV, hne, hvert, hnocross⟩
  exact hcons w (hmax m w hfree) hcone

theorem st_eq_of_coords (m a b y y' : Plane) (hc : 0 < stCross (a - m) (b - m))
    (hA : stA m b y = stA m b y') (hB : stB m a y = stB m a y') : y = y' := by
  have h1 := st_decomp m a b y hc.ne'
  have h2 := st_decomp m a b y' hc.ne'
  rw [hA, hB] at h1
  exact h1.trans h2.symm

theorem st_pt_a (m a b y : Plane) (hc : 0 < stCross (a - m) (b - m))
    (hA : stA m b y = stCross (a - m) (b - m)) (hB : stB m a y = 0) : y = a := by
  apply st_eq_of_coords m a b y a hc
  · rw [hA, stA_a]
  · rw [hB, stB_a]

theorem st_pt_b (m a b y : Plane) (hc : 0 < stCross (a - m) (b - m))
    (hA : stA m b y = 0) (hB : stB m a y = stCross (a - m) (b - m)) : y = b := by
  apply st_eq_of_coords m a b y b hc
  · rw [hA, stA_b]
  · rw [hB, stB_b]

/-- Collinear case of the base-freeness argument. -/
theorem st_collinear_false {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    {m a b : Plane} (hc : 0 < stCross (a - m) (b - m)) (haV : a ∈ V) (hbV : b ∈ V)
    (hempty : ∀ w ∈ V, w ∈ convexHull ℝ ({m, a, b} : Set Plane) → w = m ∨ w = a ∨ w = b)
    {p q z : Plane} (hpV : p ∈ V) (hqV : q ∈ V) (hg : s(p, q) ∈ M) (hne : s(p, q) ≠ s(a, b))
    (hHp : stH m a b p = 0) (hHq : stH m a b q = 0)
    (hzpq : z ∈ segment ℝ p q) (hz0 : 0 < stA m b z) (hzc : stA m b z < stCross (a - m) (b - m))
    (hpq : stA m b p ≤ stA m b q) : False := by
  obtain ⟨α, β, hα, hβ, hαβ, hzeq⟩ := hzpq
  have hAz : stA m b z = α * stA m b p + β * stA m b q := by
    rw [← hzeq, stA_comb m b p q α β hαβ]
  have hApz : stA m b p ≤ stA m b z := by nlinarith
  have hAzq : stA m b z ≤ stA m b q := by nlinarith
  have hHdef : ∀ y, stH m a b y = stCross (a - m) (b - m) - stA m b y - stB m a y := fun y => rfl
  have hBp : stB m a p = stCross (a - m) (b - m) - stA m b p := by have := hHdef p; linarith
  have hBq : stB m a q = stCross (a - m) (b - m) - stA m b q := by have := hHdef q; linarith
  set c := stCross (a - m) (b - m) with hcdef
  have hpt : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → stA m b (ρ • p + (1 - ρ) • q) =
      ρ * stA m b p + (1 - ρ) * stA m b q ∧ stB m a (ρ • p + (1 - ρ) • q) =
      c - (ρ * stA m b p + (1 - ρ) * stA m b q) := by
    intro ρ _ _
    have h1 : ρ + (1 - ρ) = 1 := by ring
    refine ⟨stA_comb m b p q ρ (1 - ρ) h1, ?_⟩
    rw [stB_comb m a p q ρ (1 - ρ) h1, hBp, hBq]; ring
  rcases lt_or_ge c (stA m b q) with hqc | hqc
  · -- a lies strictly between p and q
    have hden : 0 < stA m b q - stA m b p := by linarith
    set ρ := (stA m b q - c) / (stA m b q - stA m b p) with hρ
    have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hden.le
    have hρ1 : ρ ≤ 1 := (div_le_one hden).mpr (by linarith)
    have hval : ρ * stA m b p + (1 - ρ) * stA m b q = c := by
      rw [hρ]; field_simp; ring
    obtain ⟨hA1, hB1⟩ := hpt ρ hρ0 hρ1
    have hya : ρ • p + (1 - ρ) • q = a := by
      apply st_pt_a m a b _ hc
      · rw [hA1, hval]
      · rw [hB1, hval]; ring
    have hamem : a ∈ segment ℝ p q := ⟨ρ, 1 - ρ, hρ0, by linarith, by ring, hya⟩
    have := hD.2 _ hg a haV (by rw [stSeg_mk]; exact hamem)
    rcases Sym2.mem_iff.mp this with h | h
    · have := congrArg (stA m b) h; rw [stA_a] at this; linarith
    · have := congrArg (stA m b) h; rw [stA_a] at this; linarith
  · rcases lt_or_ge (stA m b p) 0 with hp0 | hp0
    · -- b lies strictly between p and q
      have hden : 0 < stA m b q - stA m b p := by linarith
      set ρ := stA m b q / (stA m b q - stA m b p) with hρ
      have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hden.le
      have hρ1 : ρ ≤ 1 := (div_le_one hden).mpr (by linarith)
      have hval : ρ * stA m b p + (1 - ρ) * stA m b q = 0 := by
        rw [hρ]; field_simp; ring
      obtain ⟨hA1, hB1⟩ := hpt ρ hρ0 hρ1
      have hyb : ρ • p + (1 - ρ) • q = b := by
        apply st_pt_b m a b _ hc
        · rw [hA1, hval]
        · rw [hB1, hval]; ring
      have hbmem : b ∈ segment ℝ p q := ⟨ρ, 1 - ρ, hρ0, by linarith, by ring, hyb⟩
      have := hD.2 _ hg b hbV (by rw [stSeg_mk]; exact hbmem)
      rcases Sym2.mem_iff.mp this with h | h
      · have := congrArg (stA m b) h; rw [stA_b] at this; linarith
      · have := congrArg (stA m b) h; rw [stA_b] at this; linarith
    · -- p and q lie on the segment ab
      have hph : p ∈ convexHull ℝ ({m, a, b} : Set Plane) :=
        st_coords_hull m a b hc hp0 (by rw [hBp]; linarith) hHp.ge
      have hqh : q ∈ convexHull ℝ ({m, a, b} : Set Plane) :=
        st_coords_hull m a b hc (by linarith) (by rw [hBq]; linarith) hHq.ge
      rcases hempty p hpV hph with h | h | h
      · rw [h, stH_m] at hHp; exact hc.ne' hHp
      · have e : stA m b p = c := by rw [h]; exact stA_a m a b
        linarith
      · rcases hempty q hqV hqh with h' | h' | h'
        · rw [h', stH_m] at hHq; exact hc.ne' hHq
        · apply hne; rw [h, h', Sym2.eq_swap]
        · have := congrArg (stA m b) h'; rw [stA_b] at this; linarith

/-- Step B: the base `ab` of an ear is an edge. -/
theorem st_ear_base {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    (hnc : stCrossingPairs M = ∅) (hmax : ∀ u w, stFree V M u w → s(u, w) ∈ M)
    {m a b : Plane} (hc : 0 < stCross (a - m) (b - m))
    (hma : s(m, a) ∈ M) (hmb : s(m, b) ∈ M)
    (hcons : ∀ x, s(m, x) ∈ M → ¬ stInCone (a - m) (b - m) (x - m))
    (hempty : ∀ w ∈ V, w ∈ convexHull ℝ ({m, a, b} : Set Plane) → w = m ∨ w = a ∨ w = b) :
    s(a, b) ∈ M := by
  classical
  have haV : a ∈ V := (hD.1 _ hma).2 a (Sym2.mem_mk_right _ _)
  have hbV : b ∈ V := (hD.1 _ hmb).2 b (Sym2.mem_mk_right _ _)
  have hab : a ≠ b := by
    intro h
    have h0 : stCross (b - m) (b - m) = 0 := by unfold stCross; ring
    rw [h] at hc; linarith
  have hHseg : ∀ y ∈ segment ℝ a b, stH m a b y = 0 := by
    rintro y ⟨α, β, _, _, h, rfl⟩
    rw [stH_comb m a b a b α β h, stH_a, stH_b]; ring
  have hasub : a ∈ convexHull ℝ ({m, a, b} : Set Plane) := subset_convexHull ℝ _ (by simp)
  have hbsub : b ∈ convexHull ℝ ({m, a, b} : Set Plane) := subset_convexHull ℝ _ (by simp)
  have hvert : ∀ x ∈ V, x ∈ segment ℝ a b → x = a ∨ x = b := by
    intro x hxV hxs
    have hxh : x ∈ convexHull ℝ ({m, a, b} : Set Plane) :=
      (convex_convexHull ℝ _).segment_subset hasub hbsub hxs
    rcases hempty x hxV hxh with h | h | h
    · exfalso
      have := hHseg x hxs
      rw [h, stH_m] at this
      exact hc.ne' this
    · exact Or.inl h
    · exact Or.inr h
  apply hmax a b
  refine ⟨haV, hbV, hab, hvert, ?_⟩
  intro g hg hcr
  obtain ⟨hne', z, hz1, hz2, hz3⟩ := hcr
  induction g using Sym2.ind with
  | _ p q =>
    have hpV := (hD.1 _ hg).2 p (Sym2.mem_mk_left _ _)
    have hqV := (hD.1 _ hg).2 q (Sym2.mem_mk_right _ _)
    have hz1' : z ∈ segment ℝ a b := by rw [stSeg_mk] at hz1; exact hz1
    have hz2' : z ∈ segment ℝ p q := by rw [stSeg_mk] at hz2; exact hz2
    have hza : z ≠ a := by
      intro h; apply hz3
      exact ⟨by rw [h]; exact Sym2.mem_mk_left _ _,
        by rw [h]; exact hD.2 _ hg a haV (by rw [← h]; exact hz2)⟩
    have hzb : z ≠ b := by
      intro h; apply hz3
      exact ⟨by rw [h]; exact Sym2.mem_mk_right _ _,
        by rw [h]; exact hD.2 _ hg b hbV (by rw [← h]; exact hz2)⟩
    have hHz : stH m a b z = 0 := hHseg z hz1'
    obtain ⟨α, β, hα, hβ, hαβ, hzeq⟩ := hz1'
    have hα0 : α ≠ 0 := by
      intro h; apply hzb
      have : β = 1 := by linarith
      rw [← hzeq, h, this]; simp
    have hβ0 : β ≠ 0 := by
      intro h; apply hza
      have : α = 1 := by linarith
      rw [← hzeq, h, this]; simp
    have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
    have hAz : stA m b z = α * stCross (a - m) (b - m) := by
      rw [← hzeq, stA_comb m b a b α β hαβ, stA_a, stA_b]; ring
    have hBz : stB m a z = β * stCross (a - m) (b - m) := by
      rw [← hzeq, stB_comb m a a b α β hαβ, stB_a, stB_b]; ring
    have hAzpos : 0 < stA m b z := by rw [hAz]; exact mul_pos hαpos hc
    have hBzpos : 0 < stB m a z := by rw [hBz]; exact mul_pos hβpos hc
    have hAzc : stA m b z < stCross (a - m) (b - m) := by
      rw [hAz]; nlinarith
    have claim : ∀ p q : Plane, s(p, q) ∈ M → p ∈ V → q ∈ V → s(p, q) ≠ s(a, b) →
        z ∈ segment ℝ p q → z ≠ p → z ≠ q → stH m a b p ≤ stH m a b q → False := by
      intro p q hg' hpV' hqV' hne'' hzpq hzp hzq hle
      obtain ⟨α', β', hα', hβ', hαβ', hzeq'⟩ := hzpq
      have hα'0 : α' ≠ 0 := by
        intro h; apply hzq
        have : β' = 1 := by linarith
        rw [← hzeq', h, this]; simp
      have hβ'0 : β' ≠ 0 := by
        intro h; apply hzp
        have : α' = 1 := by linarith
        rw [← hzeq', h, this]; simp
      have hα'pos : 0 < α' := lt_of_le_of_ne hα' (Ne.symm hα'0)
      have hβ'pos : 0 < β' := lt_of_le_of_ne hβ' (Ne.symm hβ'0)
      have hHz' : 0 = α' * stH m a b p + β' * stH m a b q := by
        rw [← hHz, ← hzeq', stH_comb m a b p q α' β' hαβ']
      by_cases hHq : 0 < stH m a b q
      · have hHp : stH m a b p < 0 := by nlinarith
        have hmp : m ≠ p := by
          intro h; rw [← h, stH_m] at hHp; linarith
        by_cases hqc : 0 ≤ stA m b q ∧ 0 ≤ stB m a q
        · have hqh := st_coords_hull m a b hc hqc.1 hqc.2 hHq.le
          rcases hempty q hqV' hqh with h | h | h
          · -- q = m : the edge pm lies inside the cone
            exfalso
            rw [h] at hzeq' hg'
            have hdec := st_decomp m a b z hc.ne'
            have h2 := sub_eq_of_eq_add' hdec
            have h1 : z - m = α' • (p - m) := by
              rw [← hzeq']
              have : β' = 1 - α' := by linarith
              rw [this]; module
            have hp' : p - m = (α'⁻¹ * (stA m b z / stCross (a - m) (b - m))) • (a - m) +
                (α'⁻¹ * (stB m a z / stCross (a - m) (b - m))) • (b - m) := by
              calc p - m = α'⁻¹ • (α' • (p - m)) := by
                    rw [smul_smul, inv_mul_cancel₀ hα'pos.ne', one_smul]
                _ = α'⁻¹ • (z - m) := by rw [h1]
                _ = _ := by rw [h2, smul_add, smul_smul, smul_smul]
            exact hcons p (by rw [Sym2.eq_swap]; exact hg') ⟨α'⁻¹ * (stA m b z / stCross (a - m) (b - m)),
              α'⁻¹ * (stB m a z / stCross (a - m) (b - m)), by positivity, by positivity, hp'⟩
          · rw [h, stH_a] at hHq; exact lt_irrefl _ hHq
          · rw [h, stH_b] at hHq; exact lt_irrefl _ hHq
        · have hq' : stA m b q < 0 ∨ stB m a q < 0 := by
            by_contra hh; push Not at hh; exact hqc hh
          have hmq : m ≠ q := by
            rintro rfl
            rcases hq' with h | h
            · rw [stA_m] at h; exact lt_irrefl _ h
            · rw [stB_m] at h; exact lt_irrefl _ h
          exact st_exit hnc hc hma hmb hg' ⟨α', β', hα', hβ', hαβ', hzeq'⟩ hAzpos hBzpos
            hHz.ge (by rw [hHz]; exact hHq.le) hHq hq' hmp hmq
      · push Not at hHq
        have hHq0 : stH m a b q = 0 := by
          have : stH m a b p ≤ 0 := le_trans hle hHq
          nlinarith
        have hHp0 : stH m a b p = 0 := by nlinarith
        rcases le_total (stA m b p) (stA m b q) with hAle | hAle
        · exact st_collinear_false hD hc haV hbV hempty hpV' hqV' hg' hne'' hHp0 hHq0
            ⟨α', β', hα', hβ', hαβ', hzeq'⟩ hAzpos hAzc hAle
        · refine st_collinear_false hD hc haV hbV hempty hqV' hpV' (by rw [Sym2.eq_swap]; exact hg')
            (by rw [Sym2.eq_swap]; exact hne'') hHq0 hHp0 ?_ hAzpos hAzc hAle
          rw [segment_symm]; exact ⟨α', β', hα', hβ', hαβ', hzeq'⟩
    have hzp : z ≠ p := by
      intro h
      have : p ∈ segment ℝ a b := h ▸ ⟨α, β, hα, hβ, hαβ, hzeq⟩
      rcases hvert p hpV this with h' | h'
      · exact hza (h.trans h')
      · exact hzb (h.trans h')
    have hzq : z ≠ q := by
      intro h
      have : q ∈ segment ℝ a b := h ▸ ⟨α, β, hα, hβ, hαβ, hzeq⟩
      rcases hvert q hqV this with h' | h'
      · exact hza (h.trans h')
      · exact hzb (h.trans h')
    have hz2'' : z ∈ segment ℝ p q := hz2'
    rcases le_total (stH m a b p) (stH m a b q) with hle | hle
    · exact claim p q hg hpV hqV (fun h => hne' (by rw [h])) hz2'' hzp hzq hle
    · refine claim q p (by rw [Sym2.eq_swap]; exact hg) hqV hpV
        (fun h => hne' (by rw [← h, Sym2.eq_swap])) ?_ hzq hzp hle
      rw [segment_symm]; exact hz2''

/-- The ear lemma for a positively oriented triangle. -/
theorem st1b_ear_pos {V : Finset Plane} {M : Finset (Sym2 Plane)} (hD : stDrawing V M)
    (hnc : stCrossingPairs M = ∅) (hmax : ∀ u w, stFree V M u w → s(u, w) ∈ M)
    {m a b : Plane} (hma : s(m, a) ∈ M) (hmb : s(m, b) ∈ M)
    (hc : 0 < stCross (a - m) (b - m))
    (hcons : ∀ x, s(m, x) ∈ M → ¬ stInCone (a - m) (b - m) (x - m)) :
    s(a, b) ∈ M ∧ ∀ w ∈ V, w ∈ convexHull ℝ ({m, a, b} : Set Plane) → w = m ∨ w = a ∨ w = b := by
  have hempty := st_ear_empty hD hnc hmax hc hma hmb hcons
  exact ⟨st_ear_base hD hnc hmax hc hma hmb hcons hempty, hempty⟩

theorem stInCone_swap {u v w : Plane} (h : stInCone u v w) : stInCone v u w := by
  obtain ⟨α, β, hα, hβ, rfl⟩ := h
  exact ⟨β, α, hβ, hα, add_comm _ _⟩

/-- ST1b: Ear lemma. -/
theorem st1b_ear (V : Finset Plane) (M : Finset (Sym2 Plane)) (hD : stDrawing V M)
    (hnc : stCrossingPairs M = ∅) (hmax : ∀ u w, stFree V M u w → s(u, w) ∈ M)
    {m a b : Plane} (hma : s(m, a) ∈ M) (hmb : s(m, b) ∈ M)
    (hcr : stCross (a - m) (b - m) ≠ 0)
    (hcons : ∀ x, s(m, x) ∈ M → ¬ stInCone (a - m) (b - m) (x - m)) :
    s(a, b) ∈ M ∧ ∀ w ∈ V, w ∈ convexHull ℝ ({m, a, b} : Set Plane) → w = m ∨ w = a ∨ w = b := by
  rcases lt_or_gt_of_ne hcr with hneg | hpos
  · have hc' : 0 < stCross (b - m) (a - m) := by
      have : stCross (b - m) (a - m) = - stCross (a - m) (b - m) := by simp [stCross]; ring
      rw [this]; linarith
    obtain ⟨h1, h2⟩ := st1b_ear_pos hD hnc hmax hmb hma hc'
      (fun x hx h => hcons x hx (stInCone_swap h))
    refine ⟨by rw [Sym2.eq_swap]; exact h1, ?_⟩
    intro w hw hwh
    have hs : ({m, a, b} : Set Plane) = {m, b, a} := by ext; simp; tauto
    rw [hs] at hwh
    rcases h2 w hw hwh with h | h | h <;> tauto
  · exact st1b_ear_pos hD hnc hmax hma hmb hpos hcons

/-- A generic shear makes the x-coordinate injective on a finite set. -/
theorem st_exists_generic (V : Finset Plane) :
    ∃ ε : ℝ, Set.InjOn (fun p : Plane => p 0 + ε * p 1) V := by
  classical
  obtain ⟨ε, hε⟩ := Infinite.exists_notMem_finset
    ((V ×ˢ V).image (fun pq : Plane × Plane => (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1)))
  refine ⟨ε, fun p hp q hq hpq => ?_⟩
  by_contra hne
  simp only at hpq
  apply hε
  rw [Finset.mem_image]
  refine ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
  simp only
  by_cases h1 : p 1 = q 1
  · exfalso
    apply hne
    have h0 : p 0 = q 0 := by rw [h1] at hpq; linarith
    ext i
    fin_cases i
    · exact h0
    · exact h1
  · have : p 1 - q 1 ≠ 0 := sub_ne_zero.mpr h1
    rw [div_eq_iff this]
    linarith


/-- ST1 : plane straight-line graphs have at most `3|V|` edges. -/
theorem st1_planar3 (V : Finset Plane) (E : Finset (Sym2 Plane))
    (hD : stDrawing V E) (hnc : stCrossingPairs E = ∅) : E.card ≤ 3 * V.card := by
  obtain ⟨M, hEM, hDM, hncM, hmax⟩ := st1a_maximal V E hD hnc
  obtain ⟨ε, hε⟩ := st_exists_generic V
  have h := st1c_count V M hDM hncM ε hε
    (fun m a b hma hmb hcr hcons => st1b_ear V M hDM hncM hmax hma hmb hcr hcons)
  exact (Finset.card_le_card hEM).trans h

theorem st1_planar (V : Finset Plane) (E : Finset (Sym2 Plane))
    (hD : stDrawing V E) (hnc : stCrossingPairs E = ∅) : E.card ≤ 4 * V.card := by
  have := st1_planar3 V E hD hnc
  omega

/-- Parent reduction: Theorem 1 follows from ST2 and ST3 with `c₁ = 9`. -/
theorem st_parent_of
    (h2 : ∀ (V : Finset Plane) (E : Finset (Sym2 Plane)), stDrawing V E → 8 * V.card ≤ E.card →
      (E.card : ℝ) ^ 3 / (128 * (V.card : ℝ) ^ 2) ≤ (stCrossingPairs E).card)
    (h3 : ∀ (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)), (∀ l ∈ L, IsLine l) →
      ∃ E : Finset (Sym2 Plane), stDrawing P E ∧
        (incidences P L : ℝ) - L.card ≤ E.card ∧
        ((stCrossingPairs E).card : ℝ) ≤ (L.card : ℝ) ^ 2) :
    ∃ c₁ : ℝ, ∀ (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)),
      (∀ l ∈ L, IsLine l) →
      Real.sqrt (P.card : ℝ) ≤ (L.card : ℝ) →
      L.card ≤ P.card.choose 2 →
      (incidences P L : ℝ) ≤ c₁ * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ) := by
  refine ⟨9, fun P L hL hsq hch => ?_⟩
  set n : ℝ := (P.card : ℝ) with hn
  set t : ℝ := (L.card : ℝ) with ht
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  set A : ℝ := n ^ (2 / 3 : ℝ) * t ^ (2 / 3 : ℝ) with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg ht0 _)
  have hcube : ∀ x : ℝ, 0 ≤ x → (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hA3 : A ^ 3 = n ^ 2 * t ^ 2 := by
    rw [hA, mul_pow, hcube n hn0, hcube t ht0]
  -- n ≤ t^2 and t ≤ n^2
  have hnt : n ≤ t ^ 2 := by
    calc n = (Real.sqrt n) ^ 2 := (Real.sq_sqrt hn0).symm
      _ ≤ t ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  have htn : t ≤ n ^ 2 := by
    have h1 : (L.card : ℝ) ≤ ((P.card.choose 2 : ℕ) : ℝ) := by exact_mod_cast hch
    have h2' : ((P.card.choose 2 : ℕ) : ℝ) ≤ (P.card : ℝ) ^ 2 / ((Nat.factorial 2 : ℕ) : ℝ) :=
      Nat.choose_le_pow_div 2 P.card
    have hf : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hf] at h2'
    have hsq0 : 0 ≤ (P.card : ℝ) ^ 2 := by positivity
    rw [ht, hn]; linarith
  have hnA : n ≤ A := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hA0
    rw [hA3]
    have : n ^ 3 = n * n ^ 2 := by ring
    rw [this]
    calc n * n ^ 2 ≤ t ^ 2 * n ^ 2 := mul_le_mul_of_nonneg_right hnt (by positivity)
      _ = n ^ 2 * t ^ 2 := by ring
  have htA : t ≤ A := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hA0
    rw [hA3]
    have : t ^ 3 = t * t ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right htn (by positivity)
  obtain ⟨E, hD, hI, hcr⟩ := h3 P L hL
  have goalA : (incidences P L : ℝ) ≤ 9 * A := by
    by_cases hP : P.card = 0
    · have : P = ∅ := Finset.card_eq_zero.mp hP
      have hI0 : incidences P L = 0 := by
        unfold incidences; rw [this]; simp
      rw [hI0]; push_cast; linarith
    have hnpos : 0 < n := by rw [hn]; exact_mod_cast Nat.pos_of_ne_zero hP
    by_cases h4 : 8 * P.card ≤ E.card
    · have hc := h2 P E hD h4
      have he : (E.card : ℝ) ≤ 6 * A := by
        apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
        have hpos : 0 < 128 * n ^ 2 := by positivity
        have : (E.card : ℝ) ^ 3 ≤ 128 * n ^ 2 * t ^ 2 := by
          have h' : (E.card : ℝ) ^ 3 / (128 * n ^ 2) ≤ t ^ 2 := le_trans hc hcr
          rw [div_le_iff₀ hpos] at h'
          linarith
        calc (E.card : ℝ) ^ 3 ≤ 128 * n ^ 2 * t ^ 2 := this
          _ ≤ (6 * A) ^ 3 := by
            rw [mul_pow, hA3]
            have : 0 ≤ n ^ 2 * t ^ 2 := by positivity
            nlinarith
      linarith
    · push Not at h4
      have : (E.card : ℝ) < 8 * n := by rw [hn]; exact_mod_cast h4
      linarith
  calc (incidences P L : ℝ) ≤ 9 * A := goalA
    _ = 9 * n ^ (2 / 3 : ℝ) * t ^ (2 / 3 : ℝ) := by rw [hA]; ring


end SzemerediTrotterHelpers

open SzemerediTrotter.Incidence in
theorem solution : ∃ c₁ : ℝ, ∀ (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)),
      (∀ l ∈ L, IsLine l) →
      Real.sqrt (P.card : ℝ) ≤ (L.card : ℝ) →
      L.card ≤ P.card.choose 2 →
      (incidences P L : ℝ) ≤ c₁ * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ) := by
  exact st_parent_of (fun V E hD h4 => st2_crossing_lemma st1_planar V E hD h4) st3_incidence_graph
