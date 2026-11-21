-- Prove2me | solution 1 for ReconfRes.Frozen.lemma_3_62
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-21T00:05:12.806848+00:00
-- url     : https://prove2.me/submissions/6cb033ab-0fc6-4046-b55f-5524e81b43cc

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_VertexCover
import Definitions.Def_ReconfRes_Frozen_Construction

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-!
Blueprint for `ReconfRes.Frozen.lemma_3_62` (canonical paths at locality two).

Everything happens at the level of comb proofs given by event lists (`Event`, `combNodes`,
`combParents`, `combLabel`, `IsCombPresentation` of the bundle).

* **Part G (generic combs).** `CombValid` is a concrete, checkable condition on an event list
  (sources used exactly once, private units are units whose negated fact is present, every goal
  pivot is present, all goal clauses have width `≤ w`, the last goal clause is empty, size bound).
  A valid comb has a presentation, every presentation is an indexed vertex, and two presentations
  are one isomorphism step apart.  `IsCombMove` is a frozen move written in comb coordinates; the
  three shapes of two-inference moves used (adjacent goal swap, adjacent private swap, absorbing a
  goal unit into the private chain of the neighbouring event, before or after it) are comb moves,
  and validity transfers along them under local checks.
* **Part C (clause calculus of the construction).** Before the `A` event every goal clause is
  `headPart (expanded heads) ∪ {¬f_v : v ∈ bag}`, of width `β + r·[U expanded] + |bag|`.
* **Part K (canonical proofs are valid).**
* **Parts S, D (the path).** Sorting the four set orders by adjacent exchanges, and the deletion of
  one selected vertex `v` in five phases (paper p. 81).
-/
/-! ## Part G: generic comb proofs -/
/-- One goal-path step (the body of `goalLabel`'s fold). -/
def stepG (inv : ι → Clause V) (g : Clause V) (e : Event ι V) : Clause V :=
  (sideLabel inv e e.prep.length).erase (e.pivot, true) ∪ g.erase (e.pivot, false)

theorem goalLabel_eq_foldl (inv : ι → Clause V) (start : ι) (es : List (Event ι V)) :
    goalLabel inv start es = es.foldl (stepG inv) (inv start) := rfl

theorem goalLabel_snoc (inv : ι → Clause V) (start : ι) (p : List (Event ι V)) (e : Event ι V) :
    goalLabel inv start (p ++ [e]) = stepG inv (goalLabel inv start p) e := by
  simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The source list of a comb: the start, then for each event its side source and its private
units. -/
def srcList (start : ι) (es : List (Event ι V)) : List ι :=
  start :: es.flatMap (fun e => e.side :: e.prep.map Prod.fst)

/-- The private chain of an event is well formed and supplies its pivot. -/
def EventOK (inv : ι → Clause V) (e : Event ι V) : Prop :=
  (∀ l u t, e.prep = l ++ u :: t →
    inv u.1 = {(u.2, true)} ∧ (u.2, false) ∈ sideLabel inv e l.length) ∧
  (e.pivot, true) ∈ sideLabel inv e e.prep.length

/-- A valid comb: every presentation is an indexed vertex of `G^fr(F, w, s)` (see
`presentation_vertex`). -/
def CombValid (inv : ι → Clause V) (S : Finset ι) (start : ι) (F : CNF V) (w s : ℕ)
    (es : List (Event ι V)) : Prop :=
  (srcList start es).Nodup ∧ (srcList start es).toFinset = S ∧
  (∀ x ∈ S, inv x ∈ F ∧ (inv x).card ≤ w) ∧
  (∀ e ∈ es, EventOK inv e) ∧
  (∀ p e t, es = p ++ e :: t →
    (e.pivot, false) ∈ goalLabel inv start p ∧ (goalLabel inv start (p ++ [e])).card ≤ w) ∧
  goalLabel inv start es = ∅ ∧
  2 * S.card ≤ s + 1

/-- Every pair of presentations of `es`, `es'` is one indexed frozen step apart. -/
def CombStep (k : ℕ) (F : CNF V) (w s : ℕ) (inv : ι → Clause V) (S : Finset ι) (start : ι)
    (es es' : List (Event ι V)) : Prop :=
  ∀ (R : ProofDag V) (pos : ι → Fin R.n) (R' : ProofDag V) (pos' : ι → Fin R'.n),
    IsCombPresentation inv S start es R pos → IsCombPresentation inv S start es' R' pos' →
    IndexedFrozenStep k F w s inv S ⟨R, pos⟩ ⟨R', pos'⟩

/-- Every pair of presentations of `es`, `es'` is joined by an indexed frozen path. -/
def CombJoined (k : ℕ) (F : CNF V) (w s : ℕ) (inv : ι → Clause V) (S : Finset ι) (start : ι)
    (es es' : List (Event ι V)) : Prop :=
  ∀ (R : ProofDag V) (pos : ι → Fin R.n) (R' : ProofDag V) (pos' : ι → Fin R'.n),
    IsCombPresentation inv S start es R pos → IsCombPresentation inv S start es' R' pos' →
    IndexedFrozenConnected k F w s inv S ⟨R, pos⟩ ⟨R', pos'⟩

/-- Both combs are valid and all their presentations are joined. -/
def CombLink (k : ℕ) (F : CNF V) (w s : ℕ) (inv : ι → Clause V) (S : Finset ι) (start : ι)
    (es es' : List (Event ι V)) : Prop :=
  CombValid inv S start F w s es ∧ CombValid inv S start F w s es' ∧
    CombJoined k F w s inv S start es es'

/-- A frozen move of locality at most two written in comb coordinates: blocks `B ⊆ combNodes es`,
`B' ⊆ combNodes es'` of at most two inference nodes, with outputs `o`, `o'` (every other block node
is a parent of the output and has all its consumers in the block), and `σ` identifying the other
nodes, keeping labels, parent relations, the sources, the sink, and sending consumers of `o` to
consumers of `o'`; premises of `B'` from outside are inputs of `B`. -/
def IsCombMove (inv : ι → Clause V) (S : Finset ι) (start : ι) (es es' : List (Event ι V))
    (B B' : Finset (CombNode ι)) (o o' : CombNode ι) (σ : CombNode ι → CombNode ι) : Prop :=
  B ⊆ combNodes S es ∧ B' ⊆ combNodes S es' ∧ B.card ≤ 2 ∧ B'.card ≤ 2 ∧
  (∀ x ∈ B, (combParents start es x).Nonempty) ∧
  (∀ x ∈ B', (combParents start es' x).Nonempty) ∧
  o ∈ B ∧ o' ∈ B' ∧
  (∀ x ∈ B, x = o ∨ x ∈ combParents start es o) ∧
  (∀ x ∈ B', x = o' ∨ x ∈ combParents start es' o') ∧
  (∀ x ∈ B, x ≠ o → ∀ c ∈ combNodes S es, x ∈ combParents start es c → c ∈ B) ∧
  (∀ x ∈ B', x ≠ o' → ∀ c ∈ combNodes S es', x ∈ combParents start es' c → c ∈ B') ∧
  Set.BijOn σ (↑(combNodes S es \ B) : Set (CombNode ι)) (↑(combNodes S es' \ B')) ∧
  (∀ x ∈ combNodes S es \ B, combLabel inv start es' (σ x) = combLabel inv start es x) ∧
  combLabel inv start es' o' = combLabel inv start es o ∧
  (∀ x ∈ combNodes S es \ B, ∀ y ∈ combNodes S es \ B,
    σ x ∈ combParents start es' (σ y) ↔ x ∈ combParents start es y) ∧
  (∀ x ∈ combNodes S es \ B, ∀ y ∈ B', σ x ∈ combParents start es' y →
    ∃ z ∈ B, x ∈ combParents start es z) ∧
  (∀ c ∈ combNodes S es \ B, o' ∈ combParents start es' (σ c) ↔ o ∈ combParents start es c) ∧
  (combSink start es ∉ B → σ (combSink start es) = combSink start es') ∧
  (combSink start es ∈ B → combSink start es = o ∧ combSink start es' = o') ∧
  ∀ x ∈ S, σ (CombNode.src x) = CombNode.src x

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGA
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### Basic facts on proof DAGs -/
theorem mem_parents' (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers' (R : ProofDag V) (i j : Fin R.n) :
    j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem anc_edge {R : ProofDag V} {a b : Fin R.n} (h : (a, b) ∈ R.edges) : R.Anc a b :=
  Relation.ReflTransGen.single h

theorem anc_trans {R : ProofDag V} {a b c : Fin R.n} (h₁ : R.Anc a b) (h₂ : R.Anc b c) :
    R.Anc a c :=
  Relation.ReflTransGen.trans h₁ h₂

/-! ### Comb nodes, parents, labels -/
theorem src_mem_combNodes {S : Finset ι} {es : List (Event ι V)} {s : ι} :
    CombNode.src s ∈ combNodes S es ↔ s ∈ S := by
  simp [combNodes]

theorem pr_mem_combNodes {S : Finset ι} {es : List (Event ι V)} {i j : ℕ} :
    CombNode.pr i j ∈ combNodes S es ↔ i < es.length ∧ j < prepLen es i := by
  simp [combNodes]

theorem gl_mem_combNodes {S : Finset ι} {es : List (Event ι V)} {i : ℕ} :
    CombNode.gl i ∈ combNodes S es ↔ i < es.length := by
  simp [combNodes]

theorem prepLen_eq {es : List (Event ι V)} {i : ℕ} (hi : i < es.length) :
    prepLen es i = es[i].prep.length := by
  simp [prepLen, List.getElem?_eq_getElem hi]

theorem combParents_src (start : ι) (es : List (Event ι V)) (s : ι) :
    combParents start es (CombNode.src s) = ∅ := rfl

theorem combParents_pr (start : ι) {es : List (Event ι V)} {i j : ℕ} (hi : i < es.length)
    (hj : j < es[i].prep.length) :
    combParents start es (CombNode.pr i j) =
      {if j = 0 then CombNode.src es[i].side else CombNode.pr i (j - 1),
        CombNode.src (es[i].prep[j]).1} := by
  simp only [combParents, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]
  rfl

theorem combParents_gl (start : ι) {es : List (Event ι V)} {i : ℕ} (hi : i < es.length) :
    combParents start es (CombNode.gl i) =
      {if i = 0 then CombNode.src start else CombNode.gl (i - 1),
       if es[i].prep.length = 0 then CombNode.src es[i].side
         else CombNode.pr i (es[i].prep.length - 1)} := by
  simp only [combParents, List.getElem?_eq_getElem hi]

theorem foldl_erase_subset (l : List (ι × V)) (c : Clause V) :
    l.foldl (fun c u => c.erase (u.2, false)) c ⊆ c := by
  induction l generalizing c with
  | nil => exact Finset.Subset.refl _
  | cons a t ih => exact (ih _).trans (Finset.erase_subset _ _)

theorem sideLabel_subset (inv : ι → Clause V) (ev : Event ι V) (j : ℕ) :
    sideLabel inv ev j ⊆ inv ev.side :=
  foldl_erase_subset _ _

theorem sideLabel_zero (inv : ι → Clause V) (ev : Event ι V) :
    sideLabel inv ev 0 = inv ev.side := by
  simp [sideLabel]

theorem sideLabel_succ (inv : ι → Clause V) (ev : Event ι V) {j : ℕ} (hj : j < ev.prep.length) :
    sideLabel inv ev (j + 1) = (sideLabel inv ev j).erase (ev.prep[j].2, false) := by
  simp only [sideLabel, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem combLabel_pr (inv : ι → Clause V) (start : ι) {es : List (Event ι V)} {i : ℕ}
    (hi : i < es.length) (j : ℕ) :
    combLabel inv start es (CombNode.pr i j) = sideLabel inv es[i] (j + 1) := by
  simp [combLabel, List.getElem?_eq_getElem hi]

theorem take_succ_eq {es : List (Event ι V)} {i : ℕ} (hi : i < es.length) :
    es.take (i + 1) = es.take i ++ [es[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl

theorem decomp {es : List (Event ι V)} {i : ℕ} (hi : i < es.length) :
    es = es.take i ++ es[i] :: es.drop (i + 1) := by
  conv_lhs => rw [← List.take_append_drop i es]
  rw [List.drop_eq_getElem_cons hi]

theorem decompP {l : List (ι × V)} {j : ℕ} (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  conv_lhs => rw [← List.take_append_drop j l]
  rw [List.drop_eq_getElem_cons hj]

/-! ### Source lists -/
theorem start_mem_srcList (start : ι) (es : List (Event ι V)) : start ∈ srcList start es :=
  List.mem_cons_self

theorem side_mem_srcList {start : ι} {es : List (Event ι V)} {ev : Event ι V} (h : ev ∈ es) :
    ev.side ∈ srcList start es := by
  simp only [srcList, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨ev, h, Or.inl rfl⟩

theorem prep_mem_srcList {start : ι} {es : List (Event ι V)} {ev : Event ι V} (h : ev ∈ es)
    {u : ι × V} (hu : u ∈ ev.prep) : u.1 ∈ srcList start es := by
  simp only [srcList, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨ev, h, Or.inr (List.mem_map_of_mem hu)⟩

theorem mem_srcList {start x : ι} {es : List (Event ι V)} (h : x ∈ srcList start es) :
    x = start ∨ ∃ i, ∃ hi : i < es.length,
      x = es[i].side ∨ ∃ j, ∃ hj : j < es[i].prep.length, x = (es[i].prep[j]).1 := by
  simp only [srcList, List.mem_cons, List.mem_flatMap] at h
  rcases h with h | ⟨ev, hev, hx⟩
  · exact Or.inl h
  · right
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hev
    refine ⟨i, hi, ?_⟩
    rcases hx with h | h
    · exact Or.inl h
    · right
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hu
      exact ⟨j, hj, rfl⟩

theorem start_ne_side {start : ι} {es : List (Event ι V)} (hnd : (srcList start es).Nodup)
    {ev : Event ι V} (h : ev ∈ es) : start ≠ ev.side := by
  intro heq
  have h1 := (List.nodup_cons.1 hnd).1
  apply h1
  rw [heq]
  exact List.mem_flatMap.2 ⟨ev, h, List.mem_cons_self⟩

theorem side_ne_prep {start : ι} {es : List (Event ι V)} (hnd : (srcList start es).Nodup)
    {ev : Event ι V} (h : ev ∈ es) {u : ι × V} (hu : u ∈ ev.prep) : ev.side ≠ u.1 := by
  intro heq
  have h1 := ((List.nodup_flatMap.1 (List.nodup_cons.1 hnd).2).1 ev h)
  apply (List.nodup_cons.1 h1).1
  rw [heq]
  exact List.mem_map_of_mem hu

theorem length_flatMap_src (es : List (Event ι V)) :
    (es.flatMap (fun e => e.side :: e.prep.map Prod.fst)).length =
      es.length + (es.map fun e => e.prep.length).sum := by
  induction es with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]; omega

theorem sum_prepLen (es : List (Event ι V)) :
    ∑ i ∈ Finset.range es.length, prepLen es i = (es.map fun e => e.prep.length).sum := by
  induction es with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp [prepLen] at ih ⊢
    rw [← ih]; omega

end ReconfRes.Frozen.Dev.Q427d.PartGA
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGA
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
variable {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V} {w s : ℕ}
  {es : List (Event ι V)}
/-! ### Facts from validity -/
theorem valid_mem_S (h : CombValid inv S start F w s es) {x : ι} (hx : x ∈ srcList start es) :
    x ∈ S := by
  rw [← h.2.1]; exact List.mem_toFinset.2 hx

theorem valid_S_mem (h : CombValid inv S start F w s es) {x : ι} (hx : x ∈ S) :
    x ∈ srcList start es := by
  rw [← h.2.1] at hx; exact List.mem_toFinset.1 hx

theorem valid_pivot (h : CombValid inv S start F w s es) {i : ℕ} (hi : i < es.length) :
    (es[i].pivot, false) ∈ goalLabel inv start (es.take i) :=
  (h.2.2.2.2.1 _ _ _ (decomp hi)).1

theorem valid_width (h : CombValid inv S start F w s es) {i : ℕ} (hi : i < es.length) :
    (goalLabel inv start (es.take (i + 1))).card ≤ w := by
  rw [take_succ_eq hi]
  exact (h.2.2.2.2.1 _ _ _ (decomp hi)).2

theorem valid_eventOK (h : CombValid inv S start F w s es) {i : ℕ} (hi : i < es.length) :
    EventOK inv es[i] :=
  h.2.2.2.1 _ (List.getElem_mem hi)

theorem valid_unit (h : CombValid inv S start F w s es) {i : ℕ} (hi : i < es.length) {j : ℕ}
    (hj : j < es[i].prep.length) :
    inv (es[i].prep[j]).1 = {((es[i].prep[j]).2, true)} ∧
      ((es[i].prep[j]).2, false) ∈ sideLabel inv es[i] j := by
  have := (valid_eventOK h hi).1 _ _ _ (decompP hj)
  rwa [List.length_take, min_eq_left hj.le] at this

theorem valid_start_mem (h : CombValid inv S start F w s es) : start ∈ S :=
  valid_mem_S h (start_mem_srcList _ _)

theorem valid_side_mem (h : CombValid inv S start F w s es) {i : ℕ} (hi : i < es.length) :
    es[i].side ∈ S :=
  valid_mem_S h (side_mem_srcList (List.getElem_mem hi))

theorem valid_prep_mem (h : CombValid inv S start F w s es) {i : ℕ} (hi : i < es.length) {j : ℕ}
    (hj : j < es[i].prep.length) : (es[i].prep[j]).1 ∈ S :=
  valid_mem_S h (prep_mem_srcList (List.getElem_mem hi) (List.getElem_mem hj))

theorem valid_closure (h : CombValid inv S start F w s es) {y : CombNode ι}
    (hy : y ∈ combNodes S es) : combParents start es y ⊆ combNodes S es := by
  intro x hx
  cases y with
  | src t => simp [combParents_src] at hx
  | pr i j =>
    obtain ⟨hi, hj⟩ := pr_mem_combNodes.1 hy
    rw [prepLen_eq hi] at hj
    rw [combParents_pr start hi hj] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · split_ifs with h0
      · exact src_mem_combNodes.2 (valid_side_mem h hi)
      · exact pr_mem_combNodes.2 ⟨hi, by rw [prepLen_eq hi]; omega⟩
    · exact src_mem_combNodes.2 (valid_prep_mem h hi hj)
  | gl i =>
    have hi := gl_mem_combNodes.1 hy
    rw [combParents_gl start hi] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · split_ifs with h0
      · exact src_mem_combNodes.2 (valid_start_mem h)
      · exact gl_mem_combNodes.2 (by omega)
    · split_ifs with h0
      · exact src_mem_combNodes.2 (valid_side_mem h hi)
      · exact pr_mem_combNodes.2 ⟨hi, by rw [prepLen_eq hi]; omega⟩

theorem combSink_mem (h : CombValid inv S start F w s es) : combSink start es ∈ combNodes S es := by
  unfold combSink
  split_ifs with h0
  · exact src_mem_combNodes.2 (valid_start_mem h)
  · exact gl_mem_combNodes.2 (by omega)

theorem goalLabel_subset (h : CombValid inv S start F w s es) (p : List (Event ι V))
    (hp : ∀ ev ∈ p, ev ∈ es) : goalLabel inv start p ⊆ S.biUnion inv := by
  induction p using List.reverseRecOn with
  | nil => exact Finset.subset_biUnion_of_mem inv (valid_start_mem h)
  | append_singleton p ev ih =>
    rw [goalLabel_snoc]
    have hev : ev ∈ es := hp ev (by simp)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hev
    refine Finset.union_subset ?_ ?_
    · exact (Finset.erase_subset _ _).trans ((sideLabel_subset _ _ _).trans
        (Finset.subset_biUnion_of_mem inv (valid_side_mem h hi)))
    · exact (Finset.erase_subset _ _).trans (ih fun e he => hp e (by simp [he]))

theorem combLabel_subset (h : CombValid inv S start F w s es) {x : CombNode ι}
    (hx : x ∈ combNodes S es) : combLabel inv start es x ⊆ S.biUnion inv := by
  cases x with
  | src t => exact Finset.subset_biUnion_of_mem inv (src_mem_combNodes.1 hx)
  | pr i j =>
    obtain ⟨hi, -⟩ := pr_mem_combNodes.1 hx
    rw [combLabel_pr inv start hi]
    exact (sideLabel_subset _ _ _).trans (Finset.subset_biUnion_of_mem inv (valid_side_mem h hi))
  | gl i => exact goalLabel_subset h _ fun e he => List.mem_of_mem_take he

theorem combLabel_card (h : CombValid inv S start F w s es) {x : CombNode ι}
    (hx : x ∈ combNodes S es) : (combLabel inv start es x).card ≤ w := by
  cases x with
  | src t => exact (h.2.2.1 t (src_mem_combNodes.1 hx)).2
  | pr i j =>
    obtain ⟨hi, -⟩ := pr_mem_combNodes.1 hx
    rw [combLabel_pr inv start hi]
    exact (Finset.card_le_card (sideLabel_subset _ _ _)).trans
      (h.2.2.1 _ (valid_side_mem h hi)).2
  | gl i => exact valid_width h (gl_mem_combNodes.1 hx)

end ReconfRes.Frozen.Dev.Q427d.PartGA
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGA
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
variable {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V} {w s : ℕ}
  {es : List (Event ι V)} {R : ProofDag V} {e : CombNode ι → Fin R.n}
/-! ### Presentations -/
theorem pres_parents (h : CombValid inv S start F w s es)
    (hbij : Set.BijOn e (combNodes S es : Set (CombNode ι)) Set.univ)
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y))
    {y : CombNode ι} (hy : y ∈ combNodes S es) :
    R.parents (e y) = (combParents start es y).image e := by
  ext a
  obtain ⟨x, hx, rfl⟩ := hbij.surjOn (Set.mem_univ a)
  rw [mem_parents', hedge x hx y hy, Finset.mem_image]
  constructor
  · intro hp; exact ⟨x, hp, rfl⟩
  · rintro ⟨x', hx', he⟩
    have := hbij.injOn (Finset.mem_coe.2 (valid_closure h hy hx')) hx he
    subst this; exact hx'

theorem pres_edge
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y))
    {x y : CombNode ι} (hx : x ∈ combNodes S es) (hy : y ∈ combNodes S es)
    (hp : x ∈ combParents start es y) : R.Anc (e x) (e y) :=
  anc_edge ((hedge x hx y hy).2 hp)

/-- A rank strictly increasing along comb parent edges. -/
def kappa (es : List (Event ι V)) : CombNode ι → ℕ ×ₗ ℕ
  | .src _ => toLex (0, 0)
  | .pr i j => toLex (i + 1, j)
  | .gl i => toLex (i + 1, prepLen es i)

theorem kappa_lt {y x : CombNode ι} (hy : y ∈ combNodes S es)
    (hx : x ∈ combParents start es y) : kappa es x < kappa es y := by
  cases y with
  | src t => simp [combParents_src] at hx
  | pr i j =>
    obtain ⟨hi, hj⟩ := pr_mem_combNodes.1 hy
    rw [prepLen_eq hi] at hj
    rw [combParents_pr start hi hj] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · split_ifs with h0
      · simp [kappa, Prod.Lex.toLex_lt_toLex]
      · simp [kappa, Prod.Lex.toLex_lt_toLex]; omega
    · simp [kappa, Prod.Lex.toLex_lt_toLex]
  | gl i =>
    have hi := gl_mem_combNodes.1 hy
    rw [combParents_gl start hi] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · split_ifs with h0
      · simp [kappa, Prod.Lex.toLex_lt_toLex]
      · simp [kappa, Prod.Lex.toLex_lt_toLex]; omega
    · split_ifs with h0
      · simp [kappa, Prod.Lex.toLex_lt_toLex]
      · simp [kappa, Prod.Lex.toLex_lt_toLex, prepLen_eq hi]; omega

theorem pres_acyclic
    (hbij : Set.BijOn e (combNodes S es : Set (CombNode ι)) Set.univ)
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y)) :
    ∀ a b, (a, b) ∈ R.edges → R.Anc b a → False := by
  have : Nonempty (CombNode ι) := ⟨CombNode.gl 0⟩
  have hinv : ∀ a, Function.invFunOn e (combNodes S es : Set (CombNode ι)) a ∈ combNodes S es ∧
      e (Function.invFunOn e (combNodes S es : Set (CombNode ι)) a) = a := fun a =>
    ⟨Function.invFunOn_mem (hbij.surjOn (Set.mem_univ a)),
      Function.invFunOn_eq (hbij.surjOn (Set.mem_univ a))⟩
  let κR : Fin R.n → ℕ ×ₗ ℕ := fun a =>
    kappa es (Function.invFunOn e (combNodes S es : Set (CombNode ι)) a)
  have hlt : ∀ a b, (a, b) ∈ R.edges → κR a < κR b := by
    intro a b hab
    obtain ⟨ha, ea⟩ := hinv a
    obtain ⟨hb, eb⟩ := hinv b
    rw [← ea, ← eb] at hab
    exact kappa_lt hb ((hedge _ ha _ hb).1 hab)
  have hmono : ∀ c d, R.Anc c d → κR c ≤ κR d := by
    intro c d hcd
    induction hcd with
    | refl => exact le_rfl
    | tail _ hcd ih => exact ih.trans (hlt _ _ hcd).le
  intro a b hab hba
  exact absurd (hlt a b hab) (not_lt.2 (hmono b a hba))

theorem pres_node (h : CombValid inv S start F w s es)
    (hbij : Set.BijOn e (combNodes S es : Set (CombNode ι)) Set.univ)
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y))
    (hlabel : ∀ x ∈ combNodes S es, R.label (e x) = combLabel inv start es x)
    {y : CombNode ι} (hy : y ∈ combNodes S es) :
    (R.parents (e y) = ∅ ∧ R.label (e y) ∈ F) ∨
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ R.parents (e y) = {p₁, p₂} ∧
      ∃ x, ResolventOn x (R.label p₁) (R.label p₂) (R.label (e y))) ∨
    (∃ p, R.parents (e y) = {p} ∧ R.label p ⊆ R.label (e y)) := by
  cases y with
  | src t =>
    left
    refine ⟨?_, ?_⟩
    · rw [pres_parents h hbij hedge hy, combParents_src]; rfl
    · rw [hlabel _ hy]; exact (h.2.2.1 t (src_mem_combNodes.1 hy)).1
  | pr i j =>
    right; left
    obtain ⟨hi, hj⟩ := pr_mem_combNodes.1 hy
    rw [prepLen_eq hi] at hj
    have hA : (if j = 0 then CombNode.src es[i].side else CombNode.pr i (j - 1)) ∈
        combNodes S es :=
      valid_closure h hy (by rw [combParents_pr start hi hj]; simp)
    have hU : CombNode.src (es[i].prep[j]).1 ∈ combNodes S es :=
      valid_closure h hy (by rw [combParents_pr start hi hj]; simp)
    have hne : (if j = 0 then CombNode.src es[i].side else CombNode.pr i (j - 1)) ≠
        CombNode.src (es[i].prep[j]).1 := by
      split_ifs with h0
      · intro heq
        exact side_ne_prep h.1 (List.getElem_mem hi) (List.getElem_mem hj)
          (CombNode.src.inj heq)
      · simp
    have hAlab : combLabel inv start es
        (if j = 0 then CombNode.src es[i].side else CombNode.pr i (j - 1)) =
        sideLabel inv es[i] j := by
      split_ifs with h0
      · subst h0; rw [sideLabel_zero]; rfl
      · rw [combLabel_pr inv start hi]; congr 1; omega
    obtain ⟨hu1, hu2⟩ := valid_unit h hi hj
    refine ⟨e (CombNode.src (es[i].prep[j]).1),
      e (if j = 0 then CombNode.src es[i].side else CombNode.pr i (j - 1)),
      fun heq => hne (hbij.injOn hA hU heq.symm), ?_, (es[i].prep[j]).2, ?_⟩
    · rw [pres_parents h hbij hedge hy, combParents_pr start hi hj, Finset.image_insert,
        Finset.image_singleton, Finset.pair_comm]
    · rw [hlabel _ hU, hlabel _ hA, hlabel _ hy, hAlab, combLabel_pr inv start hi,
        sideLabel_succ _ _ hj]
      show ResolventOn _ (inv _) _ _
      rw [hu1]
      exact ⟨Finset.mem_singleton_self _, hu2, by simp⟩
  | gl i =>
    right; left
    have hi := gl_mem_combNodes.1 hy
    have hP : (if i = 0 then CombNode.src start else CombNode.gl (i - 1)) ∈ combNodes S es :=
      valid_closure h hy (by rw [combParents_gl start hi]; simp)
    have hT : (if es[i].prep.length = 0 then CombNode.src es[i].side
        else CombNode.pr i (es[i].prep.length - 1)) ∈ combNodes S es :=
      valid_closure h hy (by rw [combParents_gl start hi]; simp)
    have hne : (if es[i].prep.length = 0 then CombNode.src es[i].side
        else CombNode.pr i (es[i].prep.length - 1)) ≠
        (if i = 0 then CombNode.src start else CombNode.gl (i - 1)) := by
      split_ifs with h0 h1 h1
      · intro heq
        exact start_ne_side h.1 (List.getElem_mem hi) (CombNode.src.inj heq).symm
      all_goals simp
    have hPlab : combLabel inv start es (if i = 0 then CombNode.src start else CombNode.gl (i - 1)) =
        goalLabel inv start (es.take i) := by
      split_ifs with h0
      · subst h0; rfl
      · show goalLabel inv start (es.take (i - 1 + 1)) = _
        congr 2; omega
    have hTlab : combLabel inv start es (if es[i].prep.length = 0 then CombNode.src es[i].side
        else CombNode.pr i (es[i].prep.length - 1)) =
        sideLabel inv es[i] es[i].prep.length := by
      split_ifs with h0
      · rw [h0, sideLabel_zero]; rfl
      · rw [combLabel_pr inv start hi]; congr 1; omega
    refine ⟨e _, e _, fun heq => hne (hbij.injOn hT hP heq), ?_, es[i].pivot, ?_⟩
    · rw [pres_parents h hbij hedge hy, combParents_gl start hi, Finset.image_insert,
        Finset.image_singleton, Finset.pair_comm]
    · rw [hlabel _ hT, hlabel _ hP, hlabel _ hy, hTlab, hPlab]
      show ResolventOn _ _ _ (goalLabel inv start (es.take (i + 1)))
      rw [take_succ_eq hi, goalLabel_snoc]
      exact ⟨(valid_eventOK h hi).2, valid_pivot h hi, rfl⟩

theorem combSink_of_pos (hl : 0 < es.length) :
    combSink start es = CombNode.gl (es.length - 1) := by
  unfold combSink; rw [if_neg (by omega)]

theorem pres_anc_gl (h : CombValid inv S start F w s es)
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y))
    {i : ℕ} (hi : i < es.length) : R.Anc (e (CombNode.gl i)) (e (combSink start es)) := by
  rw [combSink_of_pos (by omega)]
  have key : ∀ d, i + d < es.length → R.Anc (e (CombNode.gl i)) (e (CombNode.gl (i + d))) := by
    intro d
    induction d with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ d ih =>
      intro hd
      refine anc_trans (ih (by omega)) (pres_edge hedge (gl_mem_combNodes.2 (by omega))
        (gl_mem_combNodes.2 hd) ?_)
      rw [combParents_gl start hd]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      rw [if_neg (by omega)]
      congr 1
  have := key (es.length - 1 - i) (by omega)
  rwa [show i + (es.length - 1 - i) = es.length - 1 by omega] at this

theorem pres_anc_pr (h : CombValid inv S start F w s es)
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y))
    {i j : ℕ} (hi : i < es.length) (hj : j < es[i].prep.length) :
    R.Anc (e (CombNode.pr i j)) (e (combSink start es)) := by
  have hpr : ∀ j, j < es[i].prep.length → CombNode.pr i j ∈ combNodes S es := fun j hj =>
    pr_mem_combNodes.2 ⟨hi, by rw [prepLen_eq hi]; exact hj⟩
  have key : ∀ d, j + d < es[i].prep.length →
      R.Anc (e (CombNode.pr i j)) (e (CombNode.pr i (j + d))) := by
    intro d
    induction d with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ d ih =>
      intro hd
      refine anc_trans (ih (by omega)) (pres_edge hedge (hpr _ (by omega)) (hpr _ hd) ?_)
      rw [combParents_pr start hi hd]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      rw [if_neg (by omega)]
      congr 1
  have h1 := key (es[i].prep.length - 1 - j) (by omega)
  rw [show j + (es[i].prep.length - 1 - j) = es[i].prep.length - 1 by omega] at h1
  refine anc_trans h1 (anc_trans (pres_edge hedge (hpr _ (by omega))
    (gl_mem_combNodes.2 hi) ?_) (pres_anc_gl h hedge hi))
  rw [combParents_gl start hi]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  right
  rw [if_neg (by omega)]

theorem pres_anc_src (h : CombValid inv S start F w s es)
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y))
    {t : ι} (ht : t ∈ S) : R.Anc (e (CombNode.src t)) (e (combSink start es)) := by
  rcases mem_srcList (valid_S_mem h ht) with hst | ⟨i, hi, hside | ⟨j, hj, rfl⟩⟩
  · rw [hst] at ht ⊢
    by_cases hl : es.length = 0
    · unfold combSink; rw [if_pos hl]; exact Relation.ReflTransGen.refl
    · refine anc_trans (pres_edge hedge (src_mem_combNodes.2 ht)
        (gl_mem_combNodes.2 (show 0 < es.length by omega)) ?_)
        (pres_anc_gl h hedge (show 0 < es.length by omega))
      rw [combParents_gl start (show 0 < es.length by omega)]
      simp
  · subst hside
    by_cases hl : es[i].prep.length = 0
    · refine anc_trans (pres_edge hedge (src_mem_combNodes.2 ht) (gl_mem_combNodes.2 hi) ?_)
        (pres_anc_gl h hedge hi)
      rw [combParents_gl start hi]
      simp [hl]
    · have h0 : 0 < es[i].prep.length := by omega
      refine anc_trans (pres_edge hedge (src_mem_combNodes.2 ht)
        (pr_mem_combNodes.2 ⟨hi, by rw [prepLen_eq hi]; exact h0⟩) ?_) (pres_anc_pr h hedge hi h0)
      rw [combParents_pr start hi h0]
      simp
  · refine anc_trans (pres_edge hedge (src_mem_combNodes.2 ht)
      (pr_mem_combNodes.2 ⟨hi, by rw [prepLen_eq hi]; exact hj⟩) ?_) (pres_anc_pr h hedge hi hj)
    rw [combParents_pr start hi hj]
    simp

theorem pres_anc (h : CombValid inv S start F w s es)
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y))
    {x : CombNode ι} (hx : x ∈ combNodes S es) :
    R.Anc (e x) (e (combSink start es)) := by
  cases x with
  | src t => exact pres_anc_src h hedge (src_mem_combNodes.1 hx)
  | pr i j =>
    obtain ⟨hi, hj⟩ := pr_mem_combNodes.1 hx
    rw [prepLen_eq hi] at hj
    exact pres_anc_pr h hedge hi hj
  | gl i => exact pres_anc_gl h hedge (gl_mem_combNodes.1 hx)

theorem sink_not_parent {y : CombNode ι} (hy : y ∈ combNodes S es) :
    combSink start es ∉ combParents start es y := by
  intro hp
  cases y with
  | src t => simp [combParents_src] at hp
  | pr i j =>
    obtain ⟨hi, hj⟩ := pr_mem_combNodes.1 hy
    rw [prepLen_eq hi] at hj
    rw [combParents_pr start hi hj, combSink_of_pos (by omega)] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    split_ifs at hp <;> simp at hp
  | gl i =>
    have hi := gl_mem_combNodes.1 hy
    rw [combParents_gl start hi, combSink_of_pos (by omega)] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    split_ifs at hp with h1 h2 h2 <;> simp at hp <;> omega

theorem card_combNodes_le :
    (combNodes S es).card ≤ S.card + (es.map fun e => e.prep.length).sum + es.length := by
  have h1 : (S.image CombNode.src).card ≤ S.card := Finset.card_image_le
  have h2 : ((Finset.range es.length).biUnion
      (fun i => (Finset.range (prepLen es i)).image (CombNode.pr (ι := ι) i))).card ≤
      ∑ i ∈ Finset.range es.length, prepLen es i :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ =>
      Finset.card_image_le.trans (Finset.card_range _).le)
  have h3 : ((Finset.range es.length).image (CombNode.gl (ι := ι))).card ≤ es.length :=
    Finset.card_image_le.trans (Finset.card_range _).le
  rw [sum_prepLen] at h2
  unfold combNodes
  refine (Finset.card_union_le _ _).trans ?_
  have := Finset.card_union_le (S.image CombNode.src) ((Finset.range es.length).biUnion
      (fun i => (Finset.range (prepLen es i)).image (CombNode.pr (ι := ι) i)))
  omega

theorem valid_card_S (h : CombValid inv S start F w s es) :
    S.card = 1 + es.length + (es.map fun e => e.prep.length).sum := by
  rw [← h.2.1, List.toFinset_card_of_nodup h.1, srcList, List.length_cons, length_flatMap_src]
  omega

end ReconfRes.Frozen.Dev.Q427d.PartGA
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGA
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### G-A targets -/
/-- Indexed frozen steps are symmetric. -/
theorem step_symm {k : ℕ} {F : CNF V} {w s : ℕ} {inv : ι → Clause V} {S : Finset ι}
    {P P' : Σ R : ProofDag V, ι → Fin R.n} (h : IndexedFrozenStep k F w s inv S P P') :
    IndexedFrozenStep k F w s inv S P' P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h2, h1, h4, h3, ?_⟩
  rcases h5 with ⟨e, hl, he, hs, hp⟩ | hm | hm
  · left
    refine ⟨e.symm, fun i => ?_, fun i j => ?_, ?_, fun x hx => ?_⟩
    · have := hl (e.symm i); simp only [Equiv.apply_symm_apply] at this; exact this.symm
    · have := he (e.symm i) (e.symm j); simp only [Equiv.apply_symm_apply] at this
      exact this.symm
    · rw [← hs]; simp
    · rw [← hp x hx]; simp
  · exact Or.inr (Or.inr hm)
  · exact Or.inr (Or.inl hm)

/-- Every presentation of a valid comb is an indexed vertex. -/
theorem presentation_vertex {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V}
    {w s : ℕ} {es : List (Event ι V)} (h : CombValid inv S start F w s es)
    {R : ProofDag V} {pos : ι → Fin R.n} (hR : IsCombPresentation inv S start es R pos) :
    IsVertex F w s R ∧ IsIndexedBy inv S R pos := by
  obtain ⟨e, hbij, hedge, hlabel, hsink, hpos⟩ := hR
  have hsurj : ∀ a : Fin R.n, ∃ y ∈ combNodes S es, e y = a := fun a =>
    hbij.surjOn (Set.mem_univ a)
  refine ⟨⟨⟨pres_acyclic hbij hedge, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- variables
    intro a l hl
    obtain ⟨y, hy, rfl⟩ := hsurj a
    rw [hlabel _ hy] at hl
    have := combLabel_subset h hy hl
    obtain ⟨t, ht, hlt⟩ := Finset.mem_biUnion.1 this
    simp only [vars, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨inv t, (h.2.2.1 t ht).1, l, hlt, rfl⟩
  · intro a
    obtain ⟨y, hy, rfl⟩ := hsurj a
    exact pres_node h hbij hedge hlabel hy
  · ext a
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_consumers']
    obtain ⟨y, hy, rfl⟩ := hsurj a
    rw [hsink, hedge _ (combSink_mem h) _ hy]
    exact sink_not_parent hy
  · rw [hsink, hlabel _ (combSink_mem h)]
    have hg := h.2.2.2.2.2.1
    unfold combSink
    split_ifs with hl
    · rw [List.length_eq_zero_iff] at hl
      subst hl
      exact hg
    · show goalLabel inv start (es.take (es.length - 1 + 1)) = ∅
      rw [Nat.sub_add_cancel (by omega), List.take_length]
      exact hg
  · intro a
    obtain ⟨y, hy, rfl⟩ := hsurj a
    rw [hsink]
    exact pres_anc h hedge hy
  · refine Finset.sup_le fun a _ => ?_
    obtain ⟨y, hy, rfl⟩ := hsurj a
    rw [hlabel _ hy]
    exact combLabel_card h hy
  · have hcard : (combNodes S es).card = R.n := by
      rw [← Fintype.card_fin R.n, ← Finset.card_univ]
      exact Finset.card_bij (fun x _ => e x) (fun _ _ => Finset.mem_univ _)
        (fun a ha b hb hab => hbij.injOn ha hb hab)
        (fun b _ => let ⟨x, hx, hxe⟩ := hbij.surjOn (Set.mem_univ b); ⟨x, hx, hxe⟩)
    have h1 := card_combNodes_le (S := S) (es := es)
    have h2 := valid_card_S h
    have h3 := h.2.2.2.2.2.2
    show R.n ≤ s
    omega
  · intro a ha b hb hab
    rw [hpos a ha, hpos b hb] at hab
    exact CombNode.src.inj (hbij.injOn (src_mem_combNodes.2 ha) (src_mem_combNodes.2 hb) hab)
  · intro j
    obtain ⟨y, hy, rfl⟩ := hsurj j
    unfold ProofDag.IsAxiomNode
    rw [pres_parents h hbij hedge hy, Finset.image_eq_empty]
    constructor
    · intro hp
      cases y with
      | src t => exact ⟨t, src_mem_combNodes.1 hy, hpos t (src_mem_combNodes.1 hy)⟩
      | pr i j =>
        obtain ⟨hi, hj⟩ := pr_mem_combNodes.1 hy
        rw [prepLen_eq hi] at hj
        rw [combParents_pr start hi hj] at hp
        simp at hp
      | gl i =>
        rw [combParents_gl start (gl_mem_combNodes.1 hy)] at hp
        simp at hp
    · rintro ⟨t, ht, hte⟩
      rw [hpos t ht] at hte
      have := hbij.injOn (src_mem_combNodes.2 ht) hy hte
      subst this
      rfl
  · intro t ht
    rw [hpos t ht, hlabel _ (src_mem_combNodes.2 ht)]
    rfl

/-- A valid comb has a presentation. -/
theorem exists_presentation {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V}
    {w s : ℕ} {es : List (Event ι V)} (h : CombValid inv S start F w s es) :
    ∃ (R : ProofDag V) (pos : ι → Fin R.n), IsCombPresentation inv S start es R pos := by
  have hstart : CombNode.src start ∈ combNodes S es := src_mem_combNodes.2 (valid_start_mem h)
  let f := (combNodes S es).equivFin
  let E : CombNode ι → Fin (combNodes S es).card := fun x =>
    if hx : x ∈ combNodes S es then f ⟨x, hx⟩ else f ⟨_, hstart⟩
  have hE : ∀ x (hx : x ∈ combNodes S es), E x = f ⟨x, hx⟩ := fun x hx => dif_pos hx
  let R : ProofDag V :=
    { n := (combNodes S es).card
      label := fun a => combLabel inv start es (f.symm a).1
      edges := Finset.univ.filter fun p =>
        (f.symm p.1).1 ∈ combParents start es (f.symm p.2).1
      sink := E (combSink start es) }
  refine ⟨R, fun t => E (CombNode.src t), E, ⟨?_, ?_, ?_⟩, ?_, ?_, rfl, fun _ _ => rfl⟩
  · intro x _; exact Set.mem_univ _
  · intro x hx y hy hxy
    simp only [hE x hx, hE y hy] at hxy
    exact congrArg Subtype.val (f.injective hxy)
  · intro a _
    refine ⟨(f.symm a).1, (f.symm a).2, ?_⟩
    simp only [hE _ (f.symm a).2, Subtype.coe_eta, Equiv.apply_symm_apply]
  · intro x hx y hy
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, hE x hx, hE y hy,
      Equiv.symm_apply_apply]
  · intro x hx
    simp only [R, hE x hx, Equiv.symm_apply_apply]

end ReconfRes.Frozen.Dev.Q427d.PartGA
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### G-A: presentations -/
alias exists_presentation := ReconfRes.Frozen.Dev.Q427d.PartGA.exists_presentation

alias presentation_vertex := ReconfRes.Frozen.Dev.Q427d.PartGA.presentation_vertex

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGA
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-- Two presentations of one valid comb are one (isomorphism) step apart. -/
theorem iso_step {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V}
    {w s : ℕ} {es : List (Event ι V)} (k : ℕ) (h : CombValid inv S start F w s es) :
    CombStep k F w s inv S start es es := by
  intro R pos R' pos' hR hR'
  obtain ⟨hv, hi⟩ := presentation_vertex h hR
  obtain ⟨hv', hi'⟩ := presentation_vertex h hR'
  refine ⟨hv, hv', hi, hi', Or.inl ?_⟩
  obtain ⟨e₁, hb₁, he₁, hl₁, hs₁, hp₁⟩ := hR
  obtain ⟨e₂, hb₂, he₂, hl₂, hs₂, hp₂⟩ := hR'
  have : Nonempty (CombNode ι) := ⟨CombNode.gl 0⟩
  let g₁ : Fin R.n → CombNode ι := Function.invFunOn e₁ (combNodes S es : Set (CombNode ι))
  let g₂ : Fin R'.n → CombNode ι := Function.invFunOn e₂ (combNodes S es : Set (CombNode ι))
  have hg₁ : ∀ a, g₁ a ∈ combNodes S es ∧ e₁ (g₁ a) = a := fun a =>
    ⟨Function.invFunOn_mem (hb₁.surjOn (Set.mem_univ a)),
      Function.invFunOn_eq (hb₁.surjOn (Set.mem_univ a))⟩
  have hg₂ : ∀ a, g₂ a ∈ combNodes S es ∧ e₂ (g₂ a) = a := fun a =>
    ⟨Function.invFunOn_mem (hb₂.surjOn (Set.mem_univ a)),
      Function.invFunOn_eq (hb₂.surjOn (Set.mem_univ a))⟩
  have hgx₁ : ∀ x ∈ combNodes S es, g₁ (e₁ x) = x := fun x hx =>
    hb₁.injOn.leftInvOn_invFunOn hx
  have hgx₂ : ∀ x ∈ combNodes S es, g₂ (e₂ x) = x := fun x hx =>
    hb₂.injOn.leftInvOn_invFunOn hx
  let φ : Fin R.n ≃ Fin R'.n :=
    { toFun := fun a => e₂ (g₁ a)
      invFun := fun b => e₁ (g₂ b)
      left_inv := fun a => by
        simp only
        rw [hgx₂ _ (hg₁ a).1, (hg₁ a).2]
      right_inv := fun b => by
        simp only
        rw [hgx₁ _ (hg₂ b).1, (hg₂ b).2] }
  have hφ : ∀ x ∈ combNodes S es, φ (e₁ x) = e₂ x := fun x hx => by
    show e₂ (g₁ (e₁ x)) = e₂ x
    rw [hgx₁ x hx]
  have hsurj : ∀ a : Fin R.n, ∃ y ∈ combNodes S es, e₁ y = a := fun a =>
    hb₁.surjOn (Set.mem_univ a)
  refine ⟨φ, fun a => ?_, fun a b => ?_, ?_, fun t ht => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hsurj a
    rw [hφ y hy, hl₁ y hy, hl₂ y hy]
  · obtain ⟨y, hy, rfl⟩ := hsurj a
    obtain ⟨z, hz, rfl⟩ := hsurj b
    rw [hφ y hy, hφ z hz, he₁ y hy z hz, he₂ y hy z hz]
  · rw [hs₁, hs₂, hφ _ (combSink_mem h)]
  · show φ (pos t) = pos' t
    rw [hp₁ t ht, hp₂ t ht, hφ _ (src_mem_combNodes.2 ht)]

end ReconfRes.Frozen.Dev.Q427d.PartGA
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
alias iso_step := ReconfRes.Frozen.Dev.Q427d.PartGA.iso_step

alias step_symm := ReconfRes.Frozen.Dev.Q427d.PartGA.step_symm

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGB
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
theorem combSink_mem' {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V} {w s : ℕ}
    {es : List (Event ι V)} (h : CombValid inv S start F w s es) :
    combSink start es ∈ combNodes S es := by
  unfold combSink
  split_ifs with h0
  · have : start ∈ S := by
      rw [← h.2.1]; simp [srcList]
    simp [combNodes, this]
  · simp [combNodes]; omega

/-- The image of a comb block under a presentation is a block. -/
theorem pres_block {start : ι} {S : Finset ι} {es : List (Event ι V)} {R : ProofDag V}
    {e : CombNode ι → Fin R.n} {k : ℕ}
    (hb : Set.BijOn e (combNodes S es : Set (CombNode ι)) Set.univ)
    (hedge : ∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y))
    {B : Finset (CombNode ι)} {o : CombNode ι} (hBs : B ⊆ combNodes S es) (hBc : B.card ≤ k)
    (ho : o ∈ B) (hBo : ∀ x ∈ B, x = o ∨ x ∈ combParents start es o)
    (hBcons : ∀ x ∈ B, x ≠ o → ∀ c ∈ combNodes S es, x ∈ combParents start es c → c ∈ B) :
    R.IsBlock k (B.image e) (e o) := by
  refine ⟨?_, ⟨Finset.mem_image_of_mem e ho, ?_⟩, ?_⟩
  · exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans hBc)
  · intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    rcases hBo x hx with rfl | hp
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hi, Finset.mem_image_of_mem e ho,
        (hedge x (hBs hx) o (hBs ho)).2 hp⟩
  · intro i hi hne c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    have hxo : x ≠ o := fun h => hne (h ▸ rfl)
    obtain ⟨y, hy, rfl⟩ := hb.surjOn (Set.mem_univ c)
    have hc' : (e x, e y) ∈ R.edges := by simpa [ProofDag.consumers] using hc
    exact Finset.mem_image_of_mem e
      (hBcons x hx hxo y hy ((hedge x (hBs hx) y hy).1 hc'))

/-- Block nodes (having comb parents) are not axiom nodes. -/
theorem pres_noaxiom {inv : ι → Clause V} {S : Finset ι} {start : ι} {es : List (Event ι V)}
    {R : ProofDag V} {pos : ι → Fin R.n} {e : CombNode ι → Fin R.n}
    (hb : Set.BijOn e (combNodes S es : Set (CombNode ι)) Set.univ)
    (hidx : IsIndexedBy inv S R pos) (hp : ∀ s ∈ S, pos s = e (CombNode.src s))
    {B : Finset (CombNode ι)} (hBs : B ⊆ combNodes S es)
    (hBp : ∀ x ∈ B, (combParents start es x).Nonempty) :
    ∀ i ∈ B.image e, ¬ R.IsAxiomNode i := by
  intro i hi hax
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨t, ht, hte⟩ := (hidx.2.1 (e x)).1 hax
  rw [hp t ht] at hte
  have hsrc : CombNode.src t ∈ combNodes S es := by simp [combNodes, ht]
  have := hb.injOn (Finset.mem_coe.2 hsrc) (Finset.mem_coe.2 (hBs hx)) hte
  subst this
  obtain ⟨y, hy⟩ := hBp _ hx
  simp [combParents] at hy

theorem step_of_combMove {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V}
    {w s k : ℕ} (hk : 2 ≤ k) {es es' : List (Event ι V)}
    (h : CombValid inv S start F w s es) (h' : CombValid inv S start F w s es')
    {B B' : Finset (CombNode ι)} {o o' : CombNode ι} {σ : CombNode ι → CombNode ι}
    (hm : IsCombMove inv S start es es' B B' o o' σ) :
    CombStep k F w s inv S start es es' := by
  intro R pos R' pos' hR hR'
  obtain ⟨hv, hi⟩ := presentation_vertex h hR
  obtain ⟨hv', hi'⟩ := presentation_vertex h' hR'
  refine ⟨hv, hv', hi, hi', Or.inr (Or.inl ?_)⟩
  obtain ⟨e, hb, he, hl, hs, hp⟩ := hR
  obtain ⟨e', hb', he', hl', hs', hp'⟩ := hR'
  obtain ⟨hBs, hBs', hBc, hBc', hBp, hBp', ho, ho', hBo, hBo', hBcons, hBcons', hσ, hσl, hol,
    hσe, hσin, hσo, hsk1, hsk2, hσs⟩ := hm
  have : Nonempty (CombNode ι) := ⟨CombNode.gl 0⟩
  set Q := B.image e with hQ
  set Q' := B'.image e' with hQ'
  let g : Fin R.n → CombNode ι := Function.invFunOn e (combNodes S es : Set (CombNode ι))
  let g' : Fin R'.n → CombNode ι := Function.invFunOn e' (combNodes S es' : Set (CombNode ι))
  let τ : CombNode ι → CombNode ι :=
    Function.invFunOn σ (↑(combNodes S es \ B) : Set (CombNode ι))
  have hg : ∀ a, g a ∈ combNodes S es ∧ e (g a) = a := fun a =>
    ⟨Function.invFunOn_mem (hb.surjOn (Set.mem_univ a)),
      Function.invFunOn_eq (hb.surjOn (Set.mem_univ a))⟩
  have hg' : ∀ a, g' a ∈ combNodes S es' ∧ e' (g' a) = a := fun a =>
    ⟨Function.invFunOn_mem (hb'.surjOn (Set.mem_univ a)),
      Function.invFunOn_eq (hb'.surjOn (Set.mem_univ a))⟩
  have hgx : ∀ x ∈ combNodes S es, g (e x) = x := fun x hx =>
    hb.injOn.leftInvOn_invFunOn hx
  have hgx' : ∀ x ∈ combNodes S es', g' (e' x) = x := fun x hx =>
    hb'.injOn.leftInvOn_invFunOn hx
  have hτm : ∀ y ∈ combNodes S es' \ B', τ y ∈ combNodes S es \ B := fun y hy =>
    Function.invFunOn_mem (hσ.surjOn (Finset.mem_coe.2 hy))
  have hστ : ∀ y ∈ combNodes S es' \ B', σ (τ y) = y := fun y hy =>
    hσ.invOn_invFunOn.2 (Finset.mem_coe.2 hy)
  have hτσ : ∀ x ∈ combNodes S es \ B, τ (σ x) = x := fun x hx =>
    hσ.invOn_invFunOn.1 (Finset.mem_coe.2 hx)
  have hσm : ∀ x ∈ combNodes S es \ B, σ x ∈ combNodes S es' \ B' := fun x hx =>
    hσ.mapsTo (Finset.mem_coe.2 hx)
  have hA : ∀ i : Fin R.n, i ∉ Q → g i ∈ combNodes S es \ B := fun i hiQ =>
    Finset.mem_sdiff.2 ⟨(hg i).1, fun hB => hiQ ((hg i).2 ▸ Finset.mem_image_of_mem e hB)⟩
  have hA' : ∀ j : Fin R'.n, j ∉ Q' → g' j ∈ combNodes S es' \ B' := fun j hjQ =>
    Finset.mem_sdiff.2 ⟨(hg' j).1, fun hB => hjQ ((hg' j).2 ▸ Finset.mem_image_of_mem e' hB)⟩
  have hN : ∀ x ∈ combNodes S es \ B, e x ∉ Q := by
    intro x hx hxQ
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.1 hxQ
    have := hb.injOn (Finset.mem_coe.2 (hBs hy))
      (Finset.mem_coe.2 (Finset.mem_sdiff.1 hx).1) hye
    subst this
    exact (Finset.mem_sdiff.1 hx).2 hy
  have hN' : ∀ x ∈ combNodes S es' \ B', e' x ∉ Q' := by
    intro x hx hxQ
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.1 hxQ
    have := hb'.injOn (Finset.mem_coe.2 (hBs' hy))
      (Finset.mem_coe.2 (Finset.mem_sdiff.1 hx).1) hye
    subst this
    exact (Finset.mem_sdiff.1 hx).2 hy
  let φ : {i // i ∉ Q} ≃ {j // j ∉ Q'} :=
    { toFun := fun i => ⟨e' (σ (g i.1)), hN' _ (hσm _ (hA _ i.2))⟩
      invFun := fun j => ⟨e (τ (g' j.1)), hN _ (hτm _ (hA' _ j.2))⟩
      left_inv := fun i => by
        apply Subtype.ext
        simp only
        rw [hgx' _ (Finset.mem_sdiff.1 (hσm _ (hA _ i.2))).1, hτσ _ (hA _ i.2), (hg _).2]
      right_inv := fun j => by
        apply Subtype.ext
        simp only
        rw [hgx _ (Finset.mem_sdiff.1 (hτm _ (hA' _ j.2))).1, hστ _ (hA' _ j.2), (hg' _).2] }
  -- every kept node is the image of a kept comb node
  have hrep : ∀ i : {i // i ∉ Q}, ∃ x ∈ combNodes S es \ B, e x = i.1 ∧
      (φ i).1 = e' (σ x) := fun i =>
    ⟨g i.1, hA _ i.2, (hg _).2, rfl⟩
  have hsub : ∀ x ∈ combNodes S es \ B, x ∈ combNodes S es := fun x hx =>
    (Finset.mem_sdiff.1 hx).1
  have hsub' : ∀ x ∈ combNodes S es' \ B', x ∈ combNodes S es' := fun x hx =>
    (Finset.mem_sdiff.1 hx).1
  have hsink := combSink_mem' h
  have hsink' := combSink_mem' h'
  refine ⟨Q, Q', φ, ⟨⟨e o, e' o', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact pres_block hb he hBs (hBc.trans hk) ho hBo hBcons
  · exact pres_block hb' he' hBs' (hBc'.trans hk) ho' hBo' hBcons'
  · rw [hl' _ (hBs' ho'), hl _ (hBs ho), hol]
  · intro i
    obtain ⟨x, hx, hxi, hφ⟩ := hrep i
    rw [hφ, ← hxi, hl' _ (hsub' _ (hσm _ hx)), hl _ (hsub _ hx), hσl _ hx]
  · intro i j
    obtain ⟨x, hx, hxi, hφ⟩ := hrep i
    obtain ⟨y, hy, hyj, hφ'⟩ := hrep j
    rw [hφ, hφ', ← hxi, ← hyj, he' _ (hsub' _ (hσm _ hx)) _ (hsub' _ (hσm _ hy)),
      he _ (hsub _ hx) _ (hsub _ hy), hσe _ hx _ hy]
  · intro i j hj hedge
    obtain ⟨x, hx, hxi, hφ⟩ := hrep i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hj
    rw [hφ, he' _ (hsub' _ (hσm _ hx)) _ (hBs' hy)] at hedge
    obtain ⟨z, hz, hxz⟩ := hσin x hx y hy hedge
    simp only [ProofDag.inputs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨i.2, e z, Finset.mem_image_of_mem e hz, ?_⟩
    rw [← hxi]
    exact (he _ (hsub _ hx) _ (hBs hz)).2 hxz
  · intro c
    obtain ⟨x, hx, hxc, hφ⟩ := hrep c
    rw [hφ, ← hxc, he' _ (hBs' ho') _ (hsub' _ (hσm _ hx)), he _ (hBs ho) _ (hsub _ hx), hσo _ hx]
  · intro hnot
    have hsB : combSink start es ∉ B := fun hB => hnot (hs ▸ Finset.mem_image_of_mem e hB)
    have hx : combSink start es ∈ combNodes S es \ B := Finset.mem_sdiff.2 ⟨hsink, hsB⟩
    show e' (σ (g R.sink)) = R'.sink
    rw [hs, hgx _ hsink, hsk1 hsB, hs']
  · intro hin
    rw [hs] at hin ⊢
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.1 hin
    have := hb.injOn (Finset.mem_coe.2 (hBs hy)) (Finset.mem_coe.2 hsink) hye
    subst this
    obtain ⟨h1, h2⟩ := hsk2 hy
    exact ⟨by rw [h1], by rw [hs', h2]⟩
  · exact pres_noaxiom hb hi hp hBs hBp
  · exact pres_noaxiom hb' hi' hp' hBs' hBp'
  · intro t ht hnot
    have hsrc : CombNode.src t ∈ combNodes S es := by simp [combNodes, ht]
    show e' (σ (g (pos t))) = pos' t
    rw [hp t ht, hgx _ hsrc, hσs t ht, hp' t ht]

end ReconfRes.Frozen.Dev.Q427d.PartGB
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### G-B: comb moves are frozen steps -/
alias step_of_combMove := ReconfRes.Frozen.Dev.Q427d.PartGB.step_of_combMove

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC1
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### Basic facts on comb nodes -/
theorem src_mem_combNodes (S : Finset ι) (es : List (Event ι V)) (s : ι) :
    CombNode.src s ∈ combNodes S es ↔ s ∈ S := by
  simp [combNodes]

theorem prepLen_eq_zero (es : List (Event ι V)) (i : ℕ) (h : es.length ≤ i) : prepLen es i = 0 := by
  simp [prepLen, List.getElem?_eq_none h]

theorem pr_mem_combNodes (S : Finset ι) (es : List (Event ι V)) (i j : ℕ) :
    CombNode.pr i j ∈ combNodes S es ↔ j < prepLen es i := by
  simp only [combNodes, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_range,
    reduceCtorEq, and_false, exists_false, false_or, or_false, CombNode.pr.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact hb
  · intro h
    refine ⟨i, ?_, j, h, rfl, rfl⟩
    by_contra hc
    rw [prepLen_eq_zero es i (by omega)] at h
    omega

theorem gl_mem_combNodes (S : Finset ι) (es : List (Event ι V)) (i : ℕ) :
    CombNode.gl i ∈ combNodes S es ↔ i < es.length := by
  simp [combNodes]

theorem combParents_pr (start : ι) (es : List (Event ι V)) (i j : ℕ) (e : Event ι V)
    (h : es[i]? = some e) :
    combParents start es (CombNode.pr i j) =
      {if j = 0 then CombNode.src e.side else CombNode.pr i (j - 1)} ∪
        (((e.prep[j]?).map fun u => ({CombNode.src u.1} : Finset (CombNode ι))).getD ∅) := by
  simp only [combParents, h]

theorem combParents_gl (start : ι) (es : List (Event ι V)) (i : ℕ) (e : Event ι V)
    (h : es[i]? = some e) :
    combParents start es (CombNode.gl i) =
      {if i = 0 then CombNode.src start else CombNode.gl (i - 1),
       if e.prep.length = 0 then CombNode.src e.side else CombNode.pr i (e.prep.length - 1)} := by
  simp only [combParents, h]

theorem combParents_pr_none (start : ι) (es : List (Event ι V)) (i j : ℕ)
    (h : es[i]? = none) : combParents start es (CombNode.pr i j) = ∅ := by
  simp only [combParents, h]

theorem combParents_gl_none (start : ι) (es : List (Event ι V)) (i : ℕ)
    (h : es[i]? = none) : combParents start es (CombNode.gl i) = ∅ := by
  simp only [combParents, h]

theorem goalLabel_append (inv : ι → Clause V) (start : ι) (p q : List (Event ι V)) :
    goalLabel inv start (p ++ q) = q.foldl (stepG inv) (goalLabel inv start p) := by
  simp only [goalLabel_eq_foldl, List.foldl_append]

theorem gl_mem_parents {start : ι} {es : List (Event ι V)} {a : ℕ} {c : CombNode ι}
    (h : CombNode.gl a ∈ combParents start es c) : c = CombNode.gl (a + 1) := by
  cases c with
  | src s => simp [combParents] at h
  | pr i j =>
    cases he : es[i]? with
    | none => simp [combParents_pr_none start es i j he] at h
    | some e =>
      rw [combParents_pr start es i j e he] at h
      cases hp : e.prep[j]? <;> simp [hp] at h <;> split_ifs at h
  | gl i =>
    cases he : es[i]? with
    | none => simp [combParents_gl_none start es i he] at h
    | some e =>
      rw [combParents_gl start es i e he] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> split_ifs at h <;> simp_all <;> omega

theorem pr_mem_parents {start : ι} {es : List (Event ι V)} {a b : ℕ} {c : CombNode ι}
    (h : CombNode.pr a b ∈ combParents start es c) :
    c = CombNode.pr a (b + 1) ∨
      (c = CombNode.gl a ∧ ∃ e, es[a]? = some e ∧ e.prep.length = b + 1) := by
  cases c with
  | src s => simp [combParents] at h
  | pr i j =>
    cases he : es[i]? with
    | none => simp [combParents_pr_none start es i j he] at h
    | some e =>
      rw [combParents_pr start es i j e he] at h
      left
      cases hp : e.prep[j]? <;> simp [hp] at h <;> split_ifs at h <;> simp_all <;> omega
  | gl i =>
    cases he : es[i]? with
    | none => simp [combParents_gl_none start es i he] at h
    | some e =>
      rw [combParents_gl start es i e he] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      right
      rcases h with h | h
      · split_ifs at h
      · split_ifs at h with h1
        simp only [CombNode.pr.injEq] at h
        obtain ⟨rfl, hb⟩ := h
        exact ⟨rfl, e, he, by omega⟩

/-! ### (M1): the swap of two adjacent goal events -/
/-- The transposition of `i` and `i + 1`. -/
def fsw (i j : ℕ) : ℕ := if j = i then i + 1 else if j = i + 1 then i else j

theorem fsw_fsw (i j : ℕ) : fsw i (fsw i j) = j := by
  unfold fsw; split_ifs <;> omega

/-- The node map of (M1): exchange the private chains of events `i` and `i + 1`. -/
def swN (i : ℕ) : CombNode ι → CombNode ι
  | .pr j m => .pr (fsw i j) m
  | x => x

theorem swN_swN (i : ℕ) (x : CombNode ι) : swN i (swN i x) = x := by
  cases x <;> simp [swN, fsw_fsw]

theorem swN_injective (i : ℕ) : Function.Injective (swN (ι := ι) i) := by
  intro x y h
  rw [← swN_swN i x, h, swN_swN]

theorem swN_eq_gl (i k : ℕ) (x : CombNode ι) : swN i x = CombNode.gl k ↔ x = CombNode.gl k := by
  cases x <;> simp [swN]

theorem getElem?_swap (pre post : List (Event ι V)) (e₁ e₂ : Event ι V) (j : ℕ) :
    (pre ++ e₂ :: e₁ :: post)[j]? = (pre ++ e₁ :: e₂ :: post)[fsw pre.length j]? := by
  unfold fsw
  rcases lt_or_ge j pre.length with h | h
  · rw [if_neg (by omega), if_neg (by omega), List.getElem?_append_left h,
      List.getElem?_append_left h]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rcases k with _ | _ | k
    · simp [List.getElem?_append_right]
    · simp [List.getElem?_append_right]
    · rw [if_neg (by omega), if_neg (by omega)]
      simp [List.getElem?_append_right]

theorem getElem?_swap' (pre post : List (Event ι V)) (e₁ e₂ : Event ι V) (j : ℕ) :
    (pre ++ e₂ :: e₁ :: post)[fsw pre.length j]? = (pre ++ e₁ :: e₂ :: post)[j]? := by
  rw [getElem?_swap, fsw_fsw]

theorem prepLen_swap (pre post : List (Event ι V)) (e₁ e₂ : Event ι V) (j : ℕ) :
    prepLen (pre ++ e₂ :: e₁ :: post) j = prepLen (pre ++ e₁ :: e₂ :: post) (fsw pre.length j) := by
  unfold prepLen; rw [getElem?_swap]

theorem mem_combNodes_swap (S : Finset ι) (pre post : List (Event ι V)) (e₁ e₂ : Event ι V)
    (x : CombNode ι) :
    swN pre.length x ∈ combNodes S (pre ++ e₂ :: e₁ :: post) ↔
      x ∈ combNodes S (pre ++ e₁ :: e₂ :: post) := by
  cases x with
  | src s => simp only [swN, src_mem_combNodes]
  | pr j m => simp only [swN, pr_mem_combNodes]; rw [prepLen_swap, fsw_fsw]
  | gl j => simp only [swN, gl_mem_combNodes, List.length_append, List.length_cons]

/-- Top of the private chain of event `e` at index `k`. -/
def topN (e : Event ι V) (k : ℕ) : CombNode ι :=
  if e.prep.length = 0 then CombNode.src e.side else CombNode.pr k (e.prep.length - 1)

theorem combParents_gl' (start : ι) (es : List (Event ι V)) (i : ℕ) (e : Event ι V)
    (h : es[i]? = some e) :
    combParents start es (CombNode.gl i) =
      {if i = 0 then CombNode.src start else CombNode.gl (i - 1), topN e i} :=
  combParents_gl start es i e h

theorem swN_prev (i : ℕ) (start : ι) :
    swN i (if i = 0 then CombNode.src start else CombNode.gl (i - 1)) =
      (if i = 0 then CombNode.src start else CombNode.gl (i - 1)) := by
  split_ifs <;> rfl

theorem swN_topN (i : ℕ) (e : Event ι V) : swN i (topN e i) = topN e (i + 1) := by
  unfold topN; split_ifs <;> simp [swN, fsw]

theorem swN_topN' (i : ℕ) (e : Event ι V) : swN i (topN e (i + 1)) = topN e i := by
  rw [← swN_topN, swN_swN]

theorem parents_swap (start : ι) (pre post : List (Event ι V)) (e₁ e₂ : Event ι V)
    (y : CombNode ι) (hy₁ : y ≠ CombNode.gl pre.length) (hy₂ : y ≠ CombNode.gl (pre.length + 1)) :
    combParents start (pre ++ e₂ :: e₁ :: post) (swN pre.length y) =
      (combParents start (pre ++ e₁ :: e₂ :: post) y).image (swN pre.length) := by
  cases y with
  | src s => simp [swN, combParents]
  | pr j m =>
    simp only [swN]
    cases he : (pre ++ e₁ :: e₂ :: post)[j]? with
    | none =>
      rw [combParents_pr_none _ _ _ _ he, combParents_pr_none]
      · simp
      · rw [getElem?_swap', he]
    | some e =>
      rw [combParents_pr _ _ _ _ e he, combParents_pr _ _ _ _ e (by rw [getElem?_swap', he]),
        Finset.image_union, Finset.image_singleton]
      congr 1
      · split_ifs <;> simp [swN]
      · cases e.prep[m]? <;> simp [swN]
  | gl j =>
    have hj : fsw pre.length j = j := by
      unfold fsw; split_ifs <;> simp_all
    have hg : (pre ++ e₂ :: e₁ :: post)[j]? = (pre ++ e₁ :: e₂ :: post)[j]? := by
      rw [getElem?_swap, hj]
    simp only [swN]
    cases he : (pre ++ e₁ :: e₂ :: post)[j]? with
    | none =>
      rw [combParents_gl_none _ _ _ he, combParents_gl_none]
      · simp
      · rw [hg, he]
    | some e =>
      rw [combParents_gl' _ _ _ e he, combParents_gl' _ _ _ e (by rw [hg, he]),
        Finset.image_insert, Finset.image_singleton]
      congr 1
      · split_ifs <;> rfl
      · unfold topN; split_ifs <;> simp [swN, hj]

theorem goal_take_swap (inv : ι → Clause V) (start : ι) (pre post : List (Event ι V))
    (e₁ e₂ : Event ι V)
    (heq : goalLabel inv start (pre ++ [e₁, e₂]) = goalLabel inv start (pre ++ [e₂, e₁]))
    (n : ℕ) (hn : n ≠ pre.length + 1) :
    goalLabel inv start ((pre ++ e₂ :: e₁ :: post).take n) =
      goalLabel inv start ((pre ++ e₁ :: e₂ :: post).take n) := by
  rcases le_or_gt n pre.length with h | h
  · rw [List.take_append_of_le_length h, List.take_append_of_le_length h]
  · obtain ⟨k, rfl⟩ : ∃ k, n = pre.length + (k + 2) := ⟨n - pre.length - 2, by omega⟩
    rw [List.take_length_add_append, List.take_length_add_append]
    simp only [List.take_succ_cons]
    have h1 : ∀ a b : Event ι V, pre ++ a :: b :: post.take k = (pre ++ [a, b]) ++ post.take k := by
      intro a b; simp
    rw [h1 e₂ e₁, h1 e₁ e₂, goalLabel_append inv start (pre ++ [e₂, e₁]),
      goalLabel_append inv start (pre ++ [e₁, e₂]), heq]

theorem label_swap (inv : ι → Clause V) (start : ι) (pre post : List (Event ι V))
    (e₁ e₂ : Event ι V)
    (heq : goalLabel inv start (pre ++ [e₁, e₂]) = goalLabel inv start (pre ++ [e₂, e₁]))
    (x : CombNode ι) (hx : x ≠ CombNode.gl pre.length) :
    combLabel inv start (pre ++ e₂ :: e₁ :: post) (swN pre.length x) =
      combLabel inv start (pre ++ e₁ :: e₂ :: post) x := by
  cases x with
  | src s => rfl
  | pr j m => simp only [swN, combLabel, getElem?_swap']
  | gl j =>
    simp only [swN, combLabel]
    exact goal_take_swap inv start pre post e₁ e₂ heq _ (by intro h; apply hx; congr 1; omega)

theorem swN_mem_pair (i a b : ℕ) (x : CombNode ι) :
    swN i x ∈ ({CombNode.gl a, CombNode.gl b} : Finset (CombNode ι)) ↔
      x ∈ ({CombNode.gl a, CombNode.gl b} : Finset (CombNode ι)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, swN_eq_gl]

theorem take_two (pre post : List (Event ι V)) (a b : Event ι V) :
    (pre ++ a :: b :: post).take (pre.length + 1 + 1) = pre ++ [a, b] := by
  rw [show pre.length + 1 + 1 = pre.length + 2 from rfl, List.take_length_add_append]
  simp

theorem combMove_swap {inv : ι → Clause V} {S : Finset ι} {start : ι}
    (pre post : List (Event ι V)) (e₁ e₂ : Event ι V)
    (hnd : (srcList start (pre ++ e₁ :: e₂ :: post)).Nodup)
    (hS : (srcList start (pre ++ e₁ :: e₂ :: post)).toFinset = S)
    (heq : goalLabel inv start (pre ++ [e₁, e₂]) = goalLabel inv start (pre ++ [e₂, e₁])) :
    ∃ B B' o o' σ, IsCombMove inv S start (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post)
      B B' o o' σ := by
  have h1 : (pre ++ e₁ :: e₂ :: post)[pre.length]? = some e₁ := by simp
  have h2 : (pre ++ e₁ :: e₂ :: post)[pre.length + 1]? = some e₂ := by
    simp [List.getElem?_append_right]
  have h1' : (pre ++ e₂ :: e₁ :: post)[pre.length]? = some e₂ := by simp
  have h2' : (pre ++ e₂ :: e₁ :: post)[pre.length + 1]? = some e₁ := by
    simp [List.getElem?_append_right]
  have hB : ∀ x : CombNode ι, x ∈ ({CombNode.gl pre.length, CombNode.gl (pre.length + 1)} :
      Finset (CombNode ι)) ↔ x = CombNode.gl pre.length ∨ x = CombNode.gl (pre.length + 1) := by
    intro x; simp
  have hinv : ∀ {x y : CombNode ι}, swN pre.length x = y → x = swN pre.length y := by
    rintro x y rfl; rw [swN_swN]
  refine ⟨{CombNode.gl pre.length, CombNode.gl (pre.length + 1)},
    {CombNode.gl pre.length, CombNode.gl (pre.length + 1)}, CombNode.gl (pre.length + 1),
    CombNode.gl (pre.length + 1), swN pre.length,
    ?_, ?_, Finset.card_le_two, Finset.card_le_two, ?_, ?_, by simp, by simp, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x _ => rfl⟩
  · intro x hx
    rcases (hB x).1 hx with rfl | rfl <;> simp [gl_mem_combNodes]
  · intro x hx
    rcases (hB x).1 hx with rfl | rfl <;> simp [gl_mem_combNodes]
  · intro x hx
    rcases (hB x).1 hx with rfl | rfl
    · rw [combParents_gl' _ _ _ e₁ h1]; exact Finset.insert_nonempty _ _
    · rw [combParents_gl' _ _ _ e₂ h2]; exact Finset.insert_nonempty _ _
  · intro x hx
    rcases (hB x).1 hx with rfl | rfl
    · rw [combParents_gl' _ _ _ e₂ h1']; exact Finset.insert_nonempty _ _
    · rw [combParents_gl' _ _ _ e₁ h2']; exact Finset.insert_nonempty _ _
  · intro x hx
    rcases (hB x).1 hx with rfl | rfl
    · right; rw [combParents_gl' _ _ _ e₂ h2]; simp
    · left; rfl
  · intro x hx
    rcases (hB x).1 hx with rfl | rfl
    · right; rw [combParents_gl' _ _ _ e₁ h2']; simp
    · left; rfl
  · intro x hx hne c _ hc
    rcases (hB x).1 hx with rfl | rfl
    · rw [gl_mem_parents hc]; simp
    · exact absurd rfl hne
  · intro x hx hne c _ hc
    rcases (hB x).1 hx with rfl | rfl
    · rw [gl_mem_parents hc]; simp
    · exact absurd rfl hne
  · refine Set.InvOn.bijOn ⟨fun x _ => swN_swN _ x, fun x _ => swN_swN _ x⟩ ?_ ?_
    · intro x hx
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hx ⊢
      exact ⟨(mem_combNodes_swap S pre post e₁ e₂ x).2 hx.1, by rw [swN_mem_pair]; exact hx.2⟩
    · intro x hx
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hx ⊢
      refine ⟨(mem_combNodes_swap S pre post e₁ e₂ _).1 (by rw [swN_swN]; exact hx.1), ?_⟩
      rw [swN_mem_pair]; exact hx.2
  · intro x hx
    rw [Finset.mem_sdiff, hB] at hx
    exact label_swap inv start pre post e₁ e₂ heq x (fun h => hx.2 (Or.inl h))
  · simp only [combLabel, swN]
    rw [take_two, take_two]; exact heq.symm
  · intro x hx y hy
    rw [Finset.mem_sdiff, hB] at hy
    rw [parents_swap start pre post e₁ e₂ y (fun h => hy.2 (Or.inl h)) (fun h => hy.2 (Or.inr h))]
    exact (swN_injective _).mem_finset_image
  · intro x hx y hy h
    rw [Finset.mem_sdiff, hB] at hx
    rcases (hB y).1 hy with rfl | rfl
    · rw [combParents_gl' _ _ _ e₂ h1'] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · refine ⟨CombNode.gl pre.length, by simp, ?_⟩
        rw [hinv h, swN_prev, combParents_gl' _ _ _ e₁ h1]; simp
      · refine ⟨CombNode.gl (pre.length + 1), by simp, ?_⟩
        rw [hinv h, swN_topN, combParents_gl' _ _ _ e₂ h2]; simp
    · rw [combParents_gl' _ _ _ e₁ h2'] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel] at h
        exact absurd (Or.inl ((swN_eq_gl _ _ _).1 h)) hx.2
      · refine ⟨CombNode.gl pre.length, by simp, ?_⟩
        rw [hinv h, swN_topN', combParents_gl' _ _ _ e₁ h1]; simp
  · intro c hc
    rw [Finset.mem_sdiff, hB] at hc
    rw [parents_swap start pre post e₁ e₂ c (fun h => hc.2 (Or.inl h)) (fun h => hc.2 (Or.inr h))]
    exact (swN_injective (ι := ι) pre.length).mem_finset_image (a := CombNode.gl (pre.length + 1))
  · intro _
    simp [combSink, swN]
  · intro h
    simp only [combSink, List.length_append, List.length_cons] at h ⊢
    rw [if_neg (by omega)] at h ⊢
    rw [hB] at h
    simp only [CombNode.gl.injEq] at h
    constructor <;> congr 1 <;> omega

end ReconfRes.Frozen.Dev.Q427d.PartGC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### G-C: the four two-inference comb moves -/
alias combMove_swap := ReconfRes.Frozen.Dev.Q427d.PartGC1.combMove_swap

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC1
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### (M2): the swap of two adjacent private deletions -/
theorem getElem?_mid (pre post : List (Event ι V)) (a b : Event ι V) (j : ℕ) (hj : j ≠ pre.length) :
    (pre ++ b :: post)[j]? = (pre ++ a :: post)[j]? := by
  rcases lt_or_gt_of_ne hj with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · obtain ⟨k, rfl⟩ : ∃ k, j = pre.length + (k + 1) := ⟨j - pre.length - 1, by omega⟩
    simp [List.getElem?_append_right]

theorem getElem?_prep_swap (l t : List (ι × V)) (u₁ u₂ : ι × V) (m : ℕ) (h₁ : m ≠ l.length)
    (h₂ : m ≠ l.length + 1) :
    (l ++ u₂ :: u₁ :: t)[m]? = (l ++ u₁ :: u₂ :: t)[m]? := by
  rcases lt_or_ge m l.length with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · obtain ⟨k, rfl⟩ : ∃ k, m = l.length + (k + 2) := ⟨m - l.length - 2, by omega⟩
    simp [List.getElem?_append_right]

theorem sideLabel_prep_swap (inv : ι → Clause V) (s : ι) (l t : List (ι × V)) (u₁ u₂ : ι × V)
    (x : V) (n : ℕ) (hn : n ≠ l.length + 1) :
    sideLabel inv ⟨s, l ++ u₂ :: u₁ :: t, x⟩ n = sideLabel inv ⟨s, l ++ u₁ :: u₂ :: t, x⟩ n := by
  unfold sideLabel
  simp only
  rcases le_or_gt n l.length with h | h
  · rw [List.take_append_of_le_length h, List.take_append_of_le_length h]
  · obtain ⟨k, rfl⟩ : ∃ k, n = l.length + (k + 2) := ⟨n - l.length - 2, by omega⟩
    rw [List.take_length_add_append, List.take_length_add_append]
    simp only [List.take_succ_cons, List.foldl_append, List.foldl_cons]
    rw [Finset.erase_right_comm]

theorem sideLabel_full_swap (inv : ι → Clause V) (s : ι) (l t : List (ι × V)) (u₁ u₂ : ι × V)
    (x : V) :
    sideLabel inv ⟨s, l ++ u₂ :: u₁ :: t, x⟩ (l ++ u₂ :: u₁ :: t).length =
      sideLabel inv ⟨s, l ++ u₁ :: u₂ :: t, x⟩ (l ++ u₁ :: u₂ :: t).length := by
  have : (l ++ u₂ :: u₁ :: t).length = (l ++ u₁ :: u₂ :: t).length := by simp
  rw [this]
  exact sideLabel_prep_swap inv s l t u₁ u₂ x _ (by simp)

theorem stepG_prep_swap (inv : ι → Clause V) (g : Clause V) (s : ι) (l t : List (ι × V))
    (u₁ u₂ : ι × V) (x : V) :
    stepG inv g ⟨s, l ++ u₂ :: u₁ :: t, x⟩ = stepG inv g ⟨s, l ++ u₁ :: u₂ :: t, x⟩ := by
  unfold stepG
  simp only
  rw [sideLabel_full_swap]

theorem goal_take_prep_swap (inv : ι → Clause V) (start : ι) (pre post : List (Event ι V))
    (s : ι) (l t : List (ι × V)) (u₁ u₂ : ι × V) (x : V) (n : ℕ) :
    goalLabel inv start ((pre ++ ⟨s, l ++ u₂ :: u₁ :: t, x⟩ :: post).take n) =
      goalLabel inv start ((pre ++ ⟨s, l ++ u₁ :: u₂ :: t, x⟩ :: post).take n) := by
  rcases le_or_gt n pre.length with h | h
  · rw [List.take_append_of_le_length h, List.take_append_of_le_length h]
  · obtain ⟨k, rfl⟩ : ∃ k, n = pre.length + (k + 1) := ⟨n - pre.length - 1, by omega⟩
    rw [List.take_length_add_append, List.take_length_add_append]
    simp only [List.take_succ_cons]
    have h1 : ∀ a : Event ι V, pre ++ a :: post.take k = (pre ++ [a]) ++ post.take k := by
      intro a; simp
    rw [h1, h1, goalLabel_append inv start (pre ++ [_]), goalLabel_append inv start (pre ++ [_]),
      goalLabel_snoc, goalLabel_snoc, stepG_prep_swap]

end ReconfRes.Frozen.Dev.Q427d.PartGC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC1
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
variable (pre post : List (Event ι V)) (s : ι) (l t : List (ι × V)) (u₁ u₂ : ι × V) (x : V)
theorem prepLen_prep_swap (j : ℕ) :
    prepLen (pre ++ ⟨s, l ++ u₂ :: u₁ :: t, x⟩ :: post) j =
      prepLen (pre ++ ⟨s, l ++ u₁ :: u₂ :: t, x⟩ :: post) j := by
  unfold prepLen
  by_cases hj : j = pre.length
  · subst hj; simp
  · rw [getElem?_mid pre post _ _ j hj]

theorem combNodes_prep_swap (S : Finset ι) :
    combNodes S (pre ++ ⟨s, l ++ u₂ :: u₁ :: t, x⟩ :: post) =
      combNodes S (pre ++ ⟨s, l ++ u₁ :: u₂ :: t, x⟩ :: post) := by
  ext y
  cases y with
  | src a => simp only [src_mem_combNodes]
  | pr j m => simp only [pr_mem_combNodes, prepLen_prep_swap]
  | gl j => simp only [gl_mem_combNodes, List.length_append, List.length_cons]

theorem parents_prep_swap (start : ι) (y : CombNode ι)
    (hy₁ : y ≠ CombNode.pr pre.length l.length) (hy₂ : y ≠ CombNode.pr pre.length (l.length + 1)) :
    combParents start (pre ++ ⟨s, l ++ u₂ :: u₁ :: t, x⟩ :: post) y =
      combParents start (pre ++ ⟨s, l ++ u₁ :: u₂ :: t, x⟩ :: post) y := by
  cases y with
  | src a => rfl
  | pr j m =>
    by_cases hj : j = pre.length
    · subst hj
      rw [combParents_pr _ _ _ _ (⟨s, l ++ u₂ :: u₁ :: t, x⟩ : Event ι V) (by simp), combParents_pr _ _ _ _ (⟨s, l ++ u₁ :: u₂ :: t, x⟩ : Event ι V) (by simp)]
      simp only
      rw [getElem?_prep_swap l t u₁ u₂ m (fun h => hy₁ (by rw [h]))
        (fun h => hy₂ (by rw [h]))]
    · simp only [combParents]; rw [getElem?_mid pre post (⟨s, l ++ u₁ :: u₂ :: t, x⟩ : Event ι V) (⟨s, l ++ u₂ :: u₁ :: t, x⟩ : Event ι V) j hj]
  | gl j =>
    by_cases hj : j = pre.length
    · subst hj
      rw [combParents_gl' _ _ _ (⟨s, l ++ u₂ :: u₁ :: t, x⟩ : Event ι V) (by simp), combParents_gl' _ _ _ (⟨s, l ++ u₁ :: u₂ :: t, x⟩ : Event ι V) (by simp)]
      simp [topN]
    · simp only [combParents]; rw [getElem?_mid pre post (⟨s, l ++ u₁ :: u₂ :: t, x⟩ : Event ι V) (⟨s, l ++ u₂ :: u₁ :: t, x⟩ : Event ι V) j hj]

theorem label_prep_swap (inv : ι → Clause V) (start : ι) (y : CombNode ι)
    (hy : y ≠ CombNode.pr pre.length l.length) :
    combLabel inv start (pre ++ ⟨s, l ++ u₂ :: u₁ :: t, x⟩ :: post) y =
      combLabel inv start (pre ++ ⟨s, l ++ u₁ :: u₂ :: t, x⟩ :: post) y := by
  cases y with
  | src a => rfl
  | pr j m =>
    by_cases hj : j = pre.length
    · subst hj
      simp only [combLabel, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      exact sideLabel_prep_swap inv s l t u₁ u₂ x _ (fun h => hy (by congr 1; omega))
    · simp only [combLabel]; rw [getElem?_mid pre post (⟨s, l ++ u₁ :: u₂ :: t, x⟩ : Event ι V) (⟨s, l ++ u₂ :: u₁ :: t, x⟩ : Event ι V) j hj]
  | gl j => exact goal_take_prep_swap inv start pre post s l t u₁ u₂ x _

end ReconfRes.Frozen.Dev.Q427d.PartGC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC1
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
theorem combMove_prepSwap {inv : ι → Clause V} {S : Finset ι} {start : ι}
    (pre post : List (Event ι V)) (s : ι) (l t : List (ι × V)) (u₁ u₂ : ι × V) (x : V)
    (hnd : (srcList start (pre ++ ⟨s, l ++ u₁ :: u₂ :: t, x⟩ :: post)).Nodup)
    (hS : (srcList start (pre ++ ⟨s, l ++ u₁ :: u₂ :: t, x⟩ :: post)).toFinset = S) :
    ∃ B B' o o' σ, IsCombMove inv S start (pre ++ ⟨s, l ++ u₁ :: u₂ :: t, x⟩ :: post)
      (pre ++ ⟨s, l ++ u₂ :: u₁ :: t, x⟩ :: post) B B' o o' σ := by
  have hE : (pre ++ (⟨s, l ++ u₁ :: u₂ :: t, x⟩ : Event ι V) :: post)[pre.length]? =
      some ⟨s, l ++ u₁ :: u₂ :: t, x⟩ := by simp
  have hE' : (pre ++ (⟨s, l ++ u₂ :: u₁ :: t, x⟩ : Event ι V) :: post)[pre.length]? =
      some ⟨s, l ++ u₂ :: u₁ :: t, x⟩ := by simp
  have hB : ∀ y : CombNode ι, y ∈ ({CombNode.pr pre.length l.length,
      CombNode.pr pre.length (l.length + 1)} : Finset (CombNode ι)) ↔
      y = CombNode.pr pre.length l.length ∨ y = CombNode.pr pre.length (l.length + 1) := by
    intro y; simp
  have hsub : ∀ (a b : ι × V), ({CombNode.pr pre.length l.length,
      CombNode.pr pre.length (l.length + 1)} : Finset (CombNode ι)) ⊆
      combNodes S (pre ++ ⟨s, l ++ a :: b :: t, x⟩ :: post) := by
    intro a b y hy
    rcases (hB y).1 hy with rfl | rfl <;>
      simp [pr_mem_combNodes, prepLen]
  have hne : ∀ (a b : ι × V) (y : CombNode ι), y ∈ ({CombNode.pr pre.length l.length,
      CombNode.pr pre.length (l.length + 1)} : Finset (CombNode ι)) →
      (combParents start (pre ++ ⟨s, l ++ a :: b :: t, x⟩ :: post) y).Nonempty := by
    intro a b y hy
    rcases (hB y).1 hy with rfl | rfl <;>
    · rw [combParents_pr _ _ _ _ (⟨s, l ++ a :: b :: t, x⟩ : Event ι V) (by simp)]
      exact ⟨_, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
  have hpar : ∀ (a b : ι × V), CombNode.pr pre.length l.length ∈
      combParents start (pre ++ ⟨s, l ++ a :: b :: t, x⟩ :: post)
        (CombNode.pr pre.length (l.length + 1)) := by
    intro a b
    rw [combParents_pr _ _ _ _ (⟨s, l ++ a :: b :: t, x⟩ : Event ι V) (by simp)]
    simp
  have hcons : ∀ (a b : ι × V) (c : CombNode ι), CombNode.pr pre.length l.length ∈
      combParents start (pre ++ ⟨s, l ++ a :: b :: t, x⟩ :: post) c →
      c ∈ ({CombNode.pr pre.length l.length,
        CombNode.pr pre.length (l.length + 1)} : Finset (CombNode ι)) := by
    intro a b c hc
    rcases pr_mem_parents hc with rfl | ⟨rfl, e, he, hl⟩
    · simp
    · simp at he
      subst he
      simp at hl
  refine ⟨{CombNode.pr pre.length l.length, CombNode.pr pre.length (l.length + 1)},
    {CombNode.pr pre.length l.length, CombNode.pr pre.length (l.length + 1)},
    CombNode.pr pre.length (l.length + 1), CombNode.pr pre.length (l.length + 1), id,
    hsub u₁ u₂, hsub u₂ u₁, Finset.card_le_two, Finset.card_le_two, hne u₁ u₂, hne u₂ u₁,
    by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
  · intro y hy
    rcases (hB y).1 hy with rfl | rfl
    · exact Or.inr (hpar u₁ u₂)
    · exact Or.inl rfl
  · intro y hy
    rcases (hB y).1 hy with rfl | rfl
    · exact Or.inr (hpar u₂ u₁)
    · exact Or.inl rfl
  · intro y hy _ c _ hc
    rcases (hB y).1 hy with rfl | rfl
    · exact hcons u₁ u₂ c hc
    · contradiction
  · intro y hy _ c _ hc
    rcases (hB y).1 hy with rfl | rfl
    · exact hcons u₂ u₁ c hc
    · contradiction
  · rw [combNodes_prep_swap]; exact Set.bijOn_id _
  · intro y hy
    rw [Finset.mem_sdiff, hB] at hy
    exact label_prep_swap pre post s l t u₁ u₂ x inv start y (fun h => hy.2 (Or.inl h))
  · exact label_prep_swap pre post s l t u₁ u₂ x inv start _ (by simp)
  · intro a _ y hy
    rw [Finset.mem_sdiff, hB] at hy
    rw [id, id, parents_prep_swap pre post s l t u₁ u₂ x start y (fun h => hy.2 (Or.inl h))
      (fun h => hy.2 (Or.inr h))]
  · intro a ha y hy h
    rw [Finset.mem_sdiff, hB] at ha
    rw [id] at h
    rcases (hB y).1 hy with rfl | rfl
    · rw [combParents_pr _ _ _ _ _ hE'] at h
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · refine ⟨CombNode.pr pre.length l.length, by simp, ?_⟩
        rw [combParents_pr _ _ _ _ _ hE]
        exact Finset.mem_union_left _ (by simpa using h)
      · refine ⟨CombNode.pr pre.length (l.length + 1), by simp, ?_⟩
        rw [combParents_pr _ _ _ _ _ hE]
        simp at h ⊢
        exact Or.inr h
    · rw [combParents_pr _ _ _ _ _ hE'] at h
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · simp at h
        exact absurd (Or.inl h) ha.2
      · refine ⟨CombNode.pr pre.length l.length, by simp, ?_⟩
        rw [combParents_pr _ _ _ _ _ hE]
        simp at h ⊢
        exact Or.inr h
  · intro c hc
    rw [Finset.mem_sdiff, hB] at hc
    rw [id, parents_prep_swap pre post s l t u₁ u₂ x start c (fun h => hc.2 (Or.inl h))
      (fun h => hc.2 (Or.inr h))]
  · intro _
    simp [combSink]
  · intro h
    exfalso
    unfold combSink at h
    split_ifs at h <;> simp at h

end ReconfRes.Frozen.Dev.Q427d.PartGC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
alias combMove_prepSwap := ReconfRes.Frozen.Dev.Q427d.PartGC1.combMove_prepSwap

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC2
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### Basic facts on comb nodes -/
theorem src_mem_combNodes (S : Finset ι) (es : List (Event ι V)) (s : ι) :
    CombNode.src s ∈ combNodes S es ↔ s ∈ S := by
  simp [combNodes]

theorem prepLen_eq_zero (es : List (Event ι V)) (i : ℕ) (h : es.length ≤ i) : prepLen es i = 0 := by
  simp [prepLen, List.getElem?_eq_none h]

theorem pr_mem_combNodes (S : Finset ι) (es : List (Event ι V)) (i j : ℕ) :
    CombNode.pr i j ∈ combNodes S es ↔ j < prepLen es i := by
  simp only [combNodes, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_range,
    reduceCtorEq, and_false, exists_false, false_or, or_false, CombNode.pr.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact hb
  · intro h
    refine ⟨i, ?_, j, h, rfl, rfl⟩
    by_contra hc
    rw [prepLen_eq_zero es i (by omega)] at h
    omega

theorem gl_mem_combNodes (S : Finset ι) (es : List (Event ι V)) (i : ℕ) :
    CombNode.gl i ∈ combNodes S es ↔ i < es.length := by
  simp [combNodes]

theorem combParents_pr (start : ι) (es : List (Event ι V)) (i j : ℕ) (e : Event ι V)
    (h : es[i]? = some e) :
    combParents start es (CombNode.pr i j) =
      {if j = 0 then CombNode.src e.side else CombNode.pr i (j - 1)} ∪
        (((e.prep[j]?).map fun u => ({CombNode.src u.1} : Finset (CombNode ι))).getD ∅) := by
  simp only [combParents, h]

theorem combParents_gl (start : ι) (es : List (Event ι V)) (i : ℕ) (e : Event ι V)
    (h : es[i]? = some e) :
    combParents start es (CombNode.gl i) =
      {if i = 0 then CombNode.src start else CombNode.gl (i - 1),
       if e.prep.length = 0 then CombNode.src e.side else CombNode.pr i (e.prep.length - 1)} := by
  simp only [combParents, h]

theorem combParents_pr_none (start : ι) (es : List (Event ι V)) (i j : ℕ)
    (h : es[i]? = none) : combParents start es (CombNode.pr i j) = ∅ := by
  simp only [combParents, h]

theorem combParents_gl_none (start : ι) (es : List (Event ι V)) (i : ℕ)
    (h : es[i]? = none) : combParents start es (CombNode.gl i) = ∅ := by
  simp only [combParents, h]

theorem goalLabel_append (inv : ι → Clause V) (start : ι) (p q : List (Event ι V)) :
    goalLabel inv start (p ++ q) = q.foldl (stepG inv) (goalLabel inv start p) := by
  simp only [goalLabel_eq_foldl, List.foldl_append]

theorem gl_mem_parents {start : ι} {es : List (Event ι V)} {a : ℕ} {c : CombNode ι}
    (h : CombNode.gl a ∈ combParents start es c) : c = CombNode.gl (a + 1) := by
  cases c with
  | src s => simp [combParents] at h
  | pr i j =>
    cases he : es[i]? with
    | none => simp [combParents_pr_none start es i j he] at h
    | some e =>
      rw [combParents_pr start es i j e he] at h
      cases hp : e.prep[j]? <;> simp [hp] at h <;> split_ifs at h
  | gl i =>
    cases he : es[i]? with
    | none => simp [combParents_gl_none start es i he] at h
    | some e =>
      rw [combParents_gl start es i e he] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> split_ifs at h <;> simp_all <;> omega

theorem pr_mem_parents {start : ι} {es : List (Event ι V)} {a b : ℕ} {c : CombNode ι}
    (h : CombNode.pr a b ∈ combParents start es c) :
    c = CombNode.pr a (b + 1) ∨
      (c = CombNode.gl a ∧ ∃ e, es[a]? = some e ∧ e.prep.length = b + 1) := by
  cases c with
  | src s => simp [combParents] at h
  | pr i j =>
    cases he : es[i]? with
    | none => simp [combParents_pr_none start es i j he] at h
    | some e =>
      rw [combParents_pr start es i j e he] at h
      left
      cases hp : e.prep[j]? <;> simp [hp] at h <;> split_ifs at h <;> simp_all <;> omega
  | gl i =>
    cases he : es[i]? with
    | none => simp [combParents_gl_none start es i he] at h
    | some e =>
      rw [combParents_gl start es i e he] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      right
      rcases h with h | h
      · split_ifs at h
      · split_ifs at h with h1
        simp only [CombNode.pr.injEq] at h
        obtain ⟨rfl, hb⟩ := h
        exact ⟨rfl, e, he, by omega⟩

/-- Top of the private chain of event `e` at index `k`. -/
def topN (e : Event ι V) (k : ℕ) : CombNode ι :=
  if e.prep.length = 0 then CombNode.src e.side else CombNode.pr k (e.prep.length - 1)

theorem combParents_gl' (start : ι) (es : List (Event ι V)) (i : ℕ) (e : Event ι V)
    (h : es[i]? = some e) :
    combParents start es (CombNode.gl i) =
      {if i = 0 then CombNode.src start else CombNode.gl (i - 1), topN e i} :=
  combParents_gl start es i e h

/-! ### The shift map of (M3) and (M3') -/
/-- Indices after `i` move down by one. -/
def dn (i j : ℕ) : ℕ := if i < j then j - 1 else j

theorem dn_of_lt {i j : ℕ} (h : j < i) : dn i j = j := by
  unfold dn; rw [if_neg (by omega)]

theorem dn_of_gt {i j : ℕ} (h : i < j) : dn i j = j - 1 := by
  unfold dn; rw [if_pos h]

theorem dn_eq_iff {i j : ℕ} : dn i j = i ↔ j = i ∨ j = i + 1 := by
  unfold dn; split_ifs <;> omega

/-- The node map of (M3)/(M3'). -/
def dnN (i : ℕ) : CombNode ι → CombNode ι
  | .src s => .src s
  | .pr j k => .pr (dn i j) k
  | .gl j => .gl (dn i j)

theorem dnN_eq_src {i : ℕ} {x : CombNode ι} {s : ι} :
    dnN i x = CombNode.src s ↔ x = CombNode.src s := by
  cases x <;> simp [dnN]

theorem dnN_eq_pr {i j k : ℕ} {x : CombNode ι} :
    dnN i x = CombNode.pr j k ↔ ∃ j', x = CombNode.pr j' k ∧ dn i j' = j := by
  cases x <;> simp [dnN, and_comm]

theorem dnN_eq_gl {i j : ℕ} {x : CombNode ι} :
    dnN i x = CombNode.gl j ↔ ∃ j', x = CombNode.gl j' ∧ dn i j' = j := by
  cases x <;> simp [dnN]

/-- Nodes on which `dnN i` is injective (`p` is the index of the event without private chain). -/
def Good (i p : ℕ) (x : CombNode ι) : Prop := x ≠ CombNode.gl i ∧ ∀ k, x ≠ CombNode.pr p k

theorem dnN_inj {i p : ℕ} (hp : p = i ∨ p = i + 1) {x y : CombNode ι} (hx : Good i p x)
    (hy : Good i p y) (h : dnN i x = dnN i y) : x = y := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  cases x with
  | src s => exact (dnN_eq_src.1 h.symm).symm
  | pr j k =>
    obtain ⟨j', rfl, hj'⟩ := dnN_eq_pr.1 h.symm
    have h1 : j ≠ p := fun h => hx2 k (by rw [h])
    have h2 : j' ≠ p := fun h => hy2 k (by rw [h])
    have : j' = j := by unfold dn at hj'; split_ifs at hj' <;> omega
    rw [this]
  | gl j =>
    obtain ⟨j', rfl, hj'⟩ := dnN_eq_gl.1 h.symm
    have h1 : j ≠ i := fun h => hx1 (by rw [h])
    have h2 : j' ≠ i := fun h => hy1 (by rw [h])
    have : j' = j := by unfold dn at hj'; split_ifs at hj' <;> omega
    rw [this]

end ReconfRes.Frozen.Dev.Q427d.PartGC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC2
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
variable (pre post : List (Event ι V)) (a b c : Event ι V)
theorem getElem?_dn (j : ℕ) (h1 : j ≠ pre.length) (h2 : j ≠ pre.length + 1) :
    (pre ++ c :: post)[dn pre.length j]? = (pre ++ a :: b :: post)[j]? := by
  rcases lt_or_gt_of_ne h1 with h | h
  · rw [dn_of_lt h, List.getElem?_append_left h, List.getElem?_append_left h]
  · obtain ⟨k, rfl⟩ : ∃ k, j = pre.length + (k + 2) := ⟨j - pre.length - 2, by omega⟩
    rw [dn_of_gt h, show pre.length + (k + 2) - 1 = pre.length + (k + 1) by omega]
    simp [List.getElem?_append_right]

theorem prepLen_dn (j : ℕ) (h1 : j ≠ pre.length) (h2 : j ≠ pre.length + 1) :
    prepLen (pre ++ c :: post) (dn pre.length j) = prepLen (pre ++ a :: b :: post) j := by
  unfold prepLen; rw [getElem?_dn pre post a b c j h1 h2]

theorem goal_take_dn (inv : ι → Clause V) (start : ι)
    (heq : goalLabel inv start (pre ++ [a, b]) = goalLabel inv start (pre ++ [c]))
    (j : ℕ) (hj : j ≠ pre.length) :
    goalLabel inv start ((pre ++ c :: post).take (dn pre.length j + 1)) =
      goalLabel inv start ((pre ++ a :: b :: post).take (j + 1)) := by
  rcases lt_or_gt_of_ne hj with h | h
  · rw [dn_of_lt h, List.take_append_of_le_length (by omega),
      List.take_append_of_le_length (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k, j = pre.length + (k + 1) := ⟨j - pre.length - 1, by omega⟩
    rw [dn_of_gt h, show pre.length + (k + 1) - 1 + 1 = pre.length + (k + 1) by omega,
      show pre.length + (k + 1) + 1 = pre.length + (k + 2) by omega,
      List.take_length_add_append, List.take_length_add_append]
    simp only [List.take_succ_cons]
    have h1 : pre ++ a :: b :: post.take k = (pre ++ [a, b]) ++ post.take k := by simp
    have h2 : pre ++ c :: post.take k = (pre ++ [c]) ++ post.take k := by simp
    rw [h1, h2, goalLabel_append inv start (pre ++ [a, b]), goalLabel_append inv start (pre ++ [c]), heq]

theorem parents_dn (start : ι) (y : CombNode ι)
    (hy : ∀ j, (y = CombNode.gl j ∨ ∃ k, y = CombNode.pr j k) →
      j ≠ pre.length ∧ j ≠ pre.length + 1) :
    combParents start (pre ++ c :: post) (dnN pre.length y) =
      (combParents start (pre ++ a :: b :: post) y).image (dnN pre.length) := by
  cases y with
  | src s => simp [dnN, combParents]
  | pr j m =>
    obtain ⟨h1, h2⟩ := hy j (Or.inr ⟨m, rfl⟩)
    have hg := getElem?_dn pre post a b c j h1 h2
    simp only [dnN]
    cases he : (pre ++ a :: b :: post)[j]? with
    | none =>
      rw [combParents_pr_none _ _ _ _ he, combParents_pr_none _ _ _ _ (by rw [hg, he])]
      simp
    | some e =>
      rw [combParents_pr _ _ _ _ e he, combParents_pr _ _ _ _ e (by rw [hg, he]),
        Finset.image_union, Finset.image_singleton]
      congr 1
      · split_ifs <;> simp [dnN]
      · cases e.prep[m]? <;> simp [dnN]
  | gl j =>
    obtain ⟨h1, h2⟩ := hy j (Or.inl rfl)
    have hg := getElem?_dn pre post a b c j h1 h2
    simp only [dnN]
    cases he : (pre ++ a :: b :: post)[j]? with
    | none =>
      rw [combParents_gl_none _ _ _ he, combParents_gl_none _ _ _ (by rw [hg, he])]
      simp
    | some e =>
      rw [combParents_gl' _ _ _ e he, combParents_gl' _ _ _ e (by rw [hg, he]),
        Finset.image_insert, Finset.image_singleton]
      congr 1
      · rcases lt_or_gt_of_ne h1 with h | h
        · rw [dn_of_lt h]
          split_ifs <;> simp [dnN, dn_of_lt (show j - 1 < pre.length by omega)]
        · rw [dn_of_gt h, if_neg (by omega), if_neg (by omega)]
          simp [dnN, dn_of_gt (show pre.length < j - 1 by omega)]
      · unfold topN; split_ifs <;> simp [dnN]

theorem sideLabel_snoc_le (inv : ι → Clause V) (s : ι) (l : List (ι × V)) (u : ι × V) (v : V)
    (k : ℕ) (hk : k ≤ l.length) :
    sideLabel inv ⟨s, l ++ [u], v⟩ k = sideLabel inv ⟨s, l, v⟩ k := by
  unfold sideLabel
  simp only
  rw [List.take_append_of_le_length hk]

end ReconfRes.Frozen.Dev.Q427d.PartGC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC2
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
variable {inv : ι → Clause V} {S : Finset ι} {start : ι}
  (pre post : List (Event ι V)) (a b : Event ι V) (u : ι × V) (s : ι) (l : List (ι × V)) (v : V)
  (p q : ℕ)
/-! ### The generic absorbing move -/
/-- Parents of the private node `k < |l|` of the absorbing event. -/
theorem parents_dn_q (hdq : dn pre.length q = pre.length)
    (hE : (pre ++ a :: b :: post)[q]? = some ⟨s, l, v⟩) (k : ℕ) (hk : k < l.length) :
    combParents start (pre ++ ⟨s, l ++ [u], v⟩ :: post) (dnN pre.length (CombNode.pr q k)) =
      (combParents start (pre ++ a :: b :: post) (CombNode.pr q k)).image (dnN pre.length) := by
  simp only [dnN, hdq]
  rw [combParents_pr _ _ _ _ _ hE, combParents_pr _ _ _ _ (⟨s, l ++ [u], v⟩ : Event ι V) (by simp),
    Finset.image_union, Finset.image_singleton]
  simp only [List.getElem?_append_left hk]
  congr 1
  · split_ifs <;> simp [dnN, hdq]
  · cases l[k]? <;> simp [dnN]

/-- Classification of the old nodes outside the block. -/
theorem old_cases (hpq : (p = pre.length ∧ q = pre.length + 1) ∨
      (p = pre.length + 1 ∧ q = pre.length))
    (hpLen : prepLen (pre ++ a :: b :: post) p = 0)
    (hqLen : prepLen (pre ++ a :: b :: post) q = l.length)
    (y : CombNode ι) (hy : y ∈ combNodes S (pre ++ a :: b :: post))
    (hB1 : y ≠ CombNode.gl pre.length) (hB2 : y ≠ CombNode.gl (pre.length + 1)) :
    (∃ x, y = CombNode.src x ∧ x ∈ S) ∨ (∃ k, y = CombNode.pr q k ∧ k < l.length) ∨
      (∃ j k, y = CombNode.pr j k ∧ j ≠ pre.length ∧ j ≠ pre.length + 1 ∧
        k < prepLen (pre ++ a :: b :: post) j) ∨
      (∃ j, y = CombNode.gl j ∧ j ≠ pre.length ∧ j ≠ pre.length + 1 ∧
        j < pre.length + 2 + post.length) := by
  cases y with
  | src x => exact Or.inl ⟨x, rfl, (src_mem_combNodes _ _ _).1 hy⟩
  | pr j k =>
    rw [pr_mem_combNodes] at hy
    by_cases hj : j = pre.length ∨ j = pre.length + 1
    · have : j = q := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hj with rfl | rfl <;> simp_all
      subst this
      exact Or.inr (Or.inl ⟨k, rfl, by omega⟩)
    · simp only [not_or] at hj
      exact Or.inr (Or.inr (Or.inl ⟨j, k, rfl, hj.1, hj.2, hy⟩))
  | gl j =>
    rw [gl_mem_combNodes] at hy
    simp only [List.length_append, List.length_cons] at hy
    refine Or.inr (Or.inr (Or.inr ⟨j, rfl, fun h => hB1 (by rw [h]), fun h => hB2 (by rw [h]),
      by omega⟩))

theorem absorb_move
    (hpq : (p = pre.length ∧ q = pre.length + 1) ∨ (p = pre.length + 1 ∧ q = pre.length))
    (hU : (pre ++ a :: b :: post)[p]? = some ⟨u.1, [], u.2⟩)
    (hE : (pre ++ a :: b :: post)[q]? = some ⟨s, l, v⟩)
    (heq : goalLabel inv start (pre ++ [a, b]) = goalLabel inv start (pre ++ [⟨s, l ++ [u], v⟩])) :
    ∃ B B' o o' σ, IsCombMove inv S start (pre ++ a :: b :: post)
      (pre ++ ⟨s, l ++ [u], v⟩ :: post) B B' o o' σ := by
  have hc : (pre ++ (⟨s, l ++ [u], v⟩ : Event ι V) :: post)[pre.length]? =
      some ⟨s, l ++ [u], v⟩ := by simp
  have ha : (pre ++ a :: b :: post)[pre.length]? = some a := by simp
  have hb : (pre ++ a :: b :: post)[pre.length + 1]? = some b := by
    simp
  have hpLen : prepLen (pre ++ a :: b :: post) p = 0 := by simp [prepLen, hU]
  have hqLen : prepLen (pre ++ a :: b :: post) q = l.length := by simp [prepLen, hE]
  have hcLen : prepLen (pre ++ (⟨s, l ++ [u], v⟩ : Event ι V) :: post) pre.length =
      l.length + 1 := by simp [prepLen]
  have hdq : dn pre.length q = pre.length := dn_eq_iff.2 (by omega)
  have hpi : p = pre.length ∨ p = pre.length + 1 := by omega
  have hnotp : ∀ k, CombNode.pr p k ∉ combNodes S (pre ++ a :: b :: post) := by
    intro k; rw [pr_mem_combNodes, hpLen]; omega
  have hB : ∀ y : CombNode ι, y ∈ ({CombNode.gl pre.length, CombNode.gl (pre.length + 1)} :
      Finset (CombNode ι)) ↔ y = CombNode.gl pre.length ∨ y = CombNode.gl (pre.length + 1) := by
    intro y; simp
  have hB' : ∀ y : CombNode ι, y ∈ ({CombNode.pr pre.length l.length, CombNode.gl pre.length} :
      Finset (CombNode ι)) ↔ y = CombNode.pr pre.length l.length ∨ y = CombNode.gl pre.length := by
    intro y; simp
  -- nodes outside the block are good, and so are their parents
  have hgood : ∀ y ∈ combNodes S (pre ++ a :: b :: post) \
      {CombNode.gl pre.length, CombNode.gl (pre.length + 1)}, Good pre.length p y := by
    intro y hy
    rw [Finset.mem_sdiff, hB] at hy
    exact ⟨fun h => hy.2 (Or.inl h), fun k h => hnotp k (h ▸ hy.1)⟩
  have hpgood : ∀ y ∈ combNodes S (pre ++ a :: b :: post) \
      {CombNode.gl pre.length, CombNode.gl (pre.length + 1)},
      ∀ z ∈ combParents start (pre ++ a :: b :: post) y, Good pre.length p z := by
    intro y hy z hz
    rw [Finset.mem_sdiff, hB] at hy
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hy.2 (Or.inr (gl_mem_parents hz))
    · rintro k rfl
      rcases pr_mem_parents hz with rfl | ⟨rfl, -⟩
      · exact hnotp _ hy.1
      · rcases hpi with rfl | rfl
        · exact hy.2 (Or.inl rfl)
        · exact hy.2 (Or.inr rfl)
  -- parents commute with the node map outside the block
  have hparF : ∀ y ∈ combNodes S (pre ++ a :: b :: post) \
      {CombNode.gl pre.length, CombNode.gl (pre.length + 1)},
      combParents start (pre ++ ⟨s, l ++ [u], v⟩ :: post) (dnN pre.length y) =
        (combParents start (pre ++ a :: b :: post) y).image (dnN pre.length) := by
    intro y hy
    rw [Finset.mem_sdiff, hB, not_or] at hy
    rcases old_cases pre post a b l p q hpq hpLen hqLen y hy.1 hy.2.1 hy.2.2 with
      ⟨x, rfl, -⟩ | ⟨k, rfl, hk⟩ | ⟨j, k, rfl, h1, h2, -⟩ | ⟨j, rfl, h1, h2, -⟩
    · exact parents_dn pre post a b _ start _ (by simp)
    · exact parents_dn_q pre post a b u s l v q hdq hE k hk
    · refine parents_dn pre post a b _ start _ ?_
      rintro j' (h | ⟨k', h⟩) <;> simp at h
      obtain ⟨rfl, -⟩ := h; exact ⟨h1, h2⟩
    · refine parents_dn pre post a b _ start _ ?_
      rintro j' (h | ⟨k', h⟩) <;> simp at h
      subst h; exact ⟨h1, h2⟩
  have hkey : ∀ z, Good pre.length p z → ∀ y ∈ combNodes S (pre ++ a :: b :: post) \
      {CombNode.gl pre.length, CombNode.gl (pre.length + 1)},
      (dnN pre.length z ∈ combParents start (pre ++ ⟨s, l ++ [u], v⟩ :: post) (dnN pre.length y) ↔
        z ∈ combParents start (pre ++ a :: b :: post) y) := by
    intro z hz y hy
    rw [hparF y hy, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, hwz⟩
      rwa [← dnN_inj hpi (hpgood y hy w hw) hz hwz]
    · intro h; exact ⟨z, h, rfl⟩
  have hlab : ∀ y ∈ combNodes S (pre ++ a :: b :: post) \
      {CombNode.gl pre.length, CombNode.gl (pre.length + 1)},
      combLabel inv start (pre ++ ⟨s, l ++ [u], v⟩ :: post) (dnN pre.length y) =
        combLabel inv start (pre ++ a :: b :: post) y := by
    intro y hy
    rw [Finset.mem_sdiff, hB, not_or] at hy
    rcases old_cases pre post a b l p q hpq hpLen hqLen y hy.1 hy.2.1 hy.2.2 with
      ⟨x, rfl, -⟩ | ⟨k, rfl, hk⟩ | ⟨j, k, rfl, h1, h2, -⟩ | ⟨j, rfl, h1, h2, -⟩
    · rfl
    · simp only [combLabel, dnN, hdq, hc, hE, Option.map_some, Option.getD_some]
      exact sideLabel_snoc_le inv s l u v _ hk
    · simp only [combLabel, dnN]
      rw [getElem?_dn pre post a b _ j h1 h2]
    · exact goal_take_dn pre post a b _ inv start heq j h1
  have hmaps : Set.MapsTo (dnN pre.length)
      (↑(combNodes S (pre ++ a :: b :: post) \
        {CombNode.gl pre.length, CombNode.gl (pre.length + 1)}) : Set (CombNode ι))
      ↑(combNodes S (pre ++ ⟨s, l ++ [u], v⟩ :: post) \
        {CombNode.pr pre.length l.length, CombNode.gl pre.length}) := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_sdiff, hB, not_or] at hy
    rw [Finset.mem_coe, Finset.mem_sdiff, hB']
    rcases old_cases pre post a b l p q hpq hpLen hqLen y hy.1 hy.2.1 hy.2.2 with
      ⟨x, rfl, hx⟩ | ⟨k, rfl, hk⟩ | ⟨j, k, rfl, h1, h2, hk⟩ | ⟨j, rfl, h1, h2, hj⟩
    · simp [dnN, src_mem_combNodes, hx]
    · simp only [dnN, hdq, pr_mem_combNodes, hcLen]
      refine ⟨by omega, ?_⟩
      simp; omega
    · simp only [dnN, pr_mem_combNodes]
      rw [prepLen_dn pre post a b _ j h1 h2]
      refine ⟨hk, ?_⟩
      have : dn pre.length j ≠ pre.length := fun h => by rcases dn_eq_iff.1 h with h | h <;> simp_all
      simp [this]
    · simp only [dnN, gl_mem_combNodes, List.length_append, List.length_cons]
      have : dn pre.length j ≠ pre.length := fun h => by rcases dn_eq_iff.1 h with h | h <;> simp_all
      refine ⟨?_, by simp [this]⟩
      unfold dn; split_ifs <;> omega
  have hinj : Set.InjOn (dnN pre.length)
      (↑(combNodes S (pre ++ a :: b :: post) \
        {CombNode.gl pre.length, CombNode.gl (pre.length + 1)}) : Set (CombNode ι)) := by
    intro x hx y hy h
    exact dnN_inj hpi (hgood x hx) (hgood y hy) h
  have hsurj : Set.SurjOn (dnN pre.length)
      (↑(combNodes S (pre ++ a :: b :: post) \
        {CombNode.gl pre.length, CombNode.gl (pre.length + 1)}) : Set (CombNode ι))
      ↑(combNodes S (pre ++ ⟨s, l ++ [u], v⟩ :: post) \
        {CombNode.pr pre.length l.length, CombNode.gl pre.length}) := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_sdiff, hB', not_or] at hy
    obtain ⟨hy, hy1, hy2⟩ := hy
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_sdiff, hB, not_or]
    cases y with
    | src x =>
      rw [src_mem_combNodes] at hy
      exact ⟨CombNode.src x, ⟨(src_mem_combNodes _ _ _).2 hy, by simp, by simp⟩, rfl⟩
    | pr j k =>
      rw [pr_mem_combNodes] at hy
      rcases lt_trichotomy j pre.length with h | rfl | h
      · refine ⟨CombNode.pr j k, ⟨?_, by simp, by simp⟩, by simp [dnN, dn_of_lt h]⟩
        rw [pr_mem_combNodes, ← prepLen_dn pre post a b _ j (by omega) (by omega), dn_of_lt h]
        exact hy
      · refine ⟨CombNode.pr q k, ⟨?_, by simp, by simp⟩, by simp [dnN, hdq]⟩
        rw [pr_mem_combNodes, hqLen]
        rw [hcLen] at hy
        have : k ≠ l.length := fun h => hy1 (by rw [h])
        omega
      · refine ⟨CombNode.pr (j + 1) k, ⟨?_, by simp, by simp⟩, ?_⟩
        · rw [pr_mem_combNodes, ← prepLen_dn pre post a b _ (j + 1) (by omega) (by omega),
            dn_of_gt (by omega)]
          exact hy
        · simp [dnN, dn_of_gt (show pre.length < j + 1 by omega)]
    | gl j =>
      rw [gl_mem_combNodes] at hy
      simp only [List.length_append, List.length_cons] at hy
      have hj : j ≠ pre.length := fun h => hy2 (by rw [h])
      rcases lt_or_gt_of_ne hj with h | h
      · refine ⟨CombNode.gl j, ⟨?_, by simp; omega, by simp; omega⟩, by simp [dnN, dn_of_lt h]⟩
        rw [gl_mem_combNodes]; simp; omega
      · refine ⟨CombNode.gl (j + 1), ⟨?_, by simp; omega, by simp; omega⟩, ?_⟩
        · rw [gl_mem_combNodes]; simp; omega
        · simp [dnN, dn_of_gt (show pre.length < j + 1 by omega)]
  have hqB : CombNode.gl q ∈ ({CombNode.gl pre.length, CombNode.gl (pre.length + 1)} :
      Finset (CombNode ι)) := by rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hpB : CombNode.gl p ∈ ({CombNode.gl pre.length, CombNode.gl (pre.length + 1)} :
      Finset (CombNode ι)) := by rcases hpi with rfl | rfl <;> simp
  have hu' : (l ++ [u])[l.length]? = some u := by simp
  refine ⟨{CombNode.gl pre.length, CombNode.gl (pre.length + 1)},
    {CombNode.pr pre.length l.length, CombNode.gl pre.length}, CombNode.gl (pre.length + 1),
    CombNode.gl pre.length, dnN pre.length, ?_, ?_, Finset.card_le_two, Finset.card_le_two,
    ?_, ?_, by simp, by simp, ?_, ?_, ?_, ?_, ⟨hmaps, hinj, hsurj⟩, hlab, ?_, ?_, ?_, ?_, ?_,
    ?_, fun x _ => rfl⟩
  · intro y hy
    rcases (hB y).1 hy with rfl | rfl <;> simp [gl_mem_combNodes]
  · intro y hy
    rcases (hB' y).1 hy with rfl | rfl
    · rw [pr_mem_combNodes, hcLen]; omega
    · simp [gl_mem_combNodes]
  · intro y hy
    rcases (hB y).1 hy with rfl | rfl
    · rw [combParents_gl' _ _ _ a ha]; exact Finset.insert_nonempty _ _
    · rw [combParents_gl' _ _ _ b hb]; exact Finset.insert_nonempty _ _
  · intro y hy
    rcases (hB' y).1 hy with rfl | rfl
    · rw [combParents_pr _ _ _ _ _ hc]
      exact ⟨_, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
    · rw [combParents_gl' _ _ _ _ hc]; exact Finset.insert_nonempty _ _
  · intro y hy
    rcases (hB y).1 hy with rfl | rfl
    · right; rw [combParents_gl' _ _ _ b hb]; simp
    · left; rfl
  · intro y hy
    rcases (hB' y).1 hy with rfl | rfl
    · right; rw [combParents_gl' _ _ _ _ hc]; simp [topN]
    · left; rfl
  · intro y hy hne c _ hc'
    rcases (hB y).1 hy with rfl | rfl
    · rw [gl_mem_parents hc']; simp
    · exact absurd rfl hne
  · intro y hy hne c hcn hc'
    rcases (hB' y).1 hy with rfl | rfl
    · rcases pr_mem_parents hc' with rfl | ⟨rfl, -⟩
      · rw [pr_mem_combNodes, hcLen] at hcn; omega
      · simp
    · exact absurd rfl hne
  · have := goal_take_dn pre post a b _ inv start heq (pre.length + 1) (by omega)
    rw [dn_of_gt (by omega), Nat.add_sub_cancel] at this
    exact this
  · intro x hx y hy
    exact hkey x (hgood x hx) y hy
  · intro x hx y hy h
    have hxn := (Finset.mem_sdiff.1 hx).1
    rcases (hB' y).1 hy with rfl | rfl
    · rw [combParents_pr _ _ _ _ _ hc] at h
      simp only [hu', Option.map_some, Option.getD_some, Finset.mem_union,
        Finset.mem_singleton] at h
      rcases h with h | h
      · split_ifs at h with hn
        · rw [dnN_eq_src] at h; subst h
          refine ⟨CombNode.gl q, hqB, ?_⟩
          rw [combParents_gl' _ _ _ _ hE]; simp [topN, hn]
        · obtain ⟨j', rfl, hj'⟩ := dnN_eq_pr.1 h
          have hj'q : j' = q := by
            have := dn_eq_iff.1 hj'
            have : j' ≠ p := fun h => hnotp _ (h ▸ hxn)
            omega
          subst hj'q
          refine ⟨CombNode.gl j', hqB, ?_⟩
          rw [combParents_gl' _ _ _ _ hE]; simp [topN, hn]
      · rw [dnN_eq_src] at h; subst h
        refine ⟨CombNode.gl p, hpB, ?_⟩
        rw [combParents_gl' _ _ _ _ hU]; simp [topN]
    · rw [combParents_gl' _ _ _ _ hc] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · refine ⟨CombNode.gl pre.length, by simp, ?_⟩
        rw [combParents_gl' _ _ _ a ha]
        split_ifs at h ⊢ with hi
        · rw [dnN_eq_src] at h; subst h; simp
        · obtain ⟨j', rfl, hj'⟩ := dnN_eq_gl.1 h
          have : j' = pre.length - 1 := by unfold dn at hj'; split_ifs at hj' <;> omega
          subst this; simp
      · exfalso
        unfold topN at h
        simp only [List.length_append, List.length_singleton, Nat.add_eq_zero_iff, one_ne_zero,
          and_false, ↓reduceIte, Nat.add_sub_cancel] at h
        obtain ⟨j', rfl, hj'⟩ := dnN_eq_pr.1 h
        have := dn_eq_iff.1 hj'
        by_cases hj : j' = p
        · exact hnotp _ (hj ▸ hxn)
        · have : j' = q := by omega
          subst this
          rw [pr_mem_combNodes, hqLen] at hxn; omega
  · intro c hc
    have := hkey (CombNode.gl (pre.length + 1)) ⟨by simp, by simp⟩ c hc
    simpa [dnN, dn_of_gt (show pre.length < pre.length + 1 by omega)] using this
  · intro _
    simp only [combSink, List.length_append, List.length_cons]
    rw [if_neg (by omega), if_neg (by omega)]
    simp only [dnN]
    rw [dn_of_gt (by omega)]
    congr 1
  · intro h
    simp only [combSink, List.length_append, List.length_cons] at h ⊢
    rw [if_neg (by omega)] at h ⊢
    rw [if_neg (by omega)]
    rw [hB] at h
    simp only [CombNode.gl.injEq] at h
    constructor <;> congr 1 <;> omega

end ReconfRes.Frozen.Dev.Q427d.PartGC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC2
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-- (M3) A goal unit event immediately before an event becomes its last private deletion
(block: the two goal nodes ↦ the new private node and the goal node). -/
theorem combMove_absorb {inv : ι → Clause V} {S : Finset ι} {start : ι}
    (pre post : List (Event ι V)) (u : ι × V) (s : ι) (l : List (ι × V)) (x : V)
    (hnd : (srcList start (pre ++ ⟨u.1, [], u.2⟩ :: ⟨s, l, x⟩ :: post)).Nodup)
    (hS : (srcList start (pre ++ ⟨u.1, [], u.2⟩ :: ⟨s, l, x⟩ :: post)).toFinset = S)
    (heq : goalLabel inv start (pre ++ [⟨u.1, [], u.2⟩, ⟨s, l, x⟩]) =
      goalLabel inv start (pre ++ [⟨s, l ++ [u], x⟩])) :
    ∃ B B' o o' σ, IsCombMove inv S start (pre ++ ⟨u.1, [], u.2⟩ :: ⟨s, l, x⟩ :: post)
      (pre ++ ⟨s, l ++ [u], x⟩ :: post) B B' o o' σ :=
  absorb_move (pre := pre) (post := post) (a := ⟨u.1, [], u.2⟩) (b := ⟨s, l, x⟩) (u := u)
    (s := s) (l := l) (v := x) (p := pre.length) (q := pre.length + 1) (Or.inl ⟨rfl, rfl⟩)
    (by simp) (by simp) heq

end ReconfRes.Frozen.Dev.Q427d.PartGC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
alias combMove_absorb := ReconfRes.Frozen.Dev.Q427d.PartGC2.combMove_absorb

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartGC2
open ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-- (M3') A goal unit event immediately after an event becomes its last private deletion. -/
theorem combMove_absorbAfter {inv : ι → Clause V} {S : Finset ι} {start : ι}
    (pre post : List (Event ι V)) (u : ι × V) (s : ι) (l : List (ι × V)) (x : V)
    (hnd : (srcList start (pre ++ ⟨s, l, x⟩ :: ⟨u.1, [], u.2⟩ :: post)).Nodup)
    (hS : (srcList start (pre ++ ⟨s, l, x⟩ :: ⟨u.1, [], u.2⟩ :: post)).toFinset = S)
    (heq : goalLabel inv start (pre ++ [⟨s, l, x⟩, ⟨u.1, [], u.2⟩]) =
      goalLabel inv start (pre ++ [⟨s, l ++ [u], x⟩])) :
    ∃ B B' o o' σ, IsCombMove inv S start (pre ++ ⟨s, l, x⟩ :: ⟨u.1, [], u.2⟩ :: post)
      (pre ++ ⟨s, l ++ [u], x⟩ :: post) B B' o o' σ :=
  absorb_move (pre := pre) (post := post) (a := ⟨s, l, x⟩) (b := ⟨u.1, [], u.2⟩) (u := u)
    (s := s) (l := l) (v := x) (p := pre.length + 1) (q := pre.length) (Or.inr ⟨rfl, rfl⟩)
    (by simp) (by simp) heq

end ReconfRes.Frozen.Dev.Q427d.PartGC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
alias combMove_absorbAfter := ReconfRes.Frozen.Dev.Q427d.PartGC2.combMove_absorbAfter

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartV
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
theorem mem_stepG (inv : ι → Clause V) (g : Clause V) (e : Event ι V) (l : Literal V) :
    l ∈ stepG inv g e ↔
      l ∈ (sideLabel inv e e.prep.length).erase (e.pivot, true) ∨
        (l ≠ (e.pivot, false) ∧ l ∈ g) := by
  unfold stepG
  rw [Finset.mem_union, Finset.mem_erase (s := g)]

theorem snoc_decomp {α : Type} {es p t : List α} {a e : α} (h : es ++ [a] = p ++ e :: t) :
    (t = [] ∧ p = es ∧ e = a) ∨ ∃ t', t = t' ++ [a] ∧ es = p ++ e :: t' := by
  rcases List.eq_nil_or_concat t with ht | ⟨t', b, ht⟩
  · subst ht
    left
    have := List.append_inj' h (by simp)
    simp only [List.cons.injEq, and_true] at this
    exact ⟨rfl, this.1.symm, this.2.symm⟩
  · subst ht
    right
    refine ⟨t', ?_, ?_⟩
    · have h2 : es ++ [a] = (p ++ e :: t') ++ [b] := by simp [h]
      have := List.append_inj' h2 (by simp)
      simp only [List.cons.injEq, and_true] at this
      rw [this.2, List.concat_eq_append]
    · have h2 : es ++ [a] = (p ++ e :: t') ++ [b] := by simp [h]
      exact (List.append_inj' h2 (by simp)).1

/-- Membership in a goal clause: the literal comes from the start clause or from the prepared side
clause (pivot removed) of some event, and no later event resolves it away. -/
theorem mem_goalLabel (inv : ι → Clause V) (start : ι) (es : List (Event ι V)) (l : Literal V) :
    l ∈ goalLabel inv start es ↔
      (l ∈ inv start ∧ ∀ e ∈ es, l ≠ (e.pivot, false)) ∨
      ∃ p e t, es = p ++ e :: t ∧ l ∈ (sideLabel inv e e.prep.length).erase (e.pivot, true) ∧
        ∀ e' ∈ t, l ≠ (e'.pivot, false) := by
  induction es using List.reverseRecOn with
  | nil =>
    simp only [goalLabel, List.foldl_nil, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    constructor
    · exact Or.inl
    · rintro (h | ⟨p, e, t, h, -⟩)
      · exact h
      · simp at h
  | append_singleton es a ih =>
    rw [goalLabel_snoc, mem_stepG, ih]
    constructor
    · rintro (h | ⟨hne, (⟨h1, h2⟩ | ⟨p, e, t, hpe, h1, h2⟩)⟩)
      · exact Or.inr ⟨es, a, [], rfl, h, by simp⟩
      · left
        refine ⟨h1, ?_⟩
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact h2 e he
        · simp at he; subst he; exact hne
      · right
        refine ⟨p, e, t ++ [a], by simp [hpe], h1, ?_⟩
        intro e' he'
        rcases List.mem_append.1 he' with he' | he'
        · exact h2 e' he'
        · simp at he'; subst he'; exact hne
    · rintro (⟨h1, h2⟩ | ⟨p, e, t, hpe, h1, h2⟩)
      · right
        exact ⟨h2 a (by simp), Or.inl ⟨h1, fun e he => h2 e (by simp [he])⟩⟩
      · rcases snoc_decomp hpe with ⟨rfl, rfl, rfl⟩ | ⟨t', rfl, rfl⟩
        · exact Or.inl h1
        · right
          exact ⟨h2 a (by simp), Or.inr ⟨p, e, t', rfl, h1, fun e' he' => h2 e' (by simp [he'])⟩⟩

end ReconfRes.Frozen.Dev.Q427d.PartV
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### Part V: validity transfer and clause facts (pure list/finset) -/
alias mem_goalLabel := ReconfRes.Frozen.Dev.Q427d.PartV.mem_goalLabel

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartV
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-- Two goal steps commute when neither prepared side (pivot removed) contains the other's
negated pivot. -/
theorem step_comm (inv : ι → Clause V) (g : Clause V) (e₁ e₂ : Event ι V)
    (h₁ : (e₂.pivot, false) ∉ (sideLabel inv e₁ e₁.prep.length).erase (e₁.pivot, true))
    (h₂ : (e₁.pivot, false) ∉ (sideLabel inv e₂ e₂.prep.length).erase (e₂.pivot, true)) :
    stepG inv (stepG inv g e₁) e₂ = stepG inv (stepG inv g e₂) e₁ := by
  ext l
  simp only [mem_stepG]
  constructor
  · rintro (h | ⟨hne, h | ⟨hne', h⟩⟩)
    · right; exact ⟨fun hl => h₂ (hl ▸ h), Or.inl h⟩
    · left; exact h
    · right; exact ⟨hne', Or.inr ⟨hne, h⟩⟩
  · rintro (h | ⟨hne, h | ⟨hne', h⟩⟩)
    · right; exact ⟨fun hl => h₁ (hl ▸ h), Or.inl h⟩
    · left; exact h
    · right; exact ⟨hne', Or.inr ⟨hne, h⟩⟩

end ReconfRes.Frozen.Dev.Q427d.PartV
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
alias step_comm := ReconfRes.Frozen.Dev.Q427d.PartV.step_comm

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartV
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-- Any two permutations of one list are joined by adjacent transpositions through permutations. -/
theorem perm_of_adjSwap {α : Type} (Rel : List α → List α → Prop) (l₀ : List α)
    (hrefl : ∀ l, l.Perm l₀ → Rel l l)
    (htrans : ∀ a b c, a.Perm l₀ → b.Perm l₀ → c.Perm l₀ → Rel a b → Rel b c → Rel a c)
    (hswap : ∀ p x y t, (p ++ x :: y :: t).Perm l₀ → Rel (p ++ x :: y :: t) (p ++ y :: x :: t))
    {l₁ l₂ : List α} (h₁ : l₁.Perm l₀) (h₂ : l₂.Perm l₀) : Rel l₁ l₂ := by
  have key : ∀ {a b : List α}, a.Perm b → ∀ p : List α, (p ++ a).Perm l₀ →
      Rel (p ++ a) (p ++ b) := by
    intro a b hab
    induction hab with
    | nil => intro p hp; exact hrefl _ hp
    | cons x _ ih =>
      intro p hp
      have := ih (p ++ [x]) (by simpa using hp)
      simpa using this
    | swap x y t =>
      intro p hp
      exact hswap p y x t hp
    | trans h12 h23 ih12 ih23 =>
      intro p hp
      have hp2 : (p ++ _).Perm l₀ := ((h12.append_left p).symm.trans hp)
      exact htrans _ _ _ hp hp2 (((h23.append_left p).symm.trans hp2)) (ih12 p hp) (ih23 p hp2)
  simpa using key (h₁.trans h₂.symm) [] (by simpa using h₁)

/-! ### Validity transfer -/
/-- The goal-path conditions of `CombValid`, recursively from a current goal clause. -/
def GOK (inv : ι → Clause V) (w : ℕ) : Clause V → List (Event ι V) → Prop
  | _, [] => True
  | g, e :: t => (e.pivot, false) ∈ g ∧ (stepG inv g e).card ≤ w ∧ GOK inv w (stepG inv g e) t

theorem decomp_iff (inv : ι → Clause V) (w : ℕ) (es : List (Event ι V)) (g : Clause V) :
    (∀ p e t, es = p ++ e :: t → (e.pivot, false) ∈ p.foldl (stepG inv) g ∧
      ((p ++ [e]).foldl (stepG inv) g).card ≤ w) ↔ GOK inv w g es := by
  induction es generalizing g with
  | nil =>
    simp only [GOK, iff_true]
    intro p e t h
    simp at h
  | cons a es ih =>
    simp only [GOK]
    constructor
    · intro H
      have h0 := H [] a es rfl
      simp only [List.foldl_nil, List.nil_append, List.foldl_cons] at h0
      refine ⟨h0.1, h0.2, (ih _).1 ?_⟩
      intro p e t hes
      have := H (a :: p) e t (by simp [hes])
      simpa using this
    · rintro ⟨h1, h2, h3⟩ p e t hes
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hes
        obtain ⟨rfl, rfl⟩ := hes
        simpa using ⟨h1, h2⟩
      | cons b p =>
        simp only [List.cons_append, List.cons.injEq] at hes
        obtain ⟨rfl, rfl⟩ := hes
        have := ((ih _).2 h3) p e t rfl
        simpa using this

theorem GOK_append (inv : ι → Clause V) (w : ℕ) (p q : List (Event ι V)) (g : Clause V) :
    GOK inv w g (p ++ q) ↔ GOK inv w g p ∧ GOK inv w (p.foldl (stepG inv) g) q := by
  induction p generalizing g with
  | nil => simp [GOK]
  | cons a p ih =>
    simp only [List.cons_append, GOK, ih, List.foldl_cons]
    tauto

theorem cond_iff (inv : ι → Clause V) (start : ι) (w : ℕ) (es : List (Event ι V)) :
    (∀ p e t, es = p ++ e :: t →
      (e.pivot, false) ∈ goalLabel inv start p ∧ (goalLabel inv start (p ++ [e])).card ≤ w) ↔
      GOK inv w (inv start) es :=
  decomp_iff inv w es (inv start)

theorem sideLabel_append_le (inv : ι → Clause V) (sd : ι) (l m : List (ι × V)) (x : V) (n : ℕ)
    (hn : n ≤ l.length) :
    sideLabel inv ⟨sd, l ++ m, x⟩ n = sideLabel inv ⟨sd, l, x⟩ n := by
  simp [sideLabel, List.take_append_of_le_length hn]

theorem sideLabel_snoc (inv : ι → Clause V) (sd : ι) (l : List (ι × V)) (u : ι × V) (x : V) :
    sideLabel inv ⟨sd, l ++ [u], x⟩ (l.length + 1) =
      (sideLabel inv ⟨sd, l, x⟩ l.length).erase (u.2, false) := by
  simp [sideLabel, List.take_of_length_le, List.foldl_append]

theorem valid_swap {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V} {w s : ℕ}
    {pre post : List (Event ι V)} {e₁ e₂ : Event ι V}
    (h : CombValid inv S start F w s (pre ++ e₁ :: e₂ :: post))
    (hp₂ : (e₂.pivot, false) ∈ goalLabel inv start pre)
    (hp₁ : (e₁.pivot, false) ∈ goalLabel inv start (pre ++ [e₂]))
    (hw : (goalLabel inv start (pre ++ [e₂])).card ≤ w)
    (heq : goalLabel inv start (pre ++ [e₁, e₂]) = goalLabel inv start (pre ++ [e₂, e₁])) :
    CombValid inv S start F w s (pre ++ e₂ :: e₁ :: post) := by
  obtain ⟨hnd, hS, hF, hev, hgoal, hend, hsz⟩ := h
  have hperm : (srcList start (pre ++ e₂ :: e₁ :: post)).Perm
      (srcList start (pre ++ e₁ :: e₂ :: post)) := by
    simp only [srcList, List.flatMap_append, List.flatMap_cons]
    exact List.Perm.cons _ (List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _))
  simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil] at hp₁ hw heq hend
  set G := pre.foldl (stepG inv) (inv start)
  rw [cond_iff, GOK_append] at hgoal
  obtain ⟨hpre, h1, h2, h3, h4, h5⟩ := hgoal
  refine ⟨hperm.nodup_iff.2 hnd, (List.toFinset_eq_of_perm _ _ hperm).trans hS, hF, ?_, ?_, ?_, hsz⟩
  · intro e he
    apply hev
    simp only [List.mem_append, List.mem_cons] at he ⊢
    tauto
  · rw [cond_iff, GOK_append]
    refine ⟨hpre, hp₂, hw, hp₁, heq ▸ h4, heq ▸ h5⟩
  · rw [goalLabel_eq_foldl]
    simp only [List.foldl_append, List.foldl_cons]
    rw [← heq]
    exact hend

end ReconfRes.Frozen.Dev.Q427d.PartV
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
alias valid_swap := ReconfRes.Frozen.Dev.Q427d.PartV.valid_swap

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartV
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
theorem valid_absorb {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V} {w s : ℕ}
    {pre post : List (Event ι V)} {u : ι × V} {sd : ι} {l : List (ι × V)} {x : V}
    (h : CombValid inv S start F w s (pre ++ ⟨u.1, [], u.2⟩ :: ⟨sd, l, x⟩ :: post))
    (hu : inv u.1 = {(u.2, true)})
    (hmem : (u.2, false) ∈ sideLabel inv ⟨sd, l, x⟩ l.length)
    (hpiv : (x, true) ∈ sideLabel inv ⟨sd, l ++ [u], x⟩ (l.length + 1))
    (heq : goalLabel inv start (pre ++ [⟨u.1, [], u.2⟩, ⟨sd, l, x⟩]) =
      goalLabel inv start (pre ++ [⟨sd, l ++ [u], x⟩])) :
    CombValid inv S start F w s (pre ++ ⟨sd, l ++ [u], x⟩ :: post) := by
  obtain ⟨hnd, hS, hF, hev, hgoal, hend, hsz⟩ := h
  have hperm : (srcList start (pre ++ ⟨sd, l ++ [u], x⟩ :: post)).Perm
      (srcList start (pre ++ ⟨u.1, [], u.2⟩ :: ⟨sd, l, x⟩ :: post)) := by
    simp only [srcList, List.flatMap_append, List.flatMap_cons, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.append_assoc, List.nil_append]
    refine List.Perm.cons _ (List.Perm.append_left _ ?_)
    have : (sd :: (List.map Prod.fst l ++ u.1 :: (List.flatMap
        (fun e => e.side :: List.map Prod.fst e.prep) post))).Perm
        (u.1 :: sd :: (List.map Prod.fst l ++ (List.flatMap
        (fun e => e.side :: List.map Prod.fst e.prep) post))) := by
      refine List.Perm.trans (List.Perm.cons _ List.perm_middle) (List.Perm.swap _ _ _)
    exact this
  simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil] at heq hend
  rw [cond_iff, GOK_append] at hgoal
  obtain ⟨hpre, h1, h2, h3, h4, h5⟩ := hgoal
  set G := pre.foldl (stepG inv) (inv start)
  have hunit : stepG inv G ⟨u.1, [], u.2⟩ = G.erase (u.2, false) := by
    unfold stepG
    simp [sideLabel, hu]
  refine ⟨hperm.nodup_iff.2 hnd, (List.toFinset_eq_of_perm _ _ hperm).trans hS, hF, ?_, ?_, ?_, hsz⟩
  · intro e he
    simp only [List.mem_append, List.mem_cons] at he
    rcases he with he | rfl | he
    · exact hev e (by simp [he])
    · have hold := hev ⟨sd, l, x⟩ (by simp)
      refine ⟨?_, by simpa using hpiv⟩
      intro l' u' t' hdec
      change l ++ [u] = _ at hdec
      rcases snoc_decomp hdec with ⟨rfl, rfl, rfl⟩ | ⟨t'', rfl, rfl⟩
      · refine ⟨hu, ?_⟩
        rw [sideLabel_append_le inv sd _ _ x _ le_rfl]
        exact hmem
      · obtain ⟨hA, hB⟩ := hold.1 l' u' t'' rfl
        refine ⟨hA, ?_⟩
        rw [sideLabel_append_le inv sd _ _ x _ (by simp)]
        exact hB
    · exact hev e (by simp [he])
  · rw [cond_iff, GOK_append]
    refine ⟨hpre, ?_, heq ▸ h4, heq ▸ h5⟩
    rw [hunit] at h3
    exact Finset.mem_of_mem_erase h3
  · rw [goalLabel_eq_foldl]
    simp only [List.foldl_append, List.foldl_cons]
    rw [← heq]
    exact hend

end ReconfRes.Frozen.Dev.Q427d.PartV
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
alias valid_absorb := ReconfRes.Frozen.Dev.Q427d.PartV.valid_absorb

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartV
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
theorem valid_splitAfter {inv : ι → Clause V} {S : Finset ι} {start : ι} {F : CNF V} {w s : ℕ}
    {pre post : List (Event ι V)} {u : ι × V} {sd : ι} {l : List (ι × V)} {x : V}
    (h : CombValid inv S start F w s (pre ++ ⟨sd, l ++ [u], x⟩ :: post))
    (hp : (u.2, false) ∈ goalLabel inv start (pre ++ [⟨sd, l, x⟩]))
    (hw : (goalLabel inv start (pre ++ [⟨sd, l, x⟩])).card ≤ w)
    (heq : goalLabel inv start (pre ++ [⟨sd, l, x⟩, ⟨u.1, [], u.2⟩]) =
      goalLabel inv start (pre ++ [⟨sd, l ++ [u], x⟩])) :
    CombValid inv S start F w s (pre ++ ⟨sd, l, x⟩ :: ⟨u.1, [], u.2⟩ :: post) := by
  obtain ⟨hnd, hS, hF, hev, hgoal, hend, hsz⟩ := h
  have hsrc : srcList start (pre ++ ⟨sd, l, x⟩ :: ⟨u.1, [], u.2⟩ :: post) =
      srcList start (pre ++ ⟨sd, l ++ [u], x⟩ :: post) := by
    simp [srcList, List.flatMap_append, List.flatMap_cons]
  simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil] at hp hw heq hend
  rw [cond_iff, GOK_append] at hgoal
  obtain ⟨hpre, h1, h2, h3⟩ := hgoal
  have hold := hev ⟨sd, l ++ [u], x⟩ (by simp)
  refine ⟨hsrc ▸ hnd, hsrc ▸ hS, hF, ?_, ?_, ?_, hsz⟩
  · intro e he
    simp only [List.mem_append, List.mem_cons] at he
    rcases he with he | rfl | rfl | he
    · exact hev e (by simp [he])
    · refine ⟨?_, ?_⟩
      · intro l' u' t' hdec
        change l = _ at hdec
        subst hdec
        obtain ⟨hA, hB⟩ := hold.1 l' u' (t' ++ [u]) (by simp)
        refine ⟨hA, ?_⟩
        rw [← sideLabel_append_le inv sd _ [u] x _ (by simp)]
        exact hB
      · have := hold.2
        simp only [List.length_append, List.length_cons, List.length_nil, zero_add] at this
        rw [sideLabel_snoc] at this
        exact Finset.mem_of_mem_erase this
    · refine ⟨?_, ?_⟩
      · intro l' u' t' hdec
        simp at hdec
      · obtain ⟨hA, -⟩ := hold.1 l u [] rfl
        simp [sideLabel, hA]
    · exact hev e (by simp [he])
  · rw [cond_iff, GOK_append]
    exact ⟨hpre, h1, hw, hp, heq ▸ h2, heq ▸ h3⟩
  · rw [goalLabel_eq_foldl]
    simp only [List.foldl_append, List.foldl_cons]
    rw [heq]
    exact hend

end ReconfRes.Frozen.Dev.Q427d.PartV
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
alias valid_splitAfter := ReconfRes.Frozen.Dev.Q427d.PartV.valid_splitAfter

alias perm_of_adjSwap := ReconfRes.Frozen.Dev.Q427d.PartV.perm_of_adjSwap

/-! ### Glue: links -/
theorem rtg_symm' {α : Type} {r : α → α → Prop} (hr : ∀ {x y : α}, r x y → r y x) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr hbc) ih

theorem link_refl {k : ℕ} {F : CNF V} {w s : ℕ} {inv : ι → Clause V} {S : Finset ι} {start : ι}
    {es : List (Event ι V)} (h : CombValid inv S start F w s es) :
    CombLink k F w s inv S start es es :=
  ⟨h, h, fun R pos R' pos' hp hp' => Relation.ReflTransGen.single (iso_step k h R pos R' pos' hp hp')⟩

theorem link_symm {k : ℕ} {F : CNF V} {w s : ℕ} {inv : ι → Clause V} {S : Finset ι} {start : ι}
    {es es' : List (Event ι V)} (h : CombLink k F w s inv S start es es') :
    CombLink k F w s inv S start es' es :=
  ⟨h.2.1, h.1, fun R pos R' pos' hp hp' => rtg_symm' (fun hs => step_symm hs) (h.2.2 R' pos' R pos hp' hp)⟩

theorem link_trans {k : ℕ} {F : CNF V} {w s : ℕ} {inv : ι → Clause V} {S : Finset ι} {start : ι}
    {a b c : List (Event ι V)} (h₁ : CombLink k F w s inv S start a b)
    (h₂ : CombLink k F w s inv S start b c) : CombLink k F w s inv S start a c := by
  refine ⟨h₁.1, h₂.2.1, fun R pos R' pos' hp hp' => ?_⟩
  obtain ⟨Rb, posb, hb⟩ := exists_presentation h₁.2.1
  exact (h₁.2.2 R pos Rb posb hp hb).trans (h₂.2.2 Rb posb R' pos' hb hp')

theorem link_of_move {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {es es' : List (Event ι V)}
    (h : CombValid inv S start F w s es) (h' : CombValid inv S start F w s es')
    (hm : ∃ B B' o o' σ, IsCombMove inv S start es es' B B' o o' σ) :
    CombLink k F w s inv S start es es' := by
  obtain ⟨B, B', o, o', σ, hm⟩ := hm
  exact ⟨h, h', fun R pos R' pos' hp hp' =>
    Relation.ReflTransGen.single (step_of_combMove hk h h' hm R pos R' pos' hp hp')⟩

/-- (M1) with validity transfer. -/
theorem link_swap {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {e₁ e₂ : Event ι V}
    (h : CombValid inv S start F w s (pre ++ e₁ :: e₂ :: post))
    (hp₂ : (e₂.pivot, false) ∈ goalLabel inv start pre)
    (hp₁ : (e₁.pivot, false) ∈ goalLabel inv start (pre ++ [e₂]))
    (hw : (goalLabel inv start (pre ++ [e₂])).card ≤ w)
    (heq : goalLabel inv start (pre ++ [e₁, e₂]) = goalLabel inv start (pre ++ [e₂, e₁])) :
    CombLink k F w s inv S start (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) :=
  link_of_move hk h (valid_swap h hp₂ hp₁ hw heq) (combMove_swap pre post e₁ e₂ h.1 h.2.1 heq)

/-- (M1) between two lists already known valid. -/
theorem link_swap' {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {e₁ e₂ : Event ι V}
    (h : CombValid inv S start F w s (pre ++ e₁ :: e₂ :: post))
    (h' : CombValid inv S start F w s (pre ++ e₂ :: e₁ :: post))
    (heq : goalLabel inv start (pre ++ [e₁, e₂]) = goalLabel inv start (pre ++ [e₂, e₁])) :
    CombLink k F w s inv S start (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) :=
  link_of_move hk h h' (combMove_swap pre post e₁ e₂ h.1 h.2.1 heq)

/-- (M2) between two lists already known valid. -/
theorem link_prepSwap {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {sd : ι} {l t : List (ι × V)}
    {u₁ u₂ : ι × V} {x : V}
    (h : CombValid inv S start F w s (pre ++ ⟨sd, l ++ u₁ :: u₂ :: t, x⟩ :: post))
    (h' : CombValid inv S start F w s (pre ++ ⟨sd, l ++ u₂ :: u₁ :: t, x⟩ :: post)) :
    CombLink k F w s inv S start (pre ++ ⟨sd, l ++ u₁ :: u₂ :: t, x⟩ :: post)
      (pre ++ ⟨sd, l ++ u₂ :: u₁ :: t, x⟩ :: post) :=
  link_of_move hk h h' (combMove_prepSwap pre post sd l t u₁ u₂ x h.1 h.2.1)

/-- (M3) with validity transfer. -/
theorem link_absorb {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {u : ι × V} {sd : ι}
    {l : List (ι × V)} {x : V}
    (h : CombValid inv S start F w s (pre ++ ⟨u.1, [], u.2⟩ :: ⟨sd, l, x⟩ :: post))
    (hu : inv u.1 = {(u.2, true)})
    (hmem : (u.2, false) ∈ sideLabel inv ⟨sd, l, x⟩ l.length)
    (hpiv : (x, true) ∈ sideLabel inv ⟨sd, l ++ [u], x⟩ (l.length + 1))
    (heq : goalLabel inv start (pre ++ [⟨u.1, [], u.2⟩, ⟨sd, l, x⟩]) =
      goalLabel inv start (pre ++ [⟨sd, l ++ [u], x⟩])) :
    CombLink k F w s inv S start (pre ++ ⟨u.1, [], u.2⟩ :: ⟨sd, l, x⟩ :: post)
      (pre ++ ⟨sd, l ++ [u], x⟩ :: post) :=
  link_of_move hk h (valid_absorb h hu hmem hpiv heq)
    (combMove_absorb pre post u sd l x h.1 h.2.1 heq)

/-- (M3') with validity transfer, in the splitting direction. -/
theorem link_splitAfter {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {u : ι × V} {sd : ι}
    {l : List (ι × V)} {x : V}
    (h : CombValid inv S start F w s (pre ++ ⟨sd, l ++ [u], x⟩ :: post))
    (hp : (u.2, false) ∈ goalLabel inv start (pre ++ [⟨sd, l, x⟩]))
    (hw : (goalLabel inv start (pre ++ [⟨sd, l, x⟩])).card ≤ w)
    (heq : goalLabel inv start (pre ++ [⟨sd, l, x⟩, ⟨u.1, [], u.2⟩]) =
      goalLabel inv start (pre ++ [⟨sd, l ++ [u], x⟩])) :
    CombLink k F w s inv S start (pre ++ ⟨sd, l ++ [u], x⟩ :: post)
      (pre ++ ⟨sd, l, x⟩ :: ⟨u.1, [], u.2⟩ :: post) := by
  have h' := valid_splitAfter h hp hw heq
  exact link_symm (link_of_move hk h' h
    (combMove_absorbAfter pre post u sd l x h'.1 h'.2.1 heq))

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ## The construction: events, segments, canonical lists -/
/-- Events of the construction. -/
abbrev Ev : Type := Event (Src D.TV) (CVar D.TV)

/-- Validity of a comb of the construction (every presentation is an indexed vertex of
`G^fr_2(F, W, 2α − 1)`). -/
def CombOK (es : List (Ev D)) : Prop :=
  CombValid D.inv D.srcs Src.G D.formula D.W (2 * D.α - 1) es

/-- All presentations of `es` and `es'` are joined at locality two, and both combs are valid. -/
def Link (es es' : List (Ev D)) : Prop :=
  CombLink 2 D.formula D.W (2 * D.α - 1) D.inv D.srcs Src.G es es'

/-- Goal clause of the construction's combs (start `G`). -/
abbrev goal (p : List (Ev D)) : Clause (CVar D.TV) := goalLabel D.inv Src.G p

/-- Raw head expansion. -/
def evH (h : Head D.TV) : Ev D := ⟨Src.C h, [], CVar.hd h⟩

/-- Expansion of `T` privately prepared with `P_v` for `v ∈ l`, in order. -/
def evT (l : List D.TV) : Ev D :=
  ⟨Src.C Head.T, l.map (fun v => (Src.P v, CVar.f v)), CVar.hd Head.T⟩

/-- Expansion of `b_v` privately prepared with `P_v`. -/
def evBP (v : D.TV) : Ev D := ⟨Src.C (Head.b v), [(Src.P v, CVar.f v)], CVar.hd (Head.b v)⟩

/-- Goal deletion of `f_v` with the unit `P_v`. -/
def evP (v : D.TV) : Ev D := ⟨Src.P v, [], CVar.f v⟩

/-- Goal deletion of `f_v` with the unit `Q_v`. -/
def evQ (v : D.TV) : Ev D := ⟨Src.Q v, [], CVar.f v⟩

/-- Expansion of `A`. -/
def evA : Ev D := ⟨Src.CA, [], CVar.A⟩

/-- The first-tree internal heads. -/
def seg1 (O : D.CanonOrders) : List (Ev D) := O.ord1.map (evH D)

/-- The unselected pairs `a_v, d_v`. -/
def unselSeg (l : List D.TV) : List (Ev D) := l.flatMap (fun v => [evH D (Head.a v), evQ D v])

/-- `U` and the second-tree internal heads. -/
def seg2 (O : D.CanonOrders) : List (Ev D) := evH D Head.U :: O.ord2.map (evH D)

/-- The selected packets `a_v, b_v, d_v`. -/
def selSeg (l : List D.TV) : List (Ev D) :=
  l.flatMap (fun v => [evH D (Head.a v), evH D (Head.b v), evQ D v])

/-- The prepared unselected `b_v`. -/
def prepSeg (l : List D.TV) : List (Ev D) := l.map (evBP D)

/-- `A` and the final deletions. -/
def tailSeg (O : D.CanonOrders) : List (Ev D) :=
  evA D :: O.final.map (fun s => ⟨s, [], D.finalVar s⟩)

/-- The canonical list before `A`. -/
def canonHead (O : D.CanonOrders) (lT lu ls lb : List D.TV) : List (Ev D) :=
  [evT D lT] ++ seg1 D O ++ unselSeg D lu ++ seg2 D O ++ selSeg D ls ++ prepSeg D lb

/-- The canonical event list with set orders `privT = lT`, `unsel = lu`, `sel = ls`,
`prepB = lb`. -/
def canonL (O : D.CanonOrders) (lT lu ls lb : List D.TV) : List (Ev D) :=
  canonHead D O lT lu ls lb ++ tailSeg D O

theorem canonEvents_eq (O : D.CanonOrders) (L : D.SetOrders) :
    D.canonEvents O L = canonL D O L.privT L.unsel L.sel L.prepB := by
  simp only [ConstrData.canonEvents, canonL, canonHead, evT, seg1, unselSeg, seg2, selSeg, prepSeg,
    tailSeg, evQ, evA, List.append_assoc, List.cons_append]
  rfl

/-- The set orders as lists (same conjuncts, same order, as `SetOrders.ValidFor`). -/
def ListsFor (X : Finset D.TV) (lT lu ls lb : List D.TV) : Prop :=
  lT.Nodup ∧ lT.toFinset = X ∧ ls.Nodup ∧ ls.toFinset = X ∧
  lu.Nodup ∧ lu.toFinset = Xᶜ ∧ lb.Nodup ∧ lb.toFinset = Xᶜ

theorem validFor_iff (L : D.SetOrders) (X : Finset D.TV) :
    ConstrData.SetOrders.ValidFor D L X ↔ ListsFor D X L.privT L.unsel L.sel L.prepB := Iff.rfl

/-! ## Part C: clause calculus of the construction -/
/-- The heads expanded by the events `p`. -/
def expd (p : List (Ev D)) : Finset (Head D.TV) :=
  D.heads.filter fun h => ∃ e ∈ p, e.pivot = CVar.hd h

/-- The active facts: `v` with `¬f_v` in the goal clause after `p`. -/
def bag (p : List (Ev D)) : Finset D.TV :=
  Finset.univ.filter fun v => (CVar.f v, false) ∈ goal D p

/-- The non-fact part of a goal clause before `A` when the heads `E` are expanded. -/
def headPart (E : Finset (Head D.TV)) : Clause (CVar D.TV) :=
  {(CVar.A, false)} ∪ (D.heads \ E).image (fun h => (CVar.hd h, false)) ∪
    E.image (fun h => (CVar.z h, false)) ∪
    (if Head.U ∈ E then D.ballast.image (fun j => (CVar.p j, false)) else ∅)

/-- The allowed events before `A`: a head expansion privately prepared by fact units of its own
facts, or a goal fact deletion. -/
def EvForm (e : Ev D) : Prop :=
  (∃ h ∈ D.heads, e.side = Src.C h ∧ e.pivot = CVar.hd h ∧
    ∀ u ∈ e.prep, ∃ v, (u = (Src.P v, CVar.f v) ∨ u = (Src.Q v, CVar.f v)) ∧ CVar.f v ∈ D.Xh h) ∨
  (∃ v, (e.side = Src.P v ∨ e.side = Src.Q v) ∧ e.prep = [] ∧ e.pivot = CVar.f v)

/-- Shape of a list of events before `A`: allowed events, distinct side sources, and no head is
expanded after one of its dependency children. -/
def Shape (p : List (Ev D)) : Prop :=
  (∀ e ∈ p, EvForm D e) ∧ (p.map Event.side).Nodup ∧
  ∀ (p₁ p₂ p₃ : List (Ev D)) (e₁ e₂ : Ev D) (h d : Head D.TV),
    p = p₁ ++ e₁ :: (p₂ ++ e₂ :: p₃) → e₁.pivot = CVar.hd d → e₂.pivot = CVar.hd h →
    d ∉ D.deps h

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### Generic helpers -/
theorem mem_foldl_erase (L : List (ι × V)) (c : Clause V) (l : Literal V) :
    l ∈ L.foldl (fun c u => c.erase (u.2, false)) c ↔ l ∈ c ∧ ∀ u ∈ L, l ≠ (u.2, false) := by
  induction L generalizing c with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

theorem mem_sideLabel_full (inv : ι → Clause V) (e : Event ι V) (l : Literal V) :
    l ∈ sideLabel inv e e.prep.length ↔ l ∈ inv e.side ∧ ∀ u ∈ e.prep, l ≠ (u.2, false) := by
  simp only [sideLabel, List.take_length, mem_foldl_erase]

theorem pair_sublist {α : Type} {a b : α} {l : List α} (h : [a, b].Sublist l) :
    ∃ p₁ p₂ p₃, l = p₁ ++ a :: (p₂ ++ b :: p₃) := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases List.sublist_cons_iff.1 h with h | ⟨r, hr, hs⟩
    · obtain ⟨p₁, p₂, p₃, rfl⟩ := ih h
      exact ⟨x :: p₁, p₂, p₃, rfl⟩
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨s, t, rfl⟩ := List.append_of_mem (List.singleton_sublist.1 hs)
      exact ⟨[], s, t, rfl⟩

theorem sublist_pair {α : Type} {a b : α} (p₁ p₂ p₃ : List α) :
    [a, b].Sublist (p₁ ++ a :: (p₂ ++ b :: p₃)) := by
  have : [a, b].Sublist (a :: (p₂ ++ b :: p₃)) :=
    List.Sublist.cons_cons _ (List.singleton_sublist.2 (by simp))
  exact this.trans (List.sublist_append_right _ _)

end ReconfRes.Frozen.Dev.Q427d.PartC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
/-! ### Trees and heads -/
theorem node_internal {τ : Type} (t : FBTree τ) {q : List Bool} {l r : FBTree τ}
    (h : t.subtreeAt q = some (FBTree.node l r)) : q ∈ t.internalPaths := by
  induction t generalizing q with
  | leaf v =>
    cases q with
    | nil => simp [FBTree.subtreeAt] at h
    | cons c q => simp [FBTree.subtreeAt] at h
  | node l' r' ihl ihr =>
    cases q with
    | nil => simp [FBTree.internalPaths]
    | cons c q =>
      cases c
      · simp only [FBTree.subtreeAt] at h
        simp [FBTree.internalPaths, ihl h]
      · simp only [FBTree.subtreeAt] at h
        simp [FBTree.internalPaths, ihr h]

end ReconfRes.Frozen.Dev.Q427d.PartC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
theorem T_mem : Head.T ∈ D.heads := by simp [ConstrData.heads]

theorem U_mem : Head.U ∈ D.heads := by simp [ConstrData.heads]

theorem head1_mem (q : List Bool) : D.head1 q ∈ D.heads := by
  unfold ConstrData.head1
  split
  · simp [ConstrData.heads]
  · rename_i l r hs
    split_ifs with hq
    · exact T_mem D
    · simp [ConstrData.heads, ConstrData.inner1, node_internal _ hs, hq]
  · exact T_mem D

theorem head2_mem (q : List Bool) : D.head2 q ∈ D.heads := by
  unfold ConstrData.head2
  split
  · simp [ConstrData.heads]
  · rename_i l r hs
    split_ifs with hq
    · exact U_mem D
    · simp [ConstrData.heads, ConstrData.inner2, node_internal _ hs, hq]
  · exact U_mem D

theorem deps_sub {h d : Head D.TV} (hd : d ∈ D.deps h) : d ∈ D.heads := by
  cases h with
  | T =>
    simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact head1_mem D _
    · exact head1_mem D _
    · exact U_mem D
  | U =>
    simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> exact head2_mem D _
  | i1 p =>
    simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> exact head1_mem D _
  | i2 p =>
    simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> exact head2_mem D _
  | a v =>
    simp only [ConstrData.deps, Finset.mem_image] at hd
    obtain ⟨u, -, rfl⟩ := hd
    simp [ConstrData.heads]
  | b v => simp [ConstrData.deps] at hd

theorem head1_i1 {q p : List Bool} (h : D.head1 q = Head.i1 p) : p = q := by
  unfold ConstrData.head1 at h
  split at h <;> (try split_ifs at h) <;> first | (cases h; done) | (cases h; rfl)

theorem head2_i2 {q p : List Bool} (h : D.head2 q = Head.i2 p) : p = q := by
  unfold ConstrData.head2 at h
  split at h <;> (try split_ifs at h) <;> first | (cases h; done) | (cases h; rfl)

theorem nil_internal (hD : D.Valid) (t : FBTree D.TV) (ht : ∀ v, v ∈ t.leaves) :
    [] ∈ t.internalPaths := by
  cases t with
  | leaf v =>
    exfalso
    have hn := hD.1
    have h1 := ht (⟨0, by omega⟩, ⟨0, by omega⟩)
    have h2 := ht (⟨1, by omega⟩, ⟨0, by omega⟩)
    simp only [FBTree.leaves, List.mem_singleton] at h1 h2
    rw [← h2] at h1
    simp [Prod.ext_iff] at h1
  | node l r => simp [FBTree.internalPaths]

theorem subtreeAt_append {τ : Type} (t : FBTree τ) (p q : List Bool) :
    t.subtreeAt (p ++ q) = (t.subtreeAt p).bind (fun s => s.subtreeAt q) := by
  induction t generalizing p with
  | leaf v => cases p <;> simp [FBTree.subtreeAt]
  | node l r ihl ihr =>
    cases p with
    | nil => simp [FBTree.subtreeAt]
    | cons c p => cases c <;> simp [FBTree.subtreeAt, ihl, ihr]

theorem internal_sub {τ : Type} (t : FBTree τ) (p : List Bool) (h : p ∈ t.internalPaths) :
    ∃ l r, t.subtreeAt p = some (FBTree.node l r) := by
  induction t generalizing p with
  | leaf v => simp [FBTree.internalPaths] at h
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths, List.mem_cons, List.mem_append, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨l, r, rfl⟩
    · simpa [FBTree.subtreeAt] using ihl q hq
    · simpa [FBTree.subtreeAt] using ihr q hq

theorem child_some {τ : Type} (t : FBTree τ) {p : List Bool} (hp : p ∈ t.internalPaths) (c : Bool) :
    ∃ s, t.subtreeAt (p ++ [c]) = some s := by
  obtain ⟨l, r, h⟩ := internal_sub t p hp
  rw [subtreeAt_append, h]
  cases c
  · exact ⟨l, by simp [FBTree.subtreeAt]⟩
  · exact ⟨r, by simp [FBTree.subtreeAt]⟩

theorem head1_child {p : List Bool} (hp : p ∈ D.t1.internalPaths) (c : Bool) :
    D.head1 (p ++ [c]) ≠ Head.T := by
  obtain ⟨s, hs⟩ := child_some D.t1 hp c
  unfold ConstrData.head1
  rw [hs]
  cases s with
  | leaf v => simp
  | node l r => simp

theorem head2_child {p : List Bool} (hp : p ∈ D.t2.internalPaths) (c : Bool) :
    D.head2 (p ++ [c]) ≠ Head.U := by
  obtain ⟨s, hs⟩ := child_some D.t2 hp c
  unfold ConstrData.head2
  rw [hs]
  cases s with
  | leaf v => simp
  | node l r => simp

theorem not_self_dep (hD : D.Valid) {h : Head D.TV} : h ∉ D.deps h := by
  cases h with
  | T =>
    have h0 := nil_internal D hD D.t1 hD.2.2.2.2.1.2
    simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => head1_child D h0 false (by simpa using h.symm),
      fun h => head1_child D h0 true (by simpa using h.symm), by simp⟩
  | U =>
    have h0 := nil_internal D hD D.t2 hD.2.2.2.2.2.2
    simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => head2_child D h0 false (by simpa using h.symm),
      fun h => head2_child D h0 true (by simpa using h.symm)⟩
  | i1 p =>
    simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := congrArg List.length (head1_i1 D h.symm)
      simp at this
  | i2 p =>
    simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := congrArg List.length (head2_i2 D h.symm)
      simp at this
  | a v => simp [ConstrData.deps]
  | b v => simp [ConstrData.deps]

/-! ### Clause membership -/
theorem hdf_mem_Ch {h d : Head D.TV} : (CVar.hd d, false) ∈ D.Ch h ↔ d ∈ D.deps h := by
  cases h <;> simp [ConstrData.Ch, ConstrData.Xh]

theorem zf_mem_Ch {h d : Head D.TV} : (CVar.z d, false) ∈ D.Ch h ↔ d = h := by
  cases h <;> simp [ConstrData.Ch, ConstrData.Xh, eq_comm]

theorem pf_mem_Ch {h : Head D.TV} {j : ℕ} :
    (CVar.p j, false) ∈ D.Ch h ↔ h = Head.U ∧ j ∈ D.ballast := by
  cases h <;> simp [ConstrData.Ch, ConstrData.Xh]

theorem pos_mem_Ch {h : Head D.TV} {x : CVar D.TV} : (x, true) ∈ D.Ch h ↔ x = CVar.hd h := by
  simp [ConstrData.Ch]

theorem side_iff {e : Ev D} (he : EvForm D e) (l : Literal (CVar D.TV)) :
    l ∈ (sideLabel D.inv e e.prep.length).erase (e.pivot, true) ↔
      ∃ h ∈ D.heads, e.side = Src.C h ∧ e.pivot = CVar.hd h ∧ l ∈ D.Ch h ∧
        l ≠ (CVar.hd h, true) ∧ ∀ u ∈ e.prep, l ≠ (u.2, false) := by
  rw [Finset.mem_erase, mem_sideLabel_full]
  rcases he with ⟨h, hh, hs, hp, -⟩ | ⟨v, hs, hprep, hp⟩
  · rw [hs, hp]
    constructor
    · rintro ⟨hne, hm, hall⟩
      exact ⟨h, hh, rfl, rfl, hm, hne, hall⟩
    · rintro ⟨h', -, hs', hp', hm, hne, hall⟩
      rw [Src.C.injEq] at hs'
      subst hs'
      exact ⟨hne, hm, hall⟩
  · constructor
    · rintro ⟨hne, hm, -⟩
      exfalso
      rcases hs with hs | hs <;> rw [hs] at hm <;>
        simp only [ConstrData.inv, Finset.mem_singleton] at hm <;> rw [hp] at hne <;> exact hne hm
    · rintro ⟨h', -, hs', -⟩
      rcases hs with hs | hs <;> rw [hs] at hs' <;> cases hs'

theorem evform_piv {e : Ev D} (he : EvForm D e) :
    (∃ h, e.pivot = CVar.hd h) ∨ ∃ v, e.pivot = CVar.f v := by
  rcases he with ⟨h, -, -, hp, -⟩ | ⟨v, -, -, hp⟩
  · exact Or.inl ⟨h, hp⟩
  · exact Or.inr ⟨v, hp⟩

theorem evform_prep {e : Ev D} (he : EvForm D e) : ∀ u ∈ e.prep, ∃ v, u.2 = CVar.f v := by
  rcases he with ⟨h, -, -, -, hu⟩ | ⟨v, -, hprep, -⟩
  · intro u hmem
    obtain ⟨v, hv | hv, -⟩ := hu u hmem <;> exact ⟨v, by rw [hv]⟩
  · simp [hprep]

theorem mem_expd {p : List (Ev D)} {d : Head D.TV} :
    d ∈ expd D p ↔ d ∈ D.heads ∧ ∃ e ∈ p, e.pivot = CVar.hd d := by
  simp [expd]

/-- Membership in the goal clause for a literal that is never a negated pivot. -/
theorem mem_goal_nf {p : List (Ev D)} (l : Literal (CVar D.TV))
    (hl : ∀ e ∈ p, l ≠ (e.pivot, false)) :
    l ∈ goal D p ↔ l ∈ D.Gc ∨ ∃ e ∈ p, l ∈ (sideLabel D.inv e e.prep.length).erase (e.pivot, true) := by
  rw [goal, Q427d.mem_goalLabel]
  constructor
  · rintro (⟨h1, -⟩ | ⟨p₁, e, t, rfl, h2, -⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨e, by simp, h2⟩
  · rintro (h1 | ⟨e, he, h2⟩)
    · exact Or.inl ⟨h1, hl⟩
    · obtain ⟨s, t, rfl⟩ := List.append_of_mem he
      exact Or.inr ⟨s, e, t, rfl, h2, fun e' he' => hl e' (by simp [he'])⟩

/-! ### Targets: sublists and bags -/
theorem shape_sublist {p p' : List (Ev D)} (h : Shape D p) (hs : p'.Sublist p) : Shape D p' := by
  refine ⟨fun e he => h.1 e (hs.subset he), h.2.1.sublist (hs.map _), ?_⟩
  intro p₁ p₂ p₃ e₁ e₂ hh d heq h1 h2
  subst heq
  obtain ⟨q₁, q₂, q₃, rfl⟩ := pair_sublist ((sublist_pair p₁ p₂ p₃).trans hs)
  exact h.2.2 q₁ q₂ q₃ e₁ e₂ hh d rfl h1 h2

end ReconfRes.Frozen.Dev.Q427d.PartC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias shape_sublist := ReconfRes.Frozen.Dev.Q427d.PartC1.shape_sublist

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
theorem mem_foldl_erase (L : List (ι × V)) (c : Clause V) (l : Literal V) :
    l ∈ L.foldl (fun c u => c.erase (u.2, false)) c ↔ l ∈ c ∧ ∀ u ∈ L, l ≠ (u.2, false) := by
  induction L generalizing c with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

theorem mem_sideLabel_full (inv : ι → Clause V) (e : Event ι V) (l : Literal V) :
    l ∈ sideLabel inv e e.prep.length ↔ l ∈ inv e.side ∧ ∀ u ∈ e.prep, l ≠ (u.2, false) := by
  simp only [sideLabel, List.take_length, mem_foldl_erase]

theorem sideLabel_sub (inv : ι → Clause V) (e : Event ι V) (j : ℕ) :
    sideLabel inv e j ⊆ inv e.side := by
  intro l hl
  simp only [sideLabel, mem_foldl_erase] at hl
  exact hl.1

/-- The non-start part of the source list. -/
def fl (es : List (Event ι V)) : List ι := es.flatMap (fun e => e.side :: e.prep.map Prod.fst)

theorem srcList_eq (start : ι) (es : List (Event ι V)) : srcList start es = start :: fl es := rfl

theorem fl_append (a b : List (Event ι V)) : fl (a ++ b) = fl a ++ fl b := by
  simp [fl, List.flatMap_append]

theorem side_mem_fl {es : List (Event ι V)} {e : Event ι V} (he : e ∈ es) : e.side ∈ fl es := by
  simp only [fl, List.mem_flatMap]
  exact ⟨e, he, List.mem_cons_self⟩

theorem prep_mem_fl {es : List (Event ι V)} {e : Event ι V} (he : e ∈ es) {u : ι × V}
    (hu : u ∈ e.prep) : u.1 ∈ fl es := by
  simp only [fl, List.mem_flatMap]
  exact ⟨e, he, List.mem_cons_of_mem _ (List.mem_map_of_mem hu)⟩

theorem mem_fl {es : List (Event ι V)} {s : ι} (h : s ∈ fl es) :
    ∃ e ∈ es, s = e.side ∨ ∃ u ∈ e.prep, u.1 = s := by
  simp only [fl, List.mem_flatMap, List.mem_cons, List.mem_map] at h
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h⟩

theorem map_side_sublist (es : List (Event ι V)) : (es.map Event.side).Sublist (fl es) := by
  induction es with
  | nil => simp [fl]
  | cons e es ih =>
    simp only [List.map_cons, fl, List.flatMap_cons, List.cons_append]
    exact List.Sublist.cons_cons _ (ih.trans (List.sublist_append_right _ _))

end ReconfRes.Frozen.Dev.Q427d.PartC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
theorem pos_hd {s : Src D.TV} {d : Head D.TV} (h : (CVar.hd d, true) ∈ D.inv s) : s = Src.C d := by
  cases s <;> simp_all [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc]

theorem pos_z {s : Src D.TV} {d : Head D.TV} (h : (CVar.z d, true) ∈ D.inv s) : s = Src.z d := by
  cases s <;> simp_all [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc]

theorem pos_p {s : Src D.TV} {j : ℕ} (h : (CVar.p j, true) ∈ D.inv s) : s = Src.p j := by
  cases s <;> simp_all [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc]

theorem pos_CA {x : CVar D.TV} (h : (x, true) ∈ D.CA) : x = CVar.A := by
  simp_all [ConstrData.CA]

theorem unit_cases {s : Src D.TV} {y : CVar D.TV} (h : D.inv s = {(y, true)}) :
    (∃ d, s = Src.z d ∧ y = CVar.z d) ∨ (∃ j, s = Src.p j ∧ y = CVar.p j) ∨
      (∃ v, (s = Src.P v ∨ s = Src.Q v) ∧ y = CVar.f v) := by
  cases s with
  | C d =>
    have : (CVar.A, false) ∈ D.inv (Src.C d) := by simp [ConstrData.inv, ConstrData.Ch]
    rw [h] at this; simp at this
  | CA =>
    have : (CVar.z Head.T, false) ∈ D.inv Src.CA := by
      simp [ConstrData.inv, ConstrData.CA, ConstrData.heads]
    rw [h] at this; simp at this
  | G =>
    have : (CVar.A, false) ∈ D.inv Src.G := by simp [ConstrData.inv, ConstrData.Gc]
    rw [h] at this; simp at this
  | z d =>
    simp only [ConstrData.inv, Finset.singleton_inj, Prod.mk.injEq, and_true] at h
    exact Or.inl ⟨d, rfl, h.symm⟩
  | p j =>
    simp only [ConstrData.inv, Finset.singleton_inj, Prod.mk.injEq, and_true] at h
    exact Or.inr (Or.inl ⟨j, rfl, h.symm⟩)
  | P v =>
    simp only [ConstrData.inv, Finset.singleton_inj, Prod.mk.injEq, and_true] at h
    exact Or.inr (Or.inr ⟨v, Or.inl rfl, h.symm⟩)
  | Q v =>
    simp only [ConstrData.inv, Finset.singleton_inj, Prod.mk.injEq, and_true] at h
    exact Or.inr (Or.inr ⟨v, Or.inr rfl, h.symm⟩)

theorem neg_Ch {h : Head D.TV} {x : CVar D.TV} (hx : (x, false) ∈ D.Ch h) :
    x = CVar.A ∨ x = CVar.z h ∨ (∃ d ∈ D.deps h, x = CVar.hd d) ∨ x ∈ D.Xh h := by
  simp only [ConstrData.Ch, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Prod.mk.injEq] at hx
  rcases hx with ((⟨_, h1⟩ | ⟨h1, _⟩ | ⟨h1, _⟩) | ⟨d, hd, h1, _⟩) | ⟨y, hy, h1, _⟩
  · exact absurd h1 (by decide)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl ⟨d, hd, h1.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (h1 ▸ hy)))

theorem pos_Ch {h : Head D.TV} {x : CVar D.TV} (hx : (x, true) ∈ D.Ch h) : x = CVar.hd h := by
  simp_all [ConstrData.Ch]

theorem z_not_mem_Xh {h d : Head D.TV} (hx : CVar.z d ∈ D.Xh h) : False := by
  cases h <;> simp [ConstrData.Xh] at hx

theorem p_mem_Xh {h : Head D.TV} {j : ℕ} (hx : CVar.p j ∈ D.Xh h) : j ∈ D.ballast := by
  cases h <;> simp [ConstrData.Xh] at hx
  exact hx

end ReconfRes.Frozen.Dev.Q427d.PartC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
variable {D}
variable {p t : List (Ev D)}
theorem ok_eventOK (h : CombOK D (p ++ t)) {e : Ev D} (he : e ∈ p ++ t) : EventOK D.inv e :=
  h.2.2.2.1 e he

theorem ok_unit (h : CombOK D (p ++ t)) {e : Ev D} (he : e ∈ p ++ t) {u : Src D.TV × CVar D.TV}
    (hu : u ∈ e.prep) : D.inv u.1 = {(u.2, true)} ∧ (u.2, false) ∈ D.inv e.side := by
  obtain ⟨l, t', hl⟩ := List.mem_iff_append.1 hu
  obtain ⟨h1, h2⟩ := (ok_eventOK h he).1 l u t' hl
  exact ⟨h1, sideLabel_sub _ _ _ h2⟩

theorem ok_pivot (h : CombOK D (p ++ t)) {e : Ev D} (he : e ∈ p ++ t) :
    (e.pivot, true) ∈ D.inv e.side :=
  sideLabel_sub _ _ _ (ok_eventOK h he).2

theorem ok_fl (h : CombOK D (p ++ t)) : Src.G ∉ fl (p ++ t) ∧ (fl (p ++ t)).Nodup := by
  have hnd := h.1
  rw [srcList_eq, List.nodup_cons] at hnd
  exact hnd

theorem ok_disj (h : CombOK D (p ++ t)) {s : Src D.TV} (hp : s ∈ fl p) (ht : s ∈ fl t) :
    False := by
  have hnd := (ok_fl h).2
  rw [fl_append, List.nodup_append] at hnd
  exact hnd.2.2 s hp s ht rfl

theorem exists_A (h : CombOK D (p ++ t)) (hA : ∀ e ∈ p, e.pivot ≠ CVar.A) :
    ∃ t1 eA t0, t = t1 ++ eA :: t0 ∧ eA.side = Src.CA := by
  have hmem : Src.CA ∈ srcList Src.G (p ++ t) := by
    rw [← List.mem_toFinset, h.2.1]; simp [ConstrData.srcs]
  rw [srcList_eq, List.mem_cons] at hmem
  rcases hmem with h1 | h1
  · exact absurd h1 (by simp)
  obtain ⟨e, he, hs | ⟨u, hu, hu1⟩⟩ := mem_fl h1
  · have hpiv := ok_pivot h he
    rw [← hs] at hpiv
    have : e.pivot = CVar.A := pos_CA D hpiv
    have het : e ∈ t := by
      rcases List.mem_append.1 he with h2 | h2
      · exact absurd this (hA e h2)
      · exact h2
    obtain ⟨t1, t0, ht⟩ := List.mem_iff_append.1 het
    exact ⟨t1, e, t0, ht, hs.symm⟩
  · have := (ok_unit h he hu).1
    rw [hu1] at this
    rcases unit_cases D this with ⟨d, h2, _⟩ | ⟨j, h2, _⟩ | ⟨v, h2 | h2, _⟩ <;> cases h2

theorem unused (h : CombOK D (p ++ t)) (hA : ∀ e ∈ p, e.pivot ≠ CVar.A) {x : CVar D.TV}
    {s : Src D.TV} (hx : (x, false) ∈ D.CA) (hs : ∀ s', (x, true) ∈ D.inv s' → s' = s) :
    s ∉ fl p := by
  intro hsp
  obtain ⟨t1, eA, t0, ht, hside⟩ := exists_A h hA
  have heA : eA ∈ p ++ t := by simp [ht]
  have heAt : eA ∈ t := by simp [ht]
  have hside' : (x, false) ∈ sideLabel D.inv eA eA.prep.length := by
    rw [mem_sideLabel_full]
    refine ⟨by rw [hside]; exact hx, fun u hu hxu => ?_⟩
    have h1 := (ok_unit h heA hu).1
    have h2 : (x, true) ∈ D.inv u.1 := by
      rw [h1]; simp only [Prod.mk.injEq] at hxu; rw [hxu.1]; simp
    have h3 := hs _ h2
    exact ok_disj h hsp (h3 ▸ prep_mem_fl heAt hu)
  have hgoal : goalLabel D.inv Src.G (p ++ t) = ∅ := h.2.2.2.2.2.1
  have hdec : p ++ t = (p ++ t1) ++ eA :: t0 := by simp [ht]
  by_cases hall : ∀ e' ∈ t0, (x, false) ≠ (e'.pivot, false)
  · have := (mem_goalLabel D.inv Src.G (p ++ t) (x, false)).2
      (Or.inr ⟨p ++ t1, eA, t0, hdec, Finset.mem_erase.2 ⟨by simp, hside'⟩, hall⟩)
    rw [hgoal] at this; simp at this
  · push Not at hall
    obtain ⟨e', he', hxe⟩ := hall
    have he't : e' ∈ t := by simp [ht, he']
    have h2 := ok_pivot h (List.mem_append_right p he't)
    simp only [Prod.mk.injEq] at hxe
    rw [← hxe.1] at h2
    exact ok_disj h hsp (hs _ h2 ▸ side_mem_fl he't)

theorem evForm (h : CombOK D (p ++ t)) (hA : ∀ e ∈ p, e.pivot ≠ CVar.A) {e : Ev D}
    (he : e ∈ p) : EvForm D e := by
  have he' : e ∈ p ++ t := List.mem_append_left t he
  have hpiv := ok_pivot h he'
  have hsm : e.side ∈ D.srcs := by
    rw [← h.2.1]
    exact List.mem_toFinset.2 (by rw [srcList_eq]; exact List.mem_cons_of_mem _ (side_mem_fl he'))
  have hG : e.side ≠ Src.G := by
    intro hg
    exact (ok_fl h).1 (hg ▸ side_mem_fl he')
  have hz : ∀ d ∈ D.heads, Src.z d ∉ fl p := fun d hd =>
    unused h hA (x := CVar.z d) (by simp [ConstrData.CA, hd]) (fun s' hs' => pos_z D hs')
  have hpj : ∀ j ∈ D.ballast, Src.p j ∉ fl p := fun j hj =>
    unused h hA (x := CVar.p j) (by simp [ConstrData.CA, hj]) (fun s' hs' => pos_p D hs')
  have hnoprep : ∀ v, (e.side = Src.P v ∨ e.side = Src.Q v) → e.prep = [] := by
    intro v hv
    match hpr : e.prep with
    | [] => rfl
    | u :: _ =>
      have := (ok_unit h he' (u := u) (by rw [hpr]; exact List.mem_cons_self)).2
      rcases hv with hv | hv <;> rw [hv] at this <;> simp [ConstrData.inv] at this
  cases hs : e.side with
  | C d =>
    rw [hs] at hpiv hsm
    have hpd : e.pivot = CVar.hd d := pos_Ch D hpiv
    have hdh : d ∈ D.heads := by simpa [ConstrData.srcs] using hsm
    refine Or.inl ⟨d, hdh, hs, hpd, fun u hu => ?_⟩
    obtain ⟨h1, h2⟩ := ok_unit h he' hu
    rw [hs] at h2
    rcases unit_cases D h1 with ⟨d', h3, h4⟩ | ⟨j, h3, h4⟩ | ⟨v, h3, h4⟩
    · exfalso
      rw [h4] at h2
      rcases neg_Ch D h2 with h5 | h5 | ⟨_, _, h5⟩ | h5
      · cases h5
      · cases h5
        exact hz _ hdh (h3 ▸ prep_mem_fl he hu)
      · cases h5
      · exact z_not_mem_Xh D h5
    · exfalso
      rw [h4] at h2
      rcases neg_Ch D h2 with h5 | h5 | ⟨_, _, h5⟩ | h5
      · cases h5
      · cases h5
      · cases h5
      · exact hpj j (p_mem_Xh D h5) (h3 ▸ prep_mem_fl he hu)
    · refine ⟨v, ?_, ?_⟩
      · rcases h3 with h3 | h3
        · exact Or.inl (Prod.ext h3 h4)
        · exact Or.inr (Prod.ext h3 h4)
      · rw [h4] at h2
        rcases neg_Ch D h2 with h5 | h5 | ⟨_, _, h5⟩ | h5
        · cases h5
        · cases h5
        · cases h5
        · exact h5
  | CA =>
    rw [hs] at hpiv
    exact absurd (pos_CA D hpiv) (hA e he)
  | G => exact absurd hs hG
  | z d =>
    rw [hs] at hsm
    have hdh : d ∈ D.heads := by simpa [ConstrData.srcs] using hsm
    exact absurd (hs ▸ side_mem_fl he) (hz d hdh)
  | p j =>
    rw [hs] at hsm
    have hj : j ∈ D.ballast := by simpa [ConstrData.srcs] using hsm
    exact absurd (hs ▸ side_mem_fl he) (hpj j hj)
  | P v =>
    rw [hs] at hpiv
    simp only [ConstrData.inv, Finset.mem_singleton, Prod.mk.injEq, and_true] at hpiv
    exact Or.inr ⟨v, Or.inl hs, hnoprep v (Or.inl hs), hpiv⟩
  | Q v =>
    rw [hs] at hpiv
    simp only [ConstrData.inv, Finset.mem_singleton, Prod.mk.injEq, and_true] at hpiv
    exact Or.inr ⟨v, Or.inr hs, hnoprep v (Or.inr hs), hpiv⟩

theorem dep_order (h : CombOK D (p ++ t)) (hA : ∀ e ∈ p, e.pivot ≠ CVar.A)
    (p₁ p₂ p₃ : List (Ev D)) (e₁ e₂ : Ev D) (hh d : Head D.TV)
    (hp : p = p₁ ++ e₁ :: (p₂ ++ e₂ :: p₃)) (h1 : e₁.pivot = CVar.hd d)
    (h2 : e₂.pivot = CVar.hd hh) : d ∉ D.deps hh := by
  intro hd
  have he₂ : e₂ ∈ p := by simp [hp]
  have he₁ : e₁ ∈ p := by simp [hp]
  rcases evForm h hA he₂ with ⟨h', _, hs, hpv, hu⟩ | ⟨v, _, _, hpv⟩
  swap
  · rw [h2] at hpv; cases hpv
  rw [h2] at hpv
  cases hpv
  have hmem : (CVar.hd d, false) ∈ sideLabel D.inv e₂ e₂.prep.length := by
    rw [mem_sideLabel_full, hs]
    refine ⟨by simp [ConstrData.inv, ConstrData.Ch, hd], fun u hu' heq => ?_⟩
    obtain ⟨v, hv | hv, _⟩ := hu u hu' <;> rw [hv] at heq <;> simp at heq
  have hdec : p ++ t = (p₁ ++ e₁ :: p₂) ++ e₂ :: (p₃ ++ t) := by simp [hp]
  by_cases hall : ∀ e' ∈ p₃ ++ t, (CVar.hd d, false) ≠ (e'.pivot, false)
  · have := (mem_goalLabel D.inv Src.G (p ++ t) _).2
      (Or.inr ⟨_, e₂, _, hdec, Finset.mem_erase.2 ⟨by simp, hmem⟩, hall⟩)
    rw [h.2.2.2.2.2.1] at this; simp at this
  · push Not at hall
    obtain ⟨e', he', hxe⟩ := hall
    have he'm : e' ∈ p ++ t := by rw [hdec]; simp [he']
    have hs' := ok_pivot h he'm
    simp only [Prod.mk.injEq] at hxe
    rw [← hxe.1] at hs'
    have hs1 := ok_pivot h (List.mem_append_left t he₁)
    rw [h1] at hs1
    have hnd := List.Nodup.sublist (map_side_sublist _) (ok_fl h).2
    rw [hdec] at hnd
    simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append] at hnd
    have hnd2 := (List.nodup_append.1 hnd).2.1
    rw [List.nodup_cons] at hnd2
    apply hnd2.1
    rw [pos_hd D hs1, ← pos_hd D hs']
    refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
    rw [← List.map_append]
    exact List.mem_map_of_mem he'

end ReconfRes.Frozen.Dev.Q427d.PartC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-- A valid comb's events before `A` have the shape. -/
theorem shape_of_ok (hD : D.Valid) {p t : List (Ev D)} (h : CombOK D (p ++ t))
    (hA : ∀ e ∈ p, e.pivot ≠ CVar.A) : Shape D p := by
  refine ⟨fun e he => evForm h hA he, ?_,
    fun p₁ p₂ p₃ e₁ e₂ hh d hp h1 h2 => dep_order h hA p₁ p₂ p₃ e₁ e₂ hh d hp h1 h2⟩
  have hfl := (ok_fl h).2
  rw [fl_append] at hfl
  exact hfl.sublist ((map_side_sublist p).trans (List.sublist_append_left _ _))

end ReconfRes.Frozen.Dev.Q427d.PartC2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias shape_of_ok := ReconfRes.Frozen.Dev.Q427d.PartC2.shape_of_ok

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
theorem mem_bag_snoc (p : List (Ev D)) (e : Ev D) (v : D.TV) :
    v ∈ bag D (p ++ [e]) ↔
      (CVar.f v, false) ∈ sideLabel D.inv e e.prep.length ∨
      (v ∈ bag D p ∧ e.pivot ≠ CVar.f v) := by
  simp only [bag, Finset.mem_filter, Finset.mem_univ, true_and, goal, goalLabel_snoc, stepG,
    Finset.mem_union, Finset.mem_erase, ne_eq, Prod.mk.injEq]
  constructor
  · rintro (⟨-, h⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h2, fun h => h1 ⟨h.symm, trivial⟩⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl ⟨by simp, h⟩
    · exact Or.inr ⟨fun h => h2 h.1.symm, h1⟩

end ReconfRes.Frozen.Dev.Q427d.PartC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias mem_bag_snoc := ReconfRes.Frozen.Dev.Q427d.PartC1.mem_bag_snoc

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
theorem mem_bag (p : List (Ev D)) (v : D.TV) :
    v ∈ bag D p ↔ ∃ p₁ e t, p = p₁ ++ e :: t ∧
      (CVar.f v, false) ∈ sideLabel D.inv e e.prep.length ∧ ∀ e' ∈ t, e'.pivot ≠ CVar.f v := by
  have hG : (CVar.f v, false) ∉ D.inv Src.G := by simp [ConstrData.inv, ConstrData.Gc]
  simp only [bag, Finset.mem_filter, Finset.mem_univ, true_and, goal]
  rw [Q427d.mem_goalLabel]
  constructor
  · rintro (⟨h1, -⟩ | ⟨p₁, e, t, rfl, h2, h3⟩)
    · exact absurd h1 hG
    · refine ⟨p₁, e, t, rfl, (Finset.mem_erase.1 h2).2, fun e' he' h => h3 e' he' ?_⟩
      rw [h]
  · rintro ⟨p₁, e, t, rfl, h2, h3⟩
    refine Or.inr ⟨p₁, e, t, rfl, Finset.mem_erase.2 ⟨by simp, h2⟩, fun e' he' h => ?_⟩
    simp only [Prod.mk.injEq, and_true] at h
    exact h3 e' he' h.symm

/-! ### Literal by literal -/
theorem hdf_goal (hD : D.Valid) {p : List (Ev D)} (hs : Shape D p) (d : Head D.TV) :
    (CVar.hd d, false) ∈ goal D p ↔ d ∈ D.heads ∧ d ∉ expd D p := by
  rw [goal, Q427d.mem_goalLabel]
  constructor
  · rintro (⟨hG, hall⟩ | ⟨p₁, e, t, rfl, hm, hall⟩)
    · have hd : d ∈ D.heads := by simpa [ConstrData.inv, ConstrData.Gc] using hG
      refine ⟨hd, fun hx => ?_⟩
      obtain ⟨-, e, he, hpv⟩ := (mem_expd D).1 hx
      exact hall e he (by rw [hpv])
    · obtain ⟨h', hh', -, hpv, hmC, -, -⟩ := (side_iff D (hs.1 e (by simp)) _).1 hm
      have hdep : d ∈ D.deps h' := (hdf_mem_Ch D).1 hmC
      refine ⟨deps_sub D hdep, fun hx => ?_⟩
      obtain ⟨-, e₀, he₀, hpv₀⟩ := (mem_expd D).1 hx
      rcases List.mem_append.1 he₀ with he₀ | he₀
      · obtain ⟨a, b, rfl⟩ := List.append_of_mem he₀
        exact hs.2.2 a b t e₀ e h' d (by simp) hpv₀ hpv hdep
      · rcases List.mem_cons.1 he₀ with rfl | he₀
        · rw [hpv, CVar.hd.injEq] at hpv₀
          subst hpv₀
          exact not_self_dep D hD hdep
        · exact hall e₀ he₀ (by rw [hpv₀])
  · rintro ⟨hd, hne⟩
    refine Or.inl ⟨by simp [ConstrData.inv, ConstrData.Gc, hd], fun e he h => hne ?_⟩
    simp only [Prod.mk.injEq, and_true] at h
    exact (mem_expd D).2 ⟨hd, e, he, h.symm⟩

theorem nf_of_kind {p : List (Ev D)} (hs : Shape D p) {x : CVar D.TV} (b : Bool)
    (hx : (∀ h, x ≠ CVar.hd h) ∧ ∀ v, x ≠ CVar.f v) : ∀ e ∈ p, (x, b) ≠ (e.pivot, false) := by
  intro e he h
  simp only [Prod.mk.injEq] at h
  rcases evform_piv D (hs.1 e he) with ⟨h', hp⟩ | ⟨v, hp⟩
  · exact hx.1 h' (h.1.trans hp)
  · exact hx.2 v (h.1.trans hp)

theorem zf_goal {p : List (Ev D)} (hs : Shape D p) (d : Head D.TV) :
    (CVar.z d, false) ∈ goal D p ↔ d ∈ expd D p := by
  rw [mem_goal_nf D _ (nf_of_kind D hs _ ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩),
    mem_expd]
  have hG : (CVar.z d, false) ∉ D.Gc := by simp [ConstrData.Gc]
  simp only [hG, false_or]
  constructor
  · rintro ⟨e, he, hm⟩
    obtain ⟨h', hh', -, hpv, hmC, -, -⟩ := (side_iff D (hs.1 e he) _).1 hm
    rw [zf_mem_Ch] at hmC
    subst hmC
    exact ⟨hh', e, he, hpv⟩
  · rintro ⟨hd, e, he, hpv⟩
    refine ⟨e, he, ?_⟩
    rcases hs.1 e he with ⟨h, hh, hsd, hp, -⟩ | ⟨v, -, -, hp⟩
    · rw [hpv, CVar.hd.injEq] at hp
      subst hp
      refine (side_iff D (hs.1 e he) _).2 ⟨d, hh, hsd, hpv, (zf_mem_Ch D).2 rfl, by simp, ?_⟩
      intro u hu h
      obtain ⟨v, hv⟩ := evform_prep D (hs.1 e he) u hu
      rw [hv] at h; cases h
    · rw [hpv] at hp; cases hp

theorem pf_goal {p : List (Ev D)} (hs : Shape D p) (j : ℕ) :
    (CVar.p j, false) ∈ goal D p ↔ Head.U ∈ expd D p ∧ j ∈ D.ballast := by
  rw [mem_goal_nf D _ (nf_of_kind D hs _ ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩),
    mem_expd]
  have hG : (CVar.p j, false) ∉ D.Gc := by simp [ConstrData.Gc]
  simp only [hG, false_or]
  constructor
  · rintro ⟨e, he, hm⟩
    obtain ⟨h', hh', -, hpv, hmC, -, -⟩ := (side_iff D (hs.1 e he) _).1 hm
    rw [pf_mem_Ch] at hmC
    obtain ⟨rfl, hj⟩ := hmC
    exact ⟨⟨hh', e, he, hpv⟩, hj⟩
  · rintro ⟨⟨hd, e, he, hpv⟩, hj⟩
    refine ⟨e, he, ?_⟩
    rcases hs.1 e he with ⟨h, hh, hsd, hp, -⟩ | ⟨v, -, -, hp⟩
    · rw [hpv, CVar.hd.injEq] at hp
      subst hp
      refine (side_iff D (hs.1 e he) _).2 ⟨Head.U, hh, hsd, hpv, (pf_mem_Ch D).2 ⟨rfl, hj⟩,
        by simp, ?_⟩
      intro u hu h
      obtain ⟨v, hv⟩ := evform_prep D (hs.1 e he) u hu
      rw [hv] at h; cases h
    · rw [hpv] at hp; cases hp

theorem Af_goal {p : List (Ev D)} (hs : Shape D p) : (CVar.A, false) ∈ goal D p := by
  rw [mem_goal_nf D _ (nf_of_kind D hs _ ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩)]
  exact Or.inl (by simp [ConstrData.Gc])

theorem pos_goal {p : List (Ev D)} (hs : Shape D p) (x : CVar D.TV) : (x, true) ∉ goal D p := by
  have hl : ∀ e ∈ p, (x, true) ≠ (e.pivot, false) := fun e _ h => by
    simp only [Prod.mk.injEq] at h; exact absurd h.2 (by decide)
  rw [mem_goal_nf D _ hl]
  rintro (h | ⟨e, he, hm⟩)
  · simp [ConstrData.Gc] at h
  · obtain ⟨h', -, -, -, hmC, hne, -⟩ := (side_iff D (hs.1 e he) _).1 hm
    rw [pos_mem_Ch] at hmC
    exact hne (by rw [hmC])

/-! ### Targets: the goal formula and its size -/
theorem goal_formula_shape (hD : D.Valid) {p : List (Ev D)} (h : Shape D p) :
    goal D p = headPart D (expd D p) ∪ (bag D p).image (fun v => (CVar.f v, false)) := by
  ext ⟨x, b⟩
  cases b with
  | true =>
    simp only [pos_goal D h x, false_iff, headPart, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Prod.mk.injEq]
    split_ifs <;> simp
  | false =>
    cases x with
    | hd d =>
      rw [hdf_goal D hD h]
      simp only [headPart, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Prod.mk.injEq, Finset.mem_sdiff]
      split_ifs <;> simp
    | A =>
      simp [Af_goal D h, headPart]
    | z d =>
      rw [zf_goal D h]
      simp only [headPart, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Prod.mk.injEq]
      split_ifs <;> simp
    | f v =>
      have : (CVar.f v, false) ∈ goal D p ↔ v ∈ bag D p := by simp [bag]
      rw [this]
      simp only [headPart, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Prod.mk.injEq]
      split_ifs <;> simp
    | p j =>
      rw [pf_goal D h]
      simp only [headPart, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Prod.mk.injEq]
      split_ifs with hU <;> simp [hU]

end ReconfRes.Frozen.Dev.Q427d.PartC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias goal_formula_shape := ReconfRes.Frozen.Dev.Q427d.PartC1.goal_formula_shape

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartC1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Counting (copied from Q427b.PartN) -/
theorem internal_len {τ : Type} (t : FBTree τ) :
    t.internalPaths.length + 1 = t.leaves.length := by
  induction t with
  | leaf v => simp [FBTree.internalPaths, FBTree.leaves]
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths, FBTree.leaves, List.length_cons, List.length_append,
      List.length_map]
    omega

theorem internal_nodup {τ : Type} (t : FBTree τ) : t.internalPaths.Nodup := by
  induction t with
  | leaf v => simp [FBTree.internalPaths]
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths]
    refine List.nodup_cons.2 ⟨by simp, ?_⟩
    refine List.Nodup.append (ihl.map (fun _ _ h => List.cons_injective h))
      (ihr.map (fun _ _ h => List.cons_injective h)) ?_
    intro x hx hy
    simp only [List.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, hb⟩ := hy
    simp at hb

theorem filt_card {τ : Type} (t : FBTree τ) (h : 2 ≤ t.leaves.length) :
    ((t.internalPaths.filter fun p => p ≠ []).toFinset).card + 2 = t.leaves.length := by
  rw [List.toFinset_card_of_nodup ((internal_nodup t).filter _)]
  cases t with
  | leaf v => simp [FBTree.leaves] at h
  | node l r =>
    have hl := internal_len l
    have hr := internal_len r
    have : ((FBTree.node l r).internalPaths.filter fun p => p ≠ []) =
        l.internalPaths.map (false :: ·) ++ r.internalPaths.map (true :: ·) := by
      simp only [FBTree.internalPaths]
      rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2]
      intro a ha
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ <;> simp
    rw [this]
    simp only [FBTree.leaves, List.length_append, List.length_map]
    omega

theorem leaves_len {τ : Type} [Fintype τ] [DecidableEq τ] (t : FBTree τ)
    (h : t.LeavesExactly) : t.leaves.length = Fintype.card τ := by
  rw [← List.toFinset_card_of_nodup h.1]
  have : t.leaves.toFinset = Finset.univ := by ext x; simp [h.2 x]
  rw [this, Finset.card_univ]

theorem card_TV (D : ConstrData) : Fintype.card D.TV = D.m := by
  simp [ConstrData.m, ConstrData.TV, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

theorem m_ge (D : ConstrData) (hD : D.Valid) : 2 ≤ D.m := by
  have := hD.1
  unfold ConstrData.m
  have : 1 ≤ D.b := by simp only [ConstrData.b]; omega
  nlinarith

theorem inner1_card (D : ConstrData) (hD : D.Valid) : D.inner1.card + 2 = D.m := by
  unfold ConstrData.inner1
  rw [Finset.card_image_of_injective _ (fun _ _ h => Head.i1.inj h)]
  have hl := leaves_len D.t1 hD.2.2.2.2.1
  rw [card_TV] at hl
  have := filt_card D.t1 (by rw [hl]; exact m_ge D hD)
  omega

theorem inner2_card (D : ConstrData) (hD : D.Valid) : D.inner2.card + 2 = D.m := by
  unfold ConstrData.inner2
  rw [Finset.card_image_of_injective _ (fun _ _ h => Head.i2.inj h)]
  have hl := leaves_len D.t2 hD.2.2.2.2.2
  rw [card_TV] at hl
  have := filt_card D.t2 (by rw [hl]; exact m_ge D hD)
  omega

theorem heads_card (D : ConstrData) (hD : D.Valid) : D.heads.card + 2 = 4 * D.m := by
  have h1 := inner1_card D hD
  have h2 := inner2_card D hD
  have ha : (Finset.univ.image (Head.a (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Head.a.inj h), Finset.card_univ, card_TV]
  have hb : (Finset.univ.image (Head.b (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Head.b.inj h), Finset.card_univ, card_TV]
  have hTU : ({Head.T, Head.U} : Finset (Head D.TV)).card = 2 := by simp
  unfold ConstrData.heads
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint]
  · omega
  all_goals
    refine Finset.disjoint_left.2 fun x hx hy => ?_
    simp only [ConstrData.inner1, ConstrData.inner2, Finset.mem_image, Finset.mem_univ,
      true_and] at hy
    obtain ⟨p, -, rfl⟩ := hy
    simp [ConstrData.inner1] at hx

theorem expd_sub (p : List (Ev D)) : expd D p ⊆ D.heads := Finset.filter_subset _ _

theorem card_goal_shape (hD : D.Valid) {p : List (Ev D)} (h : Shape D p) :
    (goal D p).card = D.β + (if Head.U ∈ expd D p then D.r else 0) + (bag D p).card := by
  rw [goal_formula_shape D hD h]
  set E := expd D p with hE
  have hsub : E ⊆ D.heads := expd_sub D p
  have hH := heads_card D hD
  have hsd := Finset.card_sdiff_add_card_eq_card hsub
  have hbal : D.ballast.card = D.r := by simp [ConstrData.ballast]
  have c1 : ((D.heads \ E).image (fun h => ((CVar.hd h, false) : Literal (CVar D.TV)))).card = (D.heads \ E).card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have c2 : (E.image (fun h => ((CVar.z h, false) : Literal (CVar D.TV)))).card = E.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have c3 : (D.ballast.image (fun j => ((CVar.p j, false) : Literal (CVar D.TV)))).card = D.ballast.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have c4 : ((bag D p).image (fun v => ((CVar.f v, false) : Literal (CVar D.TV)))).card = (bag D p).card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  unfold headPart
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint, c1, c2, Finset.card_singleton]
  · have hβ : D.β = 4 * D.m - 1 := rfl
    split_ifs
    · rw [c3, hbal]; omega
    · simp only [Finset.card_empty]; omega
  all_goals
    refine Finset.disjoint_left.2 fun x hx hy => ?_
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hx hy
    (try split_ifs at hx hy) <;>
    (try simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.notMem_empty] at hx hy) <;>
    aesop

end ReconfRes.Frozen.Dev.Q427d.PartC1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias card_goal_shape := ReconfRes.Frozen.Dev.Q427d.PartC1.card_goal_shape

alias mem_bag := ReconfRes.Frozen.Dev.Q427d.PartC1.mem_bag

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartK1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Counting (copied from `Q427b.PartN`) -/
theorem internal_len {τ : Type} (t : FBTree τ) :
    t.internalPaths.length + 1 = t.leaves.length := by
  induction t with
  | leaf v => simp [FBTree.internalPaths, FBTree.leaves]
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths, FBTree.leaves, List.length_cons, List.length_append,
      List.length_map]
    omega

theorem internal_nodup {τ : Type} (t : FBTree τ) : t.internalPaths.Nodup := by
  induction t with
  | leaf v => simp [FBTree.internalPaths]
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths]
    refine List.nodup_cons.2 ⟨by simp, ?_⟩
    refine List.Nodup.append (ihl.map (fun _ _ h => List.cons_injective h))
      (ihr.map (fun _ _ h => List.cons_injective h)) ?_
    intro x hx hy
    simp only [List.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, hb⟩ := hy
    simp at hb

theorem filt_card {τ : Type} (t : FBTree τ) (h : 2 ≤ t.leaves.length) :
    ((t.internalPaths.filter fun p => p ≠ []).toFinset).card + 2 = t.leaves.length := by
  rw [List.toFinset_card_of_nodup ((internal_nodup t).filter _)]
  cases t with
  | leaf v => simp [FBTree.leaves] at h
  | node l r =>
    have hl := internal_len l
    have hr := internal_len r
    have : ((FBTree.node l r).internalPaths.filter fun p => p ≠ []) =
        l.internalPaths.map (false :: ·) ++ r.internalPaths.map (true :: ·) := by
      simp only [FBTree.internalPaths]
      rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2]
      intro a ha
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ <;> simp
    rw [this]
    simp only [FBTree.leaves, List.length_append, List.length_map]
    omega

theorem leaves_len {τ : Type} [Fintype τ] [DecidableEq τ] (t : FBTree τ)
    (h : t.LeavesExactly) : t.leaves.length = Fintype.card τ := by
  rw [← List.toFinset_card_of_nodup h.1]
  have : t.leaves.toFinset = Finset.univ := by ext x; simp [h.2 x]
  rw [this, Finset.card_univ]

theorem card_TV : Fintype.card D.TV = D.m := by
  simp [ConstrData.m, ConstrData.TV, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

theorem m_ge (hD : D.Valid) : 16 ≤ D.m := by
  have := hD.1
  have := hD.2.2.2.1
  unfold ConstrData.m
  have : 8 ≤ D.b := by simp only [ConstrData.b]; omega
  nlinarith

theorem inner1_card (hD : D.Valid) : D.inner1.card + 2 = D.m := by
  unfold ConstrData.inner1
  rw [Finset.card_image_of_injective _ (fun _ _ h => Head.i1.inj h)]
  have hl := leaves_len D.t1 hD.2.2.2.2.1
  rw [card_TV] at hl
  have := filt_card D.t1 (by rw [hl]; have := m_ge D hD; omega)
  omega

theorem inner2_card (hD : D.Valid) : D.inner2.card + 2 = D.m := by
  unfold ConstrData.inner2
  rw [Finset.card_image_of_injective _ (fun _ _ h => Head.i2.inj h)]
  have hl := leaves_len D.t2 hD.2.2.2.2.2
  rw [card_TV] at hl
  have := filt_card D.t2 (by rw [hl]; have := m_ge D hD; omega)
  omega

theorem heads_card (hD : D.Valid) : D.heads.card + 2 = 4 * D.m := by
  have h1 := inner1_card D hD
  have h2 := inner2_card D hD
  have ha : (Finset.univ.image (Head.a (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Head.a.inj h), Finset.card_univ, card_TV]
  have hb : (Finset.univ.image (Head.b (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Head.b.inj h), Finset.card_univ, card_TV]
  have hTU : ({Head.T, Head.U} : Finset (Head D.TV)).card = 2 := by simp
  unfold ConstrData.heads
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint]
  · omega
  all_goals
    refine Finset.disjoint_left.2 fun x hx hy => ?_
    simp only [ConstrData.inner1, ConstrData.inner2, Finset.mem_image, Finset.mem_univ,
      true_and] at hy
    obtain ⟨p, -, rfl⟩ := hy
    simp [ConstrData.inner1] at hx

theorem srcs_card (hD : D.Valid) : D.srcs.card = D.α := by
  have hh := heads_card D hD
  have hm := m_ge D hD
  have hC : (D.heads.image (Src.C (τ := D.TV))).card = D.heads.card :=
    Finset.card_image_of_injective _ (fun _ _ h => Src.C.inj h)
  have hz : (D.heads.image (Src.z (τ := D.TV))).card = D.heads.card :=
    Finset.card_image_of_injective _ (fun _ _ h => Src.z.inj h)
  have hp : (D.ballast.image (Src.p (τ := D.TV))).card = D.r := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Src.p.inj h)]
    simp [ConstrData.ballast]
  have hP : (Finset.univ.image (Src.P (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Src.P.inj h), Finset.card_univ, card_TV]
  have hQ : (Finset.univ.image (Src.Q (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Src.Q.inj h), Finset.card_univ, card_TV]
  have h2 : ({Src.CA, Src.G} : Finset (Src D.TV)).card = 2 := by simp
  unfold ConstrData.srcs ConstrData.α
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · omega
  all_goals
    refine Finset.disjoint_left.2 fun x hx hy => ?_
    first
    | (simp only [Finset.mem_insert, Finset.mem_singleton] at hy
       rcases hy with rfl | rfl <;> simp at hx)
    | (simp only [Finset.mem_image] at hy
       obtain ⟨p, -, rfl⟩ := hy
       simp at hx)

theorem ballast_card : D.ballast.card = D.r := by simp [ConstrData.ballast]

theorem r_le_q : D.r ≤ D.q := by unfold ConstrData.r; omega

theorem W_eq (hD : D.Valid) : D.W = 4 * D.m + D.q := by
  have := m_ge D hD
  unfold ConstrData.W ConstrData.β; omega

/-! ### Widths of the sources -/
theorem deps_card (h : Head D.TV) : (D.deps h).card ≤ D.m + 3 := by
  cases h with
  | T => exact (Finset.card_le_three).trans (by omega)
  | U => exact (Finset.card_le_two).trans (by omega)
  | i1 p => exact (Finset.card_le_two).trans (by omega)
  | i2 p => exact (Finset.card_le_two).trans (by omega)
  | b v => simp [ConstrData.deps]
  | a v =>
    simp only [ConstrData.deps]
    refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
    rw [Finset.card_univ, card_TV]; omega

theorem Xh_card (h : Head D.TV) : (D.Xh h).card ≤ D.m + D.r + 1 := by
  cases h with
  | T =>
    simp only [ConstrData.Xh]
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, card_TV]; omega
  | U =>
    simp only [ConstrData.Xh]
    refine Finset.card_image_le.trans ?_
    rw [ballast_card]; omega
  | a v => simp [ConstrData.Xh]
  | b v => simp [ConstrData.Xh]
  | i1 p => simp [ConstrData.Xh]
  | i2 p => simp [ConstrData.Xh]

theorem Ch_card (h : Head D.TV) : (D.Ch h).card ≤ 2 * D.m + D.r + 7 := by
  unfold ConstrData.Ch
  have h1 := deps_card D h
  have h2 := Xh_card D h
  have h3 : ({(CVar.hd h, true), (CVar.A, false), (CVar.z h, false)} :
      Finset (Literal (CVar D.TV))).card ≤ 3 := Finset.card_le_three
  have h4 := Finset.card_union_le
    ({(CVar.hd h, true), (CVar.A, false), (CVar.z h, false)} : Finset (Literal (CVar D.TV)))
    ((D.deps h).image (fun d => (CVar.hd d, false)))
  have h5 := Finset.card_union_le
    (({(CVar.hd h, true), (CVar.A, false), (CVar.z h, false)} : Finset (Literal (CVar D.TV))) ∪
      (D.deps h).image (fun d => (CVar.hd d, false)))
    ((D.Xh h).image (fun x => (x, false)))
  have h6 := Finset.card_image_le (s := D.deps h) (f := fun d => (CVar.hd d, false))
  have h7 := Finset.card_image_le (s := D.Xh h) (f := fun x => (x, false))
  omega

theorem srcs_width (hD : D.Valid) : ∀ x ∈ D.srcs, (D.inv x).card ≤ D.W := by
  intro x _
  rw [W_eq D hD]
  have hm := m_ge D hD
  have hr := r_le_q D
  have hh := heads_card D hD
  cases x with
  | C h => have := Ch_card D h; simp only [ConstrData.inv]; omega
  | CA =>
    simp only [ConstrData.inv, ConstrData.CA]
    have h1 := Finset.card_union_le ({(CVar.A, true)} : Finset (Literal (CVar D.TV)))
      (D.heads.image (fun h => (CVar.z h, false)))
    have h2 := Finset.card_union_le (({(CVar.A, true)} : Finset (Literal (CVar D.TV))) ∪
      D.heads.image (fun h => (CVar.z h, false))) (D.ballast.image (fun j => (CVar.p j, false)))
    have h3 := Finset.card_image_le (s := D.heads) (f := fun h => (CVar.z h, false))
    have h4 := Finset.card_image_le (s := D.ballast) (f := fun j => ((CVar.p j : CVar D.TV), false))
    rw [ballast_card] at h4
    simp only [Finset.card_singleton] at h1
    omega
  | G =>
    simp only [ConstrData.inv, ConstrData.Gc]
    have h1 := Finset.card_union_le ({(CVar.A, false)} : Finset (Literal (CVar D.TV)))
      (D.heads.image (fun h => (CVar.hd h, false)))
    have h3 := Finset.card_image_le (s := D.heads) (f := fun h => (CVar.hd h, false))
    simp only [Finset.card_singleton] at h1
    omega
  | z h => simp [ConstrData.inv]; omega
  | p j => simp [ConstrData.inv]; omega
  | P v => simp [ConstrData.inv]; omega
  | Q v => simp [ConstrData.inv]; omega

end ReconfRes.Frozen.Dev.Q427d.PartK1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ## Part K: canonical lists are valid -/

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartK2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Side clauses and bag steps -/
theorem mem_foldl_erase {V : Type} [DecidableEq V] {ι : Type} (x : Literal V)
    (us : List (ι × V)) (c : Clause V) :
    x ∈ us.foldl (fun c u => c.erase (u.2, false)) c ↔ x ∈ c ∧ ∀ u ∈ us, x ≠ (u.2, false) := by
  induction us generalizing c with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, ih, Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

theorem f_mem_Ch (h : Head D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ D.Ch h ↔ CVar.f v ∈ D.Xh h := by
  simp [ConstrData.Ch]

theorem side_evH (h : Head D.TV) :
    sideLabel D.inv (evH D h) (evH D h).prep.length = D.Ch h := by
  simp [sideLabel, evH, ConstrData.inv]

theorem side_evQ (w : D.TV) :
    sideLabel D.inv (evQ D w) (evQ D w).prep.length = {(CVar.f w, true)} := by
  simp [sideLabel, evQ, ConstrData.inv]

theorem f_mem_side_evT (l : List D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ sideLabel D.inv (evT D l) (evT D l).prep.length ↔ v ∉ l := by
  simp only [sideLabel, evT, List.take_length]
  rw [mem_foldl_erase]
  have h1 : (CVar.f v, false) ∈ D.inv (Src.C Head.T) := by
    simp [ConstrData.inv, f_mem_Ch, ConstrData.Xh]
  constructor
  · rintro ⟨_, h⟩ hv
    exact h _ (List.mem_map_of_mem hv) rfl
  · intro hv
    refine ⟨h1, fun u hu he => ?_⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    simp only [Prod.mk.injEq, CVar.f.injEq, and_true] at he
    exact hv (he ▸ hw)

theorem f_mem_side_evBP (w v : D.TV) :
    (CVar.f v, false) ∉ sideLabel D.inv (evBP D w) (evBP D w).prep.length := by
  simp only [sideLabel, evBP, List.take_length]
  rw [mem_foldl_erase]
  simp [ConstrData.inv, f_mem_Ch, ConstrData.Xh]

theorem bag_nil : bag D [] = ∅ := by
  ext v
  rw [mem_bag]
  simp

theorem bag_evT (p : List (Ev D)) (l : List D.TV) (v : D.TV) :
    v ∈ bag D (p ++ [evT D l]) ↔ v ∉ l ∨ v ∈ bag D p := by
  rw [mem_bag_snoc, f_mem_side_evT]
  simp [evT]

theorem bag_evH (p : List (Ev D)) (h : Head D.TV) (v : D.TV) :
    v ∈ bag D (p ++ [evH D h]) ↔ CVar.f v ∈ D.Xh h ∨ v ∈ bag D p := by
  rw [mem_bag_snoc, side_evH, f_mem_Ch]
  simp [evH]

theorem bag_evQ (p : List (Ev D)) (w v : D.TV) :
    v ∈ bag D (p ++ [evQ D w]) ↔ v ∈ bag D p ∧ v ≠ w := by
  rw [mem_bag_snoc, side_evQ]
  simp [evQ, eq_comm]

/-! ### Walks: pivots and bag sizes along a segment -/
/-- Along `seg` (after `pre`): each fact pivot is active, and each bag has at most `k` facts. -/
def Walk (pre seg : List (Ev D)) (k : ℕ) : Prop :=
  ∀ p e t, seg = p ++ e :: t →
    (∀ v, e.pivot = CVar.f v → v ∈ bag D (pre ++ p)) ∧ (bag D (pre ++ p ++ [e])).card ≤ k

theorem walk_nil (pre : List (Ev D)) (k : ℕ) : Walk D pre [] k := by
  intro p e t h
  exact absurd h.symm (by simp)

theorem walk_cons {pre : List (Ev D)} {e : Ev D} {L : List (Ev D)} {k : ℕ}
    (h1 : ∀ v, e.pivot = CVar.f v → v ∈ bag D pre) (h2 : (bag D (pre ++ [e])).card ≤ k)
    (h3 : Walk D (pre ++ [e]) L k) : Walk D pre (e :: L) k := by
  intro p e' t h
  cases p with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simpa using h1, by simpa using h2⟩
  | cons x p =>
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := h3 p e' t h
    simpa [List.append_assoc] using this

theorem walk_cons_inv {pre : List (Ev D)} {e : Ev D} {L : List (Ev D)} {k : ℕ}
    (h : Walk D pre (e :: L) k) : Walk D (pre ++ [e]) L k := by
  intro p e' t hL
  have := h (e :: p) e' t (by simp [hL])
  simpa [List.append_assoc] using this

theorem walk_append {pre L1 L2 : List (Ev D)} {k : ℕ} (h1 : Walk D pre L1 k)
    (h2 : Walk D (pre ++ L1) L2 k) : Walk D pre (L1 ++ L2) k := by
  induction L1 generalizing pre with
  | nil => simpa using h2
  | cons x L1 ih =>
    have hx := h1 [] x L1 rfl
    simp only [List.append_nil] at hx
    refine walk_cons D hx.1 hx.2 (ih (walk_cons_inv D h1) ?_)
    simpa [List.append_assoc] using h2

/-- An event that neither adds nor removes facts. -/
def Neutral (e : Ev D) : Prop :=
  (∀ v, (CVar.f v, false) ∉ sideLabel D.inv e e.prep.length) ∧ ∀ v, e.pivot ≠ CVar.f v

theorem bag_neutral {e : Ev D} (he : Neutral D e) (p : List (Ev D)) :
    bag D (p ++ [e]) = bag D p := by
  ext v
  rw [mem_bag_snoc]
  simp [he.1 v, he.2 v]

theorem walk_neutral {L : List (Ev D)} (hL : ∀ e ∈ L, Neutral D e) {pre : List (Ev D)} {k : ℕ}
    (hk : (bag D pre).card ≤ k) : Walk D pre L k ∧ bag D (pre ++ L) = bag D pre := by
  induction L generalizing pre with
  | nil => exact ⟨walk_nil D pre k, by simp⟩
  | cons x L ih =>
    have hx := hL x (by simp)
    have hb := bag_neutral D hx pre
    obtain ⟨hw, he⟩ := ih (fun e he => hL e (by simp [he])) (pre := pre ++ [x]) (by rw [hb]; exact hk)
    refine ⟨walk_cons D (fun v hv => absurd hv (hx.2 v)) (by rw [hb]; exact hk) hw, ?_⟩
    rw [← hb, ← he, List.append_assoc, List.singleton_append]

theorem neutral_evH {h : Head D.TV} (hh : ∀ v, CVar.f v ∉ D.Xh h) : Neutral D (evH D h) := by
  refine ⟨fun v => ?_, fun v => by simp [evH]⟩
  rw [side_evH, f_mem_Ch]
  exact hh v

theorem neutral_evBP (w : D.TV) : Neutral D (evBP D w) :=
  ⟨fun v => f_mem_side_evBP D w v, fun v => by simp [evBP]⟩

/-! ### Segment walks -/
theorem unselSeg_cons (v : D.TV) (l : List D.TV) :
    unselSeg D (v :: l) = [evH D (Head.a v), evQ D v] ++ unselSeg D l := by
  simp [unselSeg]

theorem selSeg_cons (v : D.TV) (l : List D.TV) :
    selSeg D (v :: l) = [evH D (Head.a v), evH D (Head.b v), evQ D v] ++ selSeg D l := by
  simp [selSeg]

theorem Xh_a (v : D.TV) : D.Xh (Head.a v) = {CVar.f v} := rfl

theorem Xh_b (v : D.TV) : D.Xh (Head.b v) = {CVar.f v} := rfl

theorem walk_unsel (lu : List D.TV) (hnd : lu.Nodup) (B : Finset D.TV) (hB : ∀ v ∈ lu, v ∉ B)
    {k : ℕ} (hk : (B ∪ lu.toFinset).card ≤ k) (pre : List (Ev D))
    (hbag : bag D pre = B ∪ lu.toFinset) :
    Walk D pre (unselSeg D lu) k ∧ bag D (pre ++ unselSeg D lu) = B := by
  induction lu generalizing pre with
  | nil => exact ⟨walk_nil D pre k, by simpa [unselSeg] using hbag⟩
  | cons v lu ih =>
    rw [List.nodup_cons] at hnd
    have hvB : v ∉ B := hB v (by simp)
    have h1 : bag D (pre ++ [evH D (Head.a v)]) = bag D pre := by
      ext x
      rw [bag_evH, Xh_a, hbag]
      simp only [Finset.mem_singleton, CVar.f.injEq, Finset.mem_union, List.mem_toFinset,
        List.mem_cons]
      constructor
      · rintro (rfl | h) <;> tauto
      · tauto
    have h2 : bag D (pre ++ [evH D (Head.a v), evQ D v]) = B ∪ lu.toFinset := by
      ext x
      have : pre ++ [evH D (Head.a v), evQ D v] = (pre ++ [evH D (Head.a v)]) ++ [evQ D v] := by
        simp
      rw [this, bag_evQ, h1, hbag]
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro ⟨h | rfl | h, hne⟩
        · exact Or.inl h
        · exact absurd rfl hne
        · exact Or.inr h
      · rintro (h | h)
        · exact ⟨Or.inl h, fun he => hvB (he ▸ h)⟩
        · exact ⟨Or.inr (Or.inr h), fun he => hnd.1 (he ▸ h)⟩
    have hk' : (B ∪ lu.toFinset).card ≤ k := by
      refine le_trans (Finset.card_le_card ?_) hk
      intro x; simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]; tauto
    obtain ⟨hw, he⟩ := ih hnd.2 (fun x hx => hB x (by simp [hx])) hk' _ h2
    rw [unselSeg_cons]
    refine ⟨walk_append D ?_ hw, by rw [← List.append_assoc]; exact he⟩
    have hvin : v ∈ bag D pre := by rw [hbag]; simp
    refine walk_cons D (fun x hx => by simp [evH] at hx) ?_ ?_
    · rw [h1, hbag]; exact hk
    refine walk_cons D ?_ ?_ (walk_nil D _ k)
    · intro x hx
      simp only [evQ, CVar.f.injEq] at hx
      subst hx; rw [h1]; exact hvin
    · simpa using (h2 ▸ hk')

theorem walk_sel (ls : List D.TV) (pre : List (Ev D)) (hbag : bag D pre = ∅) :
    Walk D pre (selSeg D ls) 1 ∧ bag D (pre ++ selSeg D ls) = ∅ := by
  induction ls generalizing pre with
  | nil => exact ⟨walk_nil D pre 1, by simpa [selSeg] using hbag⟩
  | cons v ls ih =>
    have h1 : bag D (pre ++ [evH D (Head.a v)]) = {v} := by
      ext x; rw [bag_evH, Xh_a, hbag]; simp
    have h2 : bag D (pre ++ [evH D (Head.a v)] ++ [evH D (Head.b v)]) = {v} := by
      ext x; rw [bag_evH, Xh_b, h1]; simp
    have h3 : bag D (pre ++ [evH D (Head.a v)] ++ [evH D (Head.b v)] ++ [evQ D v]) = ∅ := by
      ext x; rw [bag_evQ, h2]; simp
    have h3' : bag D (pre ++ [evH D (Head.a v), evH D (Head.b v), evQ D v]) = ∅ := by
      rw [← h3]; simp
    obtain ⟨hw, he⟩ := ih _ h3'
    rw [selSeg_cons]
    refine ⟨walk_append D ?_ hw, by rw [← List.append_assoc]; exact he⟩
    refine walk_cons D (fun x hx => by simp [evH] at hx) (by rw [h1]; simp) ?_
    refine walk_cons D (fun x hx => by simp [evH] at hx) (by rw [h2]; simp) ?_
    refine walk_cons D ?_ (by rw [h3]; simp) (walk_nil D _ 1)
    intro x hx
    simp only [evQ, CVar.f.injEq] at hx
    subst hx; rw [h2]; simp

/-! ### Shape of the canonical head part -/
theorem inner1_sub {h : Head D.TV} (hh : h ∈ D.inner1) :
    ∃ p, h = Head.i1 p ∧ p ∈ D.t1.internalPaths ∧ p ≠ [] := by
  simp only [ConstrData.inner1, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hh
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hh
  exact ⟨p, rfl, hp, hne⟩

theorem inner2_sub {h : Head D.TV} (hh : h ∈ D.inner2) :
    ∃ p, h = Head.i2 p ∧ p ∈ D.t2.internalPaths ∧ p ≠ [] := by
  simp only [ConstrData.inner2, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hh
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hh
  exact ⟨p, rfl, hp, hne⟩

theorem list_of_forall {α β : Type} (f : α → β) (P : α → Prop) (l : List β)
    (h : ∀ x ∈ l, ∃ p, x = f p ∧ P p) : ∃ ps : List α, l = ps.map f ∧ ∀ p ∈ ps, P p := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons x l ih =>
    obtain ⟨ps, rfl, hps⟩ := ih (fun y hy => h y (by simp [hy]))
    obtain ⟨p, rfl, hp⟩ := h x (by simp)
    refine ⟨p :: ps, rfl, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hp
    · exact hps q hq

theorem ord1_eq {O : D.CanonOrders} (hO : O.Valid) :
    ∃ ps : List (List Bool), O.ord1 = ps.map Head.i1 ∧
      ∀ p ∈ ps, p ∈ D.t1.internalPaths ∧ p ≠ [] :=
  list_of_forall _ _ _ fun h hh => inner1_sub D (by rw [← hO.2.1]; simpa using hh)

theorem ord2_eq {O : D.CanonOrders} (hO : O.Valid) :
    ∃ ps : List (List Bool), O.ord2 = ps.map Head.i2 ∧
      ∀ p ∈ ps, p ∈ D.t2.internalPaths ∧ p ≠ [] :=
  list_of_forall _ _ _ fun h hh => inner2_sub D (by rw [← hO.2.2.2.2.1]; simpa using hh)

theorem i1_mem {p : List Bool} (hp : p ∈ D.t1.internalPaths) (hne : p ≠ []) :
    Head.i1 p ∈ D.heads := by
  simp [ConstrData.heads, ConstrData.inner1, hp, hne]

theorem i2_mem {p : List Bool} (hp : p ∈ D.t2.internalPaths) (hne : p ≠ []) :
    Head.i2 p ∈ D.heads := by
  simp [ConstrData.heads, ConstrData.inner2, hp, hne]

theorem evform_evH {h : Head D.TV} (hh : h ∈ D.heads) : EvForm D (evH D h) :=
  Or.inl ⟨h, hh, rfl, rfl, by simp [evH]⟩

theorem evform_evT (l : List D.TV) : EvForm D (evT D l) := by
  refine Or.inl ⟨Head.T, by simp [ConstrData.heads], rfl, rfl, ?_⟩
  intro u hu
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
  exact ⟨v, Or.inl rfl, by simp [ConstrData.Xh]⟩

theorem evform_evBP (v : D.TV) : EvForm D (evBP D v) := by
  refine Or.inl ⟨Head.b v, by simp [ConstrData.heads], rfl, rfl, ?_⟩
  intro u hu
  simp only [evBP, List.mem_singleton] at hu
  exact ⟨v, Or.inl hu, by simp [ConstrData.Xh]⟩

theorem evform_evQ (v : D.TV) : EvForm D (evQ D v) :=
  Or.inr ⟨v, Or.inr rfl, rfl, rfl⟩

/-- The canonical head part with the internal heads written by their paths. -/
theorem canonHead_eq (O : D.CanonOrders) (lT lu ls lb : List D.TV) (ps1 ps2 : List (List Bool))
    (h1 : O.ord1 = ps1.map Head.i1) (h2 : O.ord2 = ps2.map Head.i2) :
    canonHead D O lT lu ls lb =
      [evT D lT] ++ ps1.map (fun p => evH D (Head.i1 p)) ++ unselSeg D lu ++
        (evH D Head.U :: ps2.map (fun p => evH D (Head.i2 p))) ++ selSeg D ls ++ prepSeg D lb := by
  simp [canonHead, seg1, seg2, h1, h2, List.map_map, Function.comp_def]

theorem sides_nodup {X : Finset D.TV} {lT lu ls lb : List D.TV} (hL : ListsFor D X lT lu ls lb)
    (ps1 ps2 : List (List Bool)) (h1 : ps1.Nodup) (h2 : ps2.Nodup) :
    (([evT D lT] ++ ps1.map (fun p => evH D (Head.i1 p)) ++ unselSeg D lu ++
        (evH D Head.U :: ps2.map (fun p => evH D (Head.i2 p))) ++ selSeg D ls ++
        prepSeg D lb).map Event.side).Nodup := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ := hL
  have hus : ∀ v ∈ lu, v ∉ ls := by
    intro v hv hv'
    have h1 : v ∈ lu.toFinset := List.mem_toFinset.2 hv
    have h2 : v ∈ ls.toFinset := List.mem_toFinset.2 hv'
    rw [c2] at h1; rw [b2] at h2
    exact (Finset.mem_compl.1 h1) h2
  have hsb : ∀ v ∈ ls, v ∉ lb := by
    intro v hv hv'
    have h1 : v ∈ lb.toFinset := List.mem_toFinset.2 hv'
    have h2 : v ∈ ls.toFinset := List.mem_toFinset.2 hv
    rw [d2] at h1; rw [b2] at h2
    exact (Finset.mem_compl.1 h1) h2
  simp only [unselSeg, selSeg, prepSeg, evT, evH, evQ, evBP, List.map_flatMap, List.nodup_append,
    List.nodup_flatMap, List.map_cons, List.map_nil, List.map_map, List.map_append,
    List.cons_append, List.nil_append, List.nodup_cons, List.mem_map, List.mem_flatMap,
    List.mem_cons, List.mem_append, Function.comp_def, List.not_mem_nil, or_false]
  and_intros
  all_goals first
    | exact List.Nodup.map (fun a b h => by simpa using h) ‹_›
    | (simp; done)
    | (intro x hx; simp; done)
    | (refine List.Nodup.pairwise_of_forall_ne ‹_› fun a _ b _ hab => ?_
       simp [Function.onFun, Ne.symm hab])
    | (intro a ha b hb hab; subst hab; aesop)

/-! ### Dependencies -/
theorem subtreeAt_append {τ : Type} (t : FBTree τ) (p q : List Bool) :
    t.subtreeAt (p ++ q) = (t.subtreeAt p).bind (fun s => s.subtreeAt q) := by
  induction t generalizing p with
  | leaf v => cases p <;> simp [FBTree.subtreeAt]
  | node l r ihl ihr =>
    cases p with
    | nil => simp [FBTree.subtreeAt]
    | cons c p => cases c <;> simp [FBTree.subtreeAt, ihl, ihr]

theorem internal_sub {τ : Type} (t : FBTree τ) (p : List Bool) (h : p ∈ t.internalPaths) :
    ∃ l r, t.subtreeAt p = some (FBTree.node l r) := by
  induction t generalizing p with
  | leaf v => simp [FBTree.internalPaths] at h
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths, List.mem_cons, List.mem_append, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨l, r, rfl⟩
    · simpa [FBTree.subtreeAt] using ihl q hq
    · simpa [FBTree.subtreeAt] using ihr q hq

theorem child_some {τ : Type} (t : FBTree τ) {p : List Bool} (hp : p ∈ t.internalPaths) (c : Bool) :
    ∃ s, t.subtreeAt (p ++ [c]) = some s := by
  obtain ⟨l, r, h⟩ := internal_sub t p hp
  rw [subtreeAt_append, h]
  cases c
  · exact ⟨l, by simp [FBTree.subtreeAt]⟩
  · exact ⟨r, by simp [FBTree.subtreeAt]⟩

theorem head1_child {p : List Bool} (hp : p ∈ D.t1.internalPaths) (c : Bool) :
    D.head1 (p ++ [c]) ≠ Head.T := by
  obtain ⟨s, hs⟩ := child_some D.t1 hp c
  unfold ConstrData.head1
  rw [hs]
  cases s with
  | leaf v => simp
  | node l r => simp

theorem head2_child {p : List Bool} (hp : p ∈ D.t2.internalPaths) (c : Bool) :
    D.head2 (p ++ [c]) ≠ Head.U := by
  obtain ⟨s, hs⟩ := child_some D.t2 hp c
  unfold ConstrData.head2
  rw [hs]
  cases s with
  | leaf v => simp
  | node l r => simp

theorem head2_kind (q : List Bool) :
    D.head2 q = Head.U ∨ (∃ p, D.head2 q = Head.i2 p) ∨ ∃ v, D.head2 q = Head.b v := by
  unfold ConstrData.head2
  split
  · exact Or.inr (Or.inr ⟨_, rfl⟩)
  · split_ifs
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inl rfl

/-- Heads of the first kind (`T`, first-tree internal, `a`). -/
def K1 (d : Head D.TV) : Prop := d = Head.T ∨ (∃ p, d = Head.i1 p) ∨ ∃ v, d = Head.a v

theorem nmem_deps_a {d : Head D.TV} (hd : ∀ u, d ≠ Head.b u) (w : D.TV) :
    d ∉ D.deps (Head.a w) := by
  simp only [ConstrData.deps, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    not_exists, not_and]
  intro u _ h
  exact hd u h.symm

theorem nmem_deps_b (d : Head D.TV) (w : D.TV) : d ∉ D.deps (Head.b w) := by
  simp [ConstrData.deps]

theorem K1_nmem_head2 {d : Head D.TV} (hd : K1 D d) (q : List Bool) : d ≠ D.head2 q := by
  intro h
  rcases head2_kind D q with h2 | ⟨p, h2⟩ | ⟨v, h2⟩ <;>
    rcases hd with rfl | ⟨p', rfl⟩ | ⟨v', rfl⟩ <;> rw [h2] at h <;> cases h

theorem nmem_deps_U {d : Head D.TV} (hd : K1 D d) : d ∉ D.deps Head.U := by
  simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨K1_nmem_head2 D hd _, K1_nmem_head2 D hd _⟩

theorem nmem_deps_i2 {d : Head D.TV} (hd : K1 D d ∨ d = Head.U) {p : List Bool}
    (hp : p ∈ D.t2.internalPaths) : d ∉ D.deps (Head.i2 p) := by
  simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases hd with hd | rfl
  · exact ⟨K1_nmem_head2 D hd _, K1_nmem_head2 D hd _⟩
  · exact ⟨fun h => head2_child D hp false h.symm, fun h => head2_child D hp true h.symm⟩

theorem T_nmem_deps_i1 {p : List Bool} (hp : p ∈ D.t1.internalPaths) :
    Head.T ∉ D.deps (Head.i1 p) := by
  simp only [ConstrData.deps, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun h => head1_child D hp false h.symm, fun h => head1_child D hp true h.symm⟩

/-! ### Dependency order along the canonical head part -/
/-- `e₁` (earlier) does not expand a dependency child of the head expanded by `e₂` (later). -/
def Ord (e₁ e₂ : Ev D) : Prop :=
  ∀ d h, e₁.pivot = CVar.hd d → e₂.pivot = CVar.hd h → d ∉ D.deps h

theorem pairwise_of_mem {α : Type} {R : α → α → Prop} {l : List α}
    (h : ∀ a ∈ l, ∀ b ∈ l, R a b) : l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x l ih =>
    refine List.Pairwise.cons (fun b hb => h x (by simp) b (by simp [hb])) ?_
    exact ih fun a ha b hb => h a (by simp [ha]) b (by simp [hb])

theorem ord_later_a {e₁ e₂ : Ev D} (h₂ : ∀ h, e₂.pivot = CVar.hd h → ∃ w, h = Head.a w)
    (h₁ : ∀ d, e₁.pivot = CVar.hd d → ∀ u, d ≠ Head.b u) : Ord D e₁ e₂ := by
  intro d h hd hh
  obtain ⟨w, rfl⟩ := h₂ h hh
  exact nmem_deps_a D (h₁ d hd) w

theorem ord_later_b {e₁ e₂ : Ev D} (h₂ : ∀ h, e₂.pivot = CVar.hd h → ∃ w, h = Head.b w) :
    Ord D e₁ e₂ := by
  intro d h hd hh
  obtain ⟨w, rfl⟩ := h₂ h hh
  exact nmem_deps_b D d w

theorem piv_unsel {lu : List D.TV} {e : Ev D} (he : e ∈ unselSeg D lu) :
    ∀ h, e.pivot = CVar.hd h → ∃ w, h = Head.a w := by
  intro h hh
  simp only [unselSeg, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨v, -, rfl | rfl⟩ := he
  · simp only [evH, CVar.hd.injEq] at hh; exact ⟨v, hh.symm⟩
  · simp [evQ] at hh

theorem piv_sel {ls : List D.TV} {e : Ev D} (he : e ∈ selSeg D ls) :
    ∀ h, e.pivot = CVar.hd h → ∃ w ∈ ls, h = Head.a w ∨ h = Head.b w := by
  intro h hh
  simp only [selSeg, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨v, hv, rfl | rfl | rfl⟩ := he
  · simp only [evH, CVar.hd.injEq] at hh; exact ⟨v, hv, Or.inl hh.symm⟩
  · simp only [evH, CVar.hd.injEq] at hh; exact ⟨v, hv, Or.inr hh.symm⟩
  · simp [evQ] at hh

theorem piv_prep {lb : List D.TV} {e : Ev D} (he : e ∈ prepSeg D lb) :
    ∀ h, e.pivot = CVar.hd h → ∃ w, h = Head.b w := by
  intro h hh
  simp only [prepSeg, List.mem_map] at he
  obtain ⟨v, -, rfl⟩ := he
  simp only [evBP, CVar.hd.injEq] at hh; exact ⟨v, hh.symm⟩

theorem piv_i1 {ps : List (List Bool)} {e : Ev D}
    (he : e ∈ ps.map (fun p => evH D (Head.i1 p))) :
    ∀ h, e.pivot = CVar.hd h → ∃ p ∈ ps, h = Head.i1 p := by
  intro h hh
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
  simp only [evH, CVar.hd.injEq] at hh; exact ⟨p, hp, hh.symm⟩

theorem piv_i2 {ps : List (List Bool)} {e : Ev D}
    (he : e ∈ ps.map (fun p => evH D (Head.i2 p))) :
    ∀ h, e.pivot = CVar.hd h → ∃ p ∈ ps, h = Head.i2 p := by
  intro h hh
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
  simp only [evH, CVar.hd.injEq] at hh; exact ⟨p, hp, hh.symm⟩

theorem pairwise_map_evH {ps : List (List Bool)} (f : List Bool → Head D.TV)
    (h : ps.Pairwise (fun x y => f x ∉ D.deps (f y))) :
    (ps.map (fun p => evH D (f p))).Pairwise (Ord D) := by
  rw [List.pairwise_map]
  refine h.imp fun hxy d k hd hk => ?_
  simp only [evH, CVar.hd.injEq] at hd hk
  subst hd; subst hk; exact hxy

theorem pairwise_sel {ls : List D.TV} (hls : ∀ v ∈ ls, ∀ w ∈ ls, ¬D.J.Adj v w) :
    (selSeg D ls).Pairwise (Ord D) := by
  induction ls with
  | nil => simp [selSeg]
  | cons v ls ih =>
    rw [selSeg_cons, List.pairwise_append]
    refine ⟨?_, ih fun a ha b hb => hls a (by simp [ha]) b (by simp [hb]), ?_⟩
    · have hQ : ∀ e : Ev D, Ord D e (evQ D v) := fun e d h _ hh => by simp [evQ] at hh
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
      · intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact ord_later_b D (fun h hh => by simp only [evH, CVar.hd.injEq] at hh; exact ⟨v, hh.symm⟩)
        · exact hQ _
      · intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact hQ _
      · simp
    · intro a ha b hb d h hd hh
      obtain ⟨w, hw, hwh⟩ := piv_sel D hb h hh
      rcases hwh with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> simp only [evH, evQ, CVar.hd.injEq, reduceCtorEq] at hd
        · subst hd; exact nmem_deps_a D (fun u => by simp) w
        · subst hd
          simp only [ConstrData.deps, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and, Head.b.injEq, not_exists, not_and]
          intro u hu huv; subst huv
          exact hls w (by simp [hw]) u (by simp) hu
      · exact nmem_deps_b D d w

theorem K1_not_b {d : Head D.TV} (hd : K1 D d) (u : D.TV) : d ≠ Head.b u := by
  rcases hd with rfl | ⟨p, rfl⟩ | ⟨v, rfl⟩ <;> simp

theorem piv_first {lT lu : List D.TV} {ps1 : List (List Bool)} {e : Ev D}
    (he : e ∈ [evT D lT] ++ ps1.map (fun p => evH D (Head.i1 p)) ++ unselSeg D lu) :
    ∀ d, e.pivot = CVar.hd d → K1 D d := by
  intro d hd
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · simp only [List.mem_singleton] at he; subst he
      simp only [evT, CVar.hd.injEq] at hd; exact Or.inl hd.symm
    · obtain ⟨p, -, rfl⟩ := piv_i1 D he d hd; exact Or.inr (Or.inl ⟨p, rfl⟩)
  · obtain ⟨w, rfl⟩ := piv_unsel D he d hd; exact Or.inr (Or.inr ⟨w, rfl⟩)

theorem canon_pairwise {lT lu ls lb : List D.TV} {ps1 ps2 : List (List Bool)}
    (hp1 : ∀ p ∈ ps1, p ∈ D.t1.internalPaths ∧ p ≠ [])
    (hp2 : ∀ p ∈ ps2, p ∈ D.t2.internalPaths ∧ p ≠ [])
    (ho1 : ps1.Pairwise (fun x y => Head.i1 x ∉ D.deps (Head.i1 y)))
    (ho2 : ps2.Pairwise (fun x y => Head.i2 x ∉ D.deps (Head.i2 y)))
    (hls : ∀ v ∈ ls, ∀ w ∈ ls, ¬D.J.Adj v w) :
    ([evT D lT] ++ ps1.map (fun p => evH D (Head.i1 p)) ++ unselSeg D lu ++
        (evH D Head.U :: ps2.map (fun p => evH D (Head.i2 p))) ++ selSeg D ls ++
        prepSeg D lb).Pairwise (Ord D) := by
  have hE3 : ∀ e ∈ evH D Head.U :: ps2.map (fun p => evH D (Head.i2 p)), ∀ h,
      e.pivot = CVar.hd h → h = Head.U ∨ ∃ p ∈ ps2, h = Head.i2 p := by
    intro e he h hh
    rcases List.mem_cons.1 he with rfl | he
    · simp only [evH, CVar.hd.injEq] at hh; exact Or.inl hh.symm
    · exact Or.inr (piv_i2 D he h hh)
  rw [List.pairwise_append, List.pairwise_append, List.pairwise_append, List.pairwise_append,
    List.singleton_append, List.pairwise_cons]
  refine ⟨⟨⟨⟨⟨?_, pairwise_map_evH D _ ho1⟩, ?_, ?_⟩, ?_, ?_⟩, pairwise_sel D hls, ?_⟩, ?_, ?_⟩
  · -- `T` before the first-tree heads
    intro b hb d h hd hh
    obtain ⟨p, hp, rfl⟩ := piv_i1 D hb h hh
    simp only [evT, CVar.hd.injEq] at hd; subst hd
    exact T_nmem_deps_i1 D (hp1 p hp).1
  · exact pairwise_of_mem fun a ha b hb =>
      ord_later_a D (piv_unsel D hb) fun d hd u => by
        obtain ⟨w, rfl⟩ := piv_unsel D ha d hd; simp
  · intro a ha b hb
    refine ord_later_a D (piv_unsel D hb) fun d hd u => K1_not_b D ?_ u
    exact piv_first D (lu := []) (List.mem_append_left _ ha) d hd
  · -- `U` and the second-tree heads
    refine List.Pairwise.cons ?_ (pairwise_map_evH D _ ho2)
    intro b hb d h hd hh
    obtain ⟨p, hp, rfl⟩ := piv_i2 D hb h hh
    simp only [evH, CVar.hd.injEq] at hd; subst hd
    exact nmem_deps_i2 D (Or.inr rfl) (hp2 p hp).1
  · intro a ha b hb d h hd hh
    have hK := piv_first D ha d hd
    rcases hE3 b hb h hh with rfl | ⟨p, hp, rfl⟩
    · exact nmem_deps_U D hK
    · exact nmem_deps_i2 D (Or.inl hK) (hp2 p hp).1
  · intro a ha b hb d h hd hh
    obtain ⟨w, -, rfl | rfl⟩ := piv_sel D hb h hh
    · refine nmem_deps_a D (fun u => ?_) w
      rcases List.mem_append.1 ha with ha | ha
      · exact K1_not_b D (piv_first D ha d hd) u
      · rcases hE3 a ha d hd with rfl | ⟨p, -, rfl⟩ <;> simp
    · exact nmem_deps_b D d w
  · exact pairwise_of_mem fun a _ b hb => ord_later_b D (piv_prep D hb)
  · intro a _ b hb; exact ord_later_b D (piv_prep D hb)

theorem evform_all {lT lu ls lb : List D.TV} {ps1 ps2 : List (List Bool)}
    (hp1 : ∀ p ∈ ps1, p ∈ D.t1.internalPaths ∧ p ≠ [])
    (hp2 : ∀ p ∈ ps2, p ∈ D.t2.internalPaths ∧ p ≠ []) :
    ∀ e ∈ [evT D lT] ++ ps1.map (fun p => evH D (Head.i1 p)) ++ unselSeg D lu ++
        (evH D Head.U :: ps2.map (fun p => evH D (Head.i2 p))) ++ selSeg D ls ++
        prepSeg D lb, EvForm D e := by
  intro e he
  simp only [List.mem_append, List.mem_map, List.mem_cons, unselSeg, selSeg,
    prepSeg, List.mem_flatMap, List.not_mem_nil, or_false] at he
  rcases he with ((((rfl | ⟨p, hp, rfl⟩) | ⟨v, -, rfl | rfl⟩) | (rfl | ⟨p, hp, rfl⟩)) |
      ⟨v, -, rfl | rfl | rfl⟩) | ⟨v, -, rfl⟩
  · exact evform_evT D lT
  · exact evform_evH D (i1_mem D (hp1 p hp).1 (hp1 p hp).2)
  · exact evform_evH D (by simp [ConstrData.heads])
  · exact evform_evQ D v
  · exact evform_evH D (by simp [ConstrData.heads])
  · exact evform_evH D (i2_mem D (hp2 p hp).1 (hp2 p hp).2)
  · exact evform_evH D (by simp [ConstrData.heads])
  · exact evform_evH D (by simp [ConstrData.heads])
  · exact evform_evQ D v
  · exact evform_evBP D v

theorem canon_shape (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hX : IsIndepSet D.J X) {lT lu ls lb : List D.TV} (hL : ListsFor D X lT lu ls lb) :
    Shape D (canonHead D O lT lu ls lb) := by
  obtain ⟨ps1, h1, hp1⟩ := ord1_eq D hO
  obtain ⟨ps2, h2, hp2⟩ := ord2_eq D hO
  have hn1 : ps1.Nodup := List.Nodup.of_map _ (h1 ▸ hO.1)
  have hn2 : ps2.Nodup := List.Nodup.of_map _ (h2 ▸ hO.2.2.2.1)
  have ho1 : ps1.Pairwise (fun x y => Head.i1 x ∉ D.deps (Head.i1 y)) := by
    have := hO.2.2.1; rw [h1, List.pairwise_map] at this; exact this
  have ho2 : ps2.Pairwise (fun x y => Head.i2 x ∉ D.deps (Head.i2 y)) := by
    have := hO.2.2.2.2.2.1; rw [h2, List.pairwise_map] at this; exact this
  have hls : ∀ v ∈ ls, ∀ w ∈ ls, ¬D.J.Adj v w := by
    intro v hv w hw
    have hv' : v ∈ ls.toFinset := List.mem_toFinset.2 hv
    have hw' : w ∈ ls.toFinset := List.mem_toFinset.2 hw
    rw [hL.2.2.2.1] at hv' hw'
    exact hX v hv' w hw'
  rw [canonHead_eq D O lT lu ls lb ps1 ps2 h1 h2]
  refine ⟨evform_all D hp1 hp2, sides_nodup D hL ps1 ps2 hn1 hn2, ?_⟩
  intro p₁ p₂ p₃ e₁ e₂ h d hp hd hh
  have hpw := canon_pairwise D (lT := lT) (lu := lu) (lb := lb) hp1 hp2 ho1 ho2 hls
  rw [hp, List.pairwise_append, List.pairwise_cons] at hpw
  exact hpw.2.1.1 e₂ (by simp) d h hd hh

end ReconfRes.Frozen.Dev.Q427d.PartK2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartK2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Goal clauses along the canonical head part -/
theorem decomp {L1 L2 p t : List (Ev D)} {e : Ev D} (h : L1 ++ L2 = p ++ e :: t) :
    (∃ t', L1 = p ++ e :: t') ∨ ∃ p', L2 = p' ++ e :: t ∧ p = L1 ++ p' := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · exact Or.inr ⟨as, h2, h1⟩
  · cases bs with
    | nil =>
      simp only [List.append_nil, List.nil_append] at h1 h2
      exact Or.inr ⟨[], by simp [h2], by simp [h1]⟩
    | cons x bs =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨bs, h1⟩

theorem evform_hd {e : Ev D} (he : EvForm D e) {h : Head D.TV} (hh : e.pivot = CVar.hd h) :
    e.side = Src.C h ∧ h ∈ D.heads := by
  rcases he with ⟨h', hh', hs, hp, -⟩ | ⟨v, -, -, hp⟩
  · rw [hp, CVar.hd.injEq] at hh
    subst hh; exact ⟨hs, hh'⟩
  · rw [hp] at hh; cases hh

theorem head_pivot (hD : D.Valid) {p : List (Ev D)} {e : Ev D} (hs : Shape D (p ++ [e]))
    {h : Head D.TV} (hh : e.pivot = CVar.hd h) : (CVar.hd h, false) ∈ goal D p := by
  have hsp : Shape D p := shape_sublist D hs (List.sublist_append_left p [e])
  rw [goal_formula_shape D hD hsp]
  obtain ⟨hse, hmem⟩ := evform_hd D (hs.1 e (by simp)) hh
  have hne : h ∉ expd D p := by
    intro hx
    simp only [expd, Finset.mem_filter] at hx
    obtain ⟨-, e', he', hpe'⟩ := hx
    obtain ⟨hse', -⟩ := evform_hd D (hs.1 e' (by simp [he'])) hpe'
    have hnd := hs.2.1
    rw [List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 _ (List.mem_map_of_mem he') _ (by simp) (hse'.trans hse.symm)
  refine Finset.mem_union_left _ ?_
  unfold headPart
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.2 ⟨hmem, hne⟩)

theorem width_le (hD : D.Valid) {L : List (Ev D)} (hs : Shape D L)
    (hc : ((∀ x ∈ L, x.pivot ≠ CVar.hd Head.U) ∧ (bag D L).card ≤ D.q) ∨ (bag D L).card ≤ 1) :
    (goal D L).card ≤ D.W := by
  rw [card_goal_shape D hD hs]
  unfold ConstrData.W ConstrData.r
  rcases hc with ⟨hU, hc⟩ | hc
  · have : Head.U ∉ expd D L := by
      intro hx
      simp only [expd, Finset.mem_filter] at hx
      obtain ⟨-, x, hx, hpx⟩ := hx
      exact hU x hx hpx
    rw [if_neg this]; omega
  · split_ifs <;> omega

theorem card_compl_le (hD : D.Valid) {X : Finset D.TV} (hXℓ : D.ℓ ≤ X.card) :
    Xᶜ.card ≤ D.q := by
  rw [Finset.card_compl]
  have : Fintype.card D.TV = D.m := by
    simp [ConstrData.m, ConstrData.TV, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]
  rw [this]; unfold ConstrData.q; omega

theorem neutral_ord1 {O : D.CanonOrders} (hO : O.Valid) : ∀ e ∈ seg1 D O, Neutral D e := by
  intro e he
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 he
  obtain ⟨p, rfl, -⟩ := inner1_sub D (by rw [← hO.2.1]; simpa using hh)
  exact neutral_evH D (fun v => by simp [ConstrData.Xh])

theorem neutral_seg2 {O : D.CanonOrders} (hO : O.Valid) : ∀ e ∈ seg2 D O, Neutral D e := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact neutral_evH D (fun v => by simp [ConstrData.Xh])
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 he
  obtain ⟨p, rfl, -⟩ := inner2_sub D (by rw [← hO.2.2.2.2.1]; simpa using hh)
  exact neutral_evH D (fun v => by simp [ConstrData.Xh])

theorem neutral_prep (lb : List D.TV) : ∀ e ∈ prepSeg D lb, Neutral D e := by
  intro e he
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 he
  exact neutral_evBP D v

theorem walk_first (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hXℓ : D.ℓ ≤ X.card) {lT lu ls lb : List D.TV} (hL : ListsFor D X lT lu ls lb) :
    Walk D [] ([evT D lT] ++ seg1 D O ++ unselSeg D lu) D.q ∧
      bag D ([evT D lT] ++ seg1 D O ++ unselSeg D lu) = ∅ := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ := hL
  have hq := card_compl_le D hD hXℓ
  have hT : bag D [evT D lT] = Xᶜ := by
    ext v
    have := bag_evT D [] lT v
    rw [List.nil_append, bag_nil] at this
    rw [this, ← a2]; simp
  have w1 : Walk D [] [evT D lT] D.q :=
    walk_cons D (fun v hv => by simp [evT] at hv) (by rw [List.nil_append, hT]; exact hq)
      (walk_nil D _ _)
  obtain ⟨w2, hb2⟩ := walk_neutral D (neutral_ord1 D hO) (pre := [evT D lT]) (k := D.q)
    (by rw [hT]; exact hq)
  obtain ⟨w3, hb3⟩ := walk_unsel D lu c1 ∅ (fun v _ => Finset.notMem_empty v) (k := D.q)
    (by rw [Finset.empty_union, c2]; exact hq) ([evT D lT] ++ seg1 D O)
    (by rw [hb2, hT, Finset.empty_union, c2])
  refine ⟨walk_append D (walk_append D w1 ?_) ?_, hb3⟩
  · rw [List.nil_append]; exact w2
  · rw [List.nil_append]; exact w3

theorem walk_second {O : D.CanonOrders} (hO : O.Valid) (H : List (Ev D)) (hH : bag D H = ∅)
    (ls lb : List D.TV) :
    Walk D H (seg2 D O ++ selSeg D ls ++ prepSeg D lb) 1 ∧
      bag D (H ++ (seg2 D O ++ selSeg D ls ++ prepSeg D lb)) = ∅ := by
  obtain ⟨w1, hb1⟩ := walk_neutral D (neutral_seg2 D hO) (pre := H) (k := 1) (by rw [hH]; simp)
  rw [hH] at hb1
  obtain ⟨w2, hb2⟩ := walk_sel D ls (H ++ seg2 D O) hb1
  obtain ⟨w3, hb3⟩ := walk_neutral D (neutral_prep D lb) (pre := H ++ seg2 D O ++ selSeg D ls)
    (k := 1) (by rw [hb2]; simp)
  refine ⟨walk_append D (walk_append D w1 w2) (by rw [← List.append_assoc]; exact w3), ?_⟩
  rw [← hb2, ← hb3]; simp only [List.append_assoc]

theorem first_not_U {O : D.CanonOrders} (hO : O.Valid) {lT lu : List D.TV} :
    ∀ x ∈ [evT D lT] ++ seg1 D O ++ unselSeg D lu, x.pivot ≠ CVar.hd Head.U := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · simp only [List.mem_singleton] at hx; subst hx; simp [evT]
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hx
      obtain ⟨p, rfl, -⟩ := inner1_sub D (by rw [← hO.2.1]; simpa using hh)
      simp [evH]
  · intro hp
    obtain ⟨w, hw⟩ := piv_unsel D hx _ hp
    cases hw

theorem canonHead_split (O : D.CanonOrders) (lT lu ls lb : List D.TV) :
    canonHead D O lT lu ls lb = ([evT D lT] ++ seg1 D O ++ unselSeg D lu) ++
      (seg2 D O ++ selSeg D ls ++ prepSeg D lb) := by
  simp only [canonHead, List.append_assoc]

theorem expd_canon {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    {lT lu ls lb : List D.TV} (hL : ListsFor D X lT lu ls lb) :
    expd D (canonHead D O lT lu ls lb) = D.heads := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ := hL
  unfold expd
  refine Finset.filter_true_of_mem fun h hh => ?_
  have mS : ∀ e ∈ selSeg D ls, e ∈ canonHead D O lT lu ls lb := fun e he =>
    List.mem_append_left _ (List.mem_append_right _ he)
  have mP : ∀ e ∈ prepSeg D lb, e ∈ canonHead D O lT lu ls lb := fun e he =>
    List.mem_append_right _ he
  have m2 : ∀ e ∈ seg2 D O, e ∈ canonHead D O lT lu ls lb := fun e he =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he))
  have mU : ∀ e ∈ unselSeg D lu, e ∈ canonHead D O lT lu ls lb := fun e he =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ he)))
  have m1 : ∀ e ∈ seg1 D O, e ∈ canonHead D O lT lu ls lb := fun e he =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ he))))
  simp only [ConstrData.heads, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and] at hh
  rcases hh with ((((rfl | rfl) | ⟨v, rfl⟩) | ⟨v, rfl⟩) | hh) | hh
  · exact ⟨evT D lT, by simp [canonHead], rfl⟩
  · exact ⟨evH D Head.U, m2 _ (by simp [seg2]), rfl⟩
  · by_cases hv : v ∈ X
    · have : v ∈ ls := by rw [← List.mem_toFinset, b2]; exact hv
      exact ⟨evH D (Head.a v), mS _ (List.mem_flatMap.2 ⟨v, this, by simp⟩), rfl⟩
    · have : v ∈ lu := by rw [← List.mem_toFinset, c2]; simpa using hv
      exact ⟨evH D (Head.a v), mU _ (List.mem_flatMap.2 ⟨v, this, by simp⟩), rfl⟩
  · by_cases hv : v ∈ X
    · have : v ∈ ls := by rw [← List.mem_toFinset, b2]; exact hv
      exact ⟨evH D (Head.b v), mS _ (List.mem_flatMap.2 ⟨v, this, by simp⟩), rfl⟩
    · have : v ∈ lb := by rw [← List.mem_toFinset, d2]; simpa using hv
      exact ⟨evBP D v, mP _ (List.mem_map_of_mem this), rfl⟩
  · have : h ∈ O.ord1 := by rw [← List.mem_toFinset, hO.2.1]; exact hh
    exact ⟨evH D h, m1 _ (List.mem_map_of_mem this), rfl⟩
  · have : h ∈ O.ord2 := by rw [← List.mem_toFinset, hO.2.2.2.2.1]; exact hh
    exact ⟨evH D h, m2 _ (List.mem_cons_of_mem _ (List.mem_map_of_mem this)), rfl⟩

theorem canon_head (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hX : IsIndepSet D.J X) (hXℓ : D.ℓ ≤ X.card) {lT lu ls lb : List D.TV}
    (hL : ListsFor D X lT lu ls lb) :
    (∀ p e t, canonHead D O lT lu ls lb = p ++ e :: t →
      (e.pivot, false) ∈ goal D p ∧ (goal D (p ++ [e])).card ≤ D.W) ∧
    goal D (canonHead D O lT lu ls lb) = headPart D D.heads := by
  have hsh := canon_shape D hD hO hX hL
  obtain ⟨w1, hb1⟩ := walk_first D hD hO hXℓ hL
  obtain ⟨w2, hb2⟩ := walk_second D hO _ hb1 ls lb
  refine ⟨fun p e t hpet => ?_, ?_⟩
  · have hs : Shape D (p ++ [e]) := by
      refine shape_sublist D hsh ?_
      rw [hpet]
      simp
    have hinfo : (∀ v, e.pivot = CVar.f v → v ∈ bag D p) ∧
        (((∀ x ∈ p ++ [e], x.pivot ≠ CVar.hd Head.U) ∧ (bag D (p ++ [e])).card ≤ D.q) ∨
          (bag D (p ++ [e])).card ≤ 1) := by
      rw [canonHead_split] at hpet
      rcases decomp D hpet with ⟨t', h1⟩ | ⟨p', h2, rfl⟩
      · have := w1 p e t' h1
        simp only [List.nil_append] at this
        refine ⟨this.1, Or.inl ⟨fun x hx => first_not_U D hO (lT := lT) (lu := lu) x ?_, this.2⟩⟩
        rw [h1]
        rcases List.mem_append.1 hx with hx | hx
        · exact List.mem_append_left _ hx
        · simp only [List.mem_singleton] at hx; subst hx; simp
      · have := w2 p' e t h2
        exact ⟨this.1, Or.inr this.2⟩
    refine ⟨?_, width_le D hD hs hinfo.2⟩
    rcases hs.1 e (by simp) with ⟨h, -, -, hp, -⟩ | ⟨v, -, -, hp⟩
    · rw [hp]; exact head_pivot D hD hs hp
    · rw [hp]; exact (Finset.mem_filter.1 (hinfo.1 v hp)).2
  · rw [goal_formula_shape D hD hsh, expd_canon D hO hL, canonHead_split, hb2]
    simp

end ReconfRes.Frozen.Dev.Q427d.PartK2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias canon_head := ReconfRes.Frozen.Dev.Q427d.PartK2.canon_head

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartK1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### The tail -/
/-- The goal clause right after `A`. -/
def Zc : Clause (CVar D.TV) :=
  D.heads.image (fun h => (CVar.z h, false)) ∪ D.ballast.image (fun j => (CVar.p j, false))

/-- A final deletion event. -/
def fe (s : Src D.TV) : Ev D := ⟨s, [], D.finalVar s⟩

/-- The negated pivot literal of a final deletion. -/
def flit (s : Src D.TV) : Literal (CVar D.TV) := (D.finalVar s, false)

/-- The kind of a final source. -/
def FinalKind (s : Src D.TV) : Prop := (∃ h ∈ D.heads, s = Src.z h) ∨ ∃ j ∈ D.ballast, s = Src.p j

theorem final_kind {O : D.CanonOrders} (hO : O.Valid) {s : Src D.TV} (hs : s ∈ O.final) :
    FinalKind D s := by
  have h := hO.2.2.2.2.2.2.2
  have : s ∈ O.final.toFinset := List.mem_toFinset.2 hs
  rw [h] at this
  simp only [Finset.mem_union, Finset.mem_image] at this
  rcases this with ⟨h, hh, rfl⟩ | ⟨j, hj, rfl⟩
  · exact Or.inl ⟨h, hh, rfl⟩
  · exact Or.inr ⟨j, hj, rfl⟩

theorem inv_final {s : Src D.TV} (hs : FinalKind D s) : D.inv s = {(D.finalVar s, true)} := by
  rcases hs with ⟨h, -, rfl⟩ | ⟨j, -, rfl⟩ <;> rfl

theorem flit_mem {s : Src D.TV} (hs : FinalKind D s) : flit D s ∈ Zc D := by
  rcases hs with ⟨h, hh, rfl⟩ | ⟨j, hj, rfl⟩
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hh)
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun j => ((CVar.p j : CVar D.TV), false)) hj)

theorem flit_inj {s s' : Src D.TV} (hs : FinalKind D s) (hs' : FinalKind D s')
    (h : flit D s = flit D s') : s = s' := by
  rcases hs with ⟨h1, -, rfl⟩ | ⟨j1, -, rfl⟩ <;> rcases hs' with ⟨h2, -, rfl⟩ | ⟨j2, -, rfl⟩ <;>
    simp_all [flit, ConstrData.finalVar]

theorem step_fe {s : Src D.TV} (hs : FinalKind D s) (g : Clause (CVar D.TV)) :
    stepG D.inv g (fe D s) = g.erase (flit D s) := by
  simp [stepG, fe, sideLabel, inv_final D hs, flit]

theorem foldl_fe (l : List (Src D.TV)) (hl : ∀ s ∈ l, FinalKind D s) (g : Clause (CVar D.TV)) :
    (l.map (fe D)).foldl (stepG D.inv) g = g \ (l.map (flit D)).toFinset := by
  induction l generalizing g with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.foldl_cons, List.toFinset_cons]
    rw [step_fe D (hl s (by simp)), ih (fun x hx => hl x (by simp [hx]))]
    ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto

theorem goal_after_A {H₀ : List (Ev D)} (hH : goal D H₀ = headPart D D.heads) :
    goal D (H₀ ++ [evA D]) = Zc D := by
  show goalLabel D.inv Src.G (H₀ ++ [evA D]) = _
  rw [goalLabel_snoc]
  change stepG D.inv (goal D H₀) _ = _
  rw [hH]
  have hU : Head.U ∈ D.heads := by simp [ConstrData.heads]
  ext l
  simp only [stepG, evA, sideLabel, List.take_nil, List.foldl_nil, ConstrData.inv, ConstrData.CA,
    headPart, Finset.sdiff_self, Finset.image_empty, if_pos hU, Zc, Finset.mem_union,
    Finset.mem_erase, Finset.mem_singleton, Finset.mem_image, Finset.union_empty, List.length_nil]
  constructor
  · rintro (⟨hne, (h | h) | h⟩ | ⟨hne, (h | h) | h⟩)
    all_goals first | (subst h; simp at hne) | exact Or.inl h | exact Or.inr h
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Or.inl ⟨by simp, Or.inl (Or.inr ⟨a, ha, rfl⟩)⟩
    · exact Or.inl ⟨by simp, Or.inr ⟨a, ha, rfl⟩⟩

theorem goal_tail {H₀ : List (Ev D)} (hH : goal D H₀ = headPart D D.heads)
    (l : List (Src D.TV)) (hl : ∀ s ∈ l, FinalKind D s) :
    goal D (H₀ ++ evA D :: l.map (fe D)) = Zc D \ (l.map (flit D)).toFinset := by
  have : H₀ ++ evA D :: l.map (fe D) = (H₀ ++ [evA D]) ++ l.map (fe D) := by simp
  show goalLabel D.inv Src.G _ = _
  rw [this, goalLabel_eq_foldl, List.foldl_append, ← goalLabel_eq_foldl]
  change List.foldl _ (goal D _) _ = _
  rw [goal_after_A D hH,
    foldl_fe D l hl]

theorem Zc_card (hD : D.Valid) : (Zc D).card ≤ D.W := by
  rw [W_eq D hD]
  have hh := heads_card D hD
  have hr := r_le_q D
  unfold Zc
  have h1 := Finset.card_union_le (D.heads.image (fun h => (CVar.z h, false)))
    (D.ballast.image (fun j => ((CVar.p j : CVar D.TV), false)))
  have h3 := Finset.card_image_le (s := D.heads) (f := fun h => (CVar.z h, false))
  have h4 := Finset.card_image_le (s := D.ballast) (f := fun j => ((CVar.p j : CVar D.TV), false))
  rw [ballast_card] at h4
  omega

/-- The tail `A, final deletions` after any list whose goal clause is `headPart heads`. -/
theorem tail_ok (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {H₀ : List (Ev D)}
    (hH : goal D H₀ = headPart D D.heads) :
    (∀ p e t, tailSeg D O = p ++ e :: t →
      (e.pivot, false) ∈ goal D (H₀ ++ p) ∧ (goal D (H₀ ++ p ++ [e])).card ≤ D.W) ∧
    goal D (H₀ ++ tailSeg D O) = ∅ := by
  have hk : ∀ s ∈ O.final, FinalKind D s := fun s hs => final_kind D hO hs
  have htail : tailSeg D O = evA D :: O.final.map (fe D) := rfl
  refine ⟨fun p e t hp => ?_, ?_⟩
  · rw [htail] at hp
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      refine ⟨?_, ?_⟩
      · rw [List.append_nil, hH]; simp [evA, headPart]
      · rw [List.append_nil, goal_after_A D hH]; exact Zc_card D hD
    | cons a p' =>
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨l1, l2, hfin, rfl, hl2⟩ := List.map_eq_append_iff.1 hp
      obtain ⟨s, l3, rfl, rfl, -⟩ := List.map_eq_cons_iff.1 hl2
      have hk1 : ∀ x ∈ l1, FinalKind D x := fun x hx => hk x (by rw [hfin]; simp [hx])
      have hks : FinalKind D s := hk s (by rw [hfin]; simp)
      refine ⟨?_, ?_⟩
      · rw [goal_tail D hH l1 hk1, Finset.mem_sdiff]
        refine ⟨flit_mem D hks, fun hm => ?_⟩
        obtain ⟨x, hx, hxe⟩ := List.mem_map.1 (List.mem_toFinset.1 hm)
        have := flit_inj D (hk1 x hx) hks hxe
        subst this
        have hnd := hO.2.2.2.2.2.2.1
        rw [hfin, List.nodup_append] at hnd
        exact hnd.2.2 x hx x (by simp) rfl
      · have : H₀ ++ evA D :: List.map (fe D) l1 ++ [fe D s] =
            H₀ ++ evA D :: (l1 ++ [s]).map (fe D) := by simp
        rw [this, goal_tail D hH _ (by
          intro x hx; rcases List.mem_append.1 hx with hx | hx
          · exact hk1 x hx
          · simp at hx; subst hx; exact hks)]
        exact (Finset.card_le_card Finset.sdiff_subset).trans (Zc_card D hD)
  · rw [htail, goal_tail D hH _ hk, Finset.sdiff_eq_empty_iff_subset]
    intro x hx
    rw [List.mem_toFinset, List.mem_map]
    have hf := hO.2.2.2.2.2.2.2
    simp only [Zc, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with ⟨h, hh, rfl⟩ | ⟨j, hj, rfl⟩
    · refine ⟨Src.z h, ?_, rfl⟩
      rw [← List.mem_toFinset, hf]; simp [hh]
    · refine ⟨Src.p j, ?_, rfl⟩
      rw [← List.mem_toFinset, hf]; simp [hj]

/-! ### The source list -/
/-- The source list of a canonical comb, written out. -/
def srcL (O : D.CanonOrders) (lT lu ls lb : List D.TV) : List (Src D.TV) :=
  [Src.G, Src.C Head.T] ++ lT.map Src.P ++ O.ord1.map Src.C ++
    lu.flatMap (fun v => [Src.C (Head.a v), Src.Q v]) ++ [Src.C Head.U] ++ O.ord2.map Src.C ++
    ls.flatMap (fun v => [Src.C (Head.a v), Src.C (Head.b v), Src.Q v]) ++
    lb.flatMap (fun v => [Src.C (Head.b v), Src.P v]) ++ [Src.CA] ++ O.final

theorem srcList_eq (O : D.CanonOrders) (lT lu ls lb : List D.TV) :
    srcList Src.G (canonL D O lT lu ls lb) = srcL D O lT lu ls lb := by
  simp [srcList, srcL, canonL, canonHead, tailSeg, seg1, seg2, unselSeg, selSeg, prepSeg, evT, evH, evQ,
    evBP, evA, List.flatMap_map, Function.comp_def, List.flatMap_append, List.flatMap_assoc, ← List.map_eq_flatMap]

theorem srcL_length (O : D.CanonOrders) (lT lu ls lb : List D.TV) :
    (srcL D O lT lu ls lb).length = lT.length + O.ord1.length + 2 * lu.length + O.ord2.length +
      3 * ls.length + 2 * lb.length + O.final.length + 4 := by
  simp [srcL, List.length_flatMap]
  ring

theorem heads_cases {h : Head D.TV} (hh : h ∈ D.heads) :
    h = Head.T ∨ h = Head.U ∨ (∃ v, h = Head.a v) ∨ (∃ v, h = Head.b v) ∨ h ∈ D.inner1 ∨
      h ∈ D.inner2 := by
  simp only [ConstrData.heads, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and] at hh
  rcases hh with ((((rfl | rfl) | ⟨v, rfl⟩) | ⟨v, rfl⟩) | hh) | hh
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))

theorem srcs_cases {x : Src D.TV} (hx : x ∈ D.srcs) :
    (∃ h ∈ D.heads, x = Src.C h) ∨ x = Src.CA ∨ x = Src.G ∨ (∃ h ∈ D.heads, x = Src.z h) ∨
      (∃ j ∈ D.ballast, x = Src.p j) ∨ (∃ v, x = Src.P v) ∨ ∃ v, x = Src.Q v := by
  simp only [ConstrData.srcs, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with (((((⟨h, hh, rfl⟩ | rfl | rfl) | ⟨h, hh, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨v, rfl⟩) | ⟨v, rfl⟩)
  · exact Or.inl ⟨h, hh, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hh, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩)))))

theorem C_srcs {h : Head D.TV} (hh : h ∈ D.heads) : Src.C h ∈ D.srcs := by
  simp [ConstrData.srcs, hh]

theorem G_srcs : Src.G ∈ D.srcs := by simp [ConstrData.srcs]

theorem CA_srcs : Src.CA ∈ D.srcs := by simp [ConstrData.srcs]

theorem P_srcs (v : D.TV) : Src.P v ∈ D.srcs := by simp [ConstrData.srcs]

theorem Q_srcs (v : D.TV) : Src.Q v ∈ D.srcs := by simp [ConstrData.srcs]

theorem T_mem : Head.T ∈ D.heads := by simp [ConstrData.heads]

theorem U_mem : Head.U ∈ D.heads := by simp [ConstrData.heads]

theorem a_mem (v : D.TV) : Head.a v ∈ D.heads := by simp [ConstrData.heads]

theorem b_mem (v : D.TV) : Head.b v ∈ D.heads := by simp [ConstrData.heads]

theorem inner1_heads {h : Head D.TV} (hh : h ∈ D.inner1) : h ∈ D.heads := by
  simp [ConstrData.heads, hh]

theorem inner2_heads {h : Head D.TV} (hh : h ∈ D.inner2) : h ∈ D.heads := by
  simp [ConstrData.heads, hh]

theorem srcL_toFinset {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    {lT lu ls lb : List D.TV} (hL : ListsFor D X lT lu ls lb) :
    (srcL D O lT lu ls lb).toFinset = D.srcs := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ := hL
  have hT : ∀ v, v ∈ lT ↔ v ∈ X := fun v => by rw [← a2, List.mem_toFinset]
  have hs : ∀ v, v ∈ ls ↔ v ∈ X := fun v => by rw [← b2, List.mem_toFinset]
  have hu : ∀ v, v ∈ lu ↔ v ∉ X := fun v => by rw [← Finset.mem_compl, ← c2, List.mem_toFinset]
  have hb : ∀ v, v ∈ lb ↔ v ∉ X := fun v => by rw [← Finset.mem_compl, ← d2, List.mem_toFinset]
  have h1 : ∀ h, h ∈ O.ord1 ↔ h ∈ D.inner1 := fun h => by rw [← hO.2.1, List.mem_toFinset]
  have h2 : ∀ h, h ∈ O.ord2 ↔ h ∈ D.inner2 := fun h => by rw [← hO.2.2.2.2.1, List.mem_toFinset]
  have hf : ∀ s, s ∈ O.final ↔ s ∈ D.heads.image Src.z ∪ D.ballast.image Src.p :=
    fun s => by rw [← hO.2.2.2.2.2.2.2, List.mem_toFinset]
  ext x
  rw [List.mem_toFinset]
  simp only [srcL, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false]
  constructor
  · rintro ((((((((((rfl | rfl) | ⟨v, -, rfl⟩) | ⟨h, hh, rfl⟩) | ⟨v, -, rfl | rfl⟩) | rfl) |
      ⟨h, hh, rfl⟩) | ⟨v, -, rfl | rfl | rfl⟩) | ⟨v, -, rfl | rfl⟩) | rfl) | hx)
    all_goals first
      | exact G_srcs D
      | exact CA_srcs D
      | exact P_srcs D _
      | exact Q_srcs D _
      | exact C_srcs D (T_mem D)
      | exact C_srcs D (U_mem D)
      | exact C_srcs D (a_mem D _)
      | exact C_srcs D (b_mem D _)
      | exact C_srcs D (inner1_heads D ((h1 h).1 hh))
      | exact C_srcs D (inner2_heads D ((h2 h).1 hh))
      | skip
    have := (hf x).1 hx
    simp only [Finset.mem_union, Finset.mem_image] at this
    rcases this with ⟨h, hh, rfl⟩ | ⟨j, hj, rfl⟩
    · simp [ConstrData.srcs, hh]
    · simp [ConstrData.srcs, hj]
  · intro hx
    rcases srcs_cases D hx with ⟨h, hh, rfl⟩ | rfl | rfl | ⟨h, hh, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨v, rfl⟩ |
      ⟨v, rfl⟩
    · rcases heads_cases D hh with rfl | rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ | hh | hh
      · simp
      · simp
      · by_cases hv : v ∈ X
        · simp [(hs v).2 hv]
        · simp [(hu v).2 hv]
      · by_cases hv : v ∈ X
        · simp [(hs v).2 hv]
        · simp [(hb v).2 hv]
      · simp [(h1 _).2 hh]
      · simp [(h2 _).2 hh]
    · simp
    · simp
    · have : Src.z h ∈ O.final := (hf _).2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hh))
      simp [this]
    · have : Src.p j ∈ O.final :=
        (hf _).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
      simp [this]
    · by_cases hv : v ∈ X
      · simp [(hT v).2 hv]
      · simp [(hb v).2 hv]
    · by_cases hv : v ∈ X
      · simp [(hs v).2 hv]
      · simp [(hu v).2 hv]

theorem final_length (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) :
    O.final.length + 2 = 4 * D.m + D.r := by
  rw [← List.toFinset_card_of_nodup hO.2.2.2.2.2.2.1, hO.2.2.2.2.2.2.2,
    Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => Src.z.inj h),
    Finset.card_image_of_injective _ (fun _ _ h => Src.p.inj h), ballast_card]
  · have := heads_card D hD; omega
  · refine Finset.disjoint_left.2 fun x hx hy => ?_
    simp only [Finset.mem_image] at hx hy
    obtain ⟨_, -, rfl⟩ := hx
    obtain ⟨_, -, h⟩ := hy
    cases h

theorem canon_src (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    {lT lu ls lb : List D.TV} (hL : ListsFor D X lT lu ls lb) :
    (srcList Src.G (canonL D O lT lu ls lb)).Nodup ∧
      (srcList Src.G (canonL D O lT lu ls lb)).toFinset = D.srcs := by
  rw [srcList_eq]
  have hfin := srcL_toFinset D hO hL
  refine ⟨?_, hfin⟩
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ := hL
  have hT := List.toFinset_card_of_nodup a1
  have hs := List.toFinset_card_of_nodup b1
  have hu := List.toFinset_card_of_nodup c1
  have hb := List.toFinset_card_of_nodup d1
  have h1 := List.toFinset_card_of_nodup hO.1
  have h2 := List.toFinset_card_of_nodup hO.2.2.2.1
  rw [a2] at hT; rw [b2] at hs; rw [c2] at hu; rw [d2] at hb
  rw [hO.2.1] at h1; rw [hO.2.2.2.2.1] at h2
  have hc : Xᶜ.card + X.card = D.m := by
    rw [Finset.card_compl, card_TV]; have := Finset.card_le_univ X; rw [card_TV] at this; omega
  have i1 := inner1_card D hD
  have i2 := inner2_card D hD
  have hf := final_length D hD hO
  have hlen := srcL_length D O lT lu ls lb
  have hsc := srcs_card D hD
  have hm := m_ge D hD
  have hcard : (srcL D O lT lu ls lb).toFinset.card = (srcL D O lT lu ls lb).length := by
    rw [hfin, hsc, hlen]; unfold ConstrData.α; omega
  exact Multiset.toFinset_card_eq_card_iff_nodup.1 hcard

end ReconfRes.Frozen.Dev.Q427d.PartK1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartK1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Private chains -/
theorem mem_foldl_erase {V : Type} [DecidableEq V] {ι : Type} (x : Literal V)
    (us : List (ι × V)) (c : Clause V) :
    x ∈ us.foldl (fun c u => c.erase (u.2, false)) c ↔ x ∈ c ∧ ∀ u ∈ us, x ≠ (u.2, false) := by
  induction us generalizing c with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, ih, Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

theorem eventOK_noprep {e : Ev D} (hp : e.prep = []) (hpiv : (e.pivot, true) ∈ D.inv e.side) :
    EventOK D.inv e := by
  refine ⟨fun l u t h => ?_, ?_⟩
  · rw [hp] at h; simp at h
  · simpa [sideLabel, hp] using hpiv

theorem hd_mem_Ch (h : Head D.TV) : (CVar.hd h, true) ∈ D.Ch h := by simp [ConstrData.Ch]

theorem eventOK_evH (h : Head D.TV) : EventOK D.inv (evH D h) :=
  eventOK_noprep D rfl (hd_mem_Ch D h)

theorem eventOK_evQ (v : D.TV) : EventOK D.inv (evQ D v) :=
  eventOK_noprep D rfl (by simp [evQ, ConstrData.inv])

theorem eventOK_evA : EventOK D.inv (evA D) :=
  eventOK_noprep D rfl (by simp [evA, ConstrData.inv, ConstrData.CA])

theorem eventOK_fe {s : Src D.TV} (hs : FinalKind D s) : EventOK D.inv (fe D s) :=
  eventOK_noprep D rfl (by simp [fe, inv_final D hs])

theorem eventOK_evT {l : List D.TV} (hl : l.Nodup) : EventOK D.inv (evT D l) := by
  refine ⟨fun l' u t h => ?_, ?_⟩
  · simp only [evT] at h
    obtain ⟨l1, l2, rfl, rfl, h2⟩ := List.map_eq_append_iff.1 h
    obtain ⟨v, l3, rfl, rfl, -⟩ := List.map_eq_cons_iff.1 h2
    refine ⟨rfl, ?_⟩
    simp only [sideLabel, evT, List.length_map]
    rw [List.map_append, List.map_cons, List.take_left' (by simp), mem_foldl_erase]
    refine ⟨by simp [ConstrData.inv, ConstrData.Ch, ConstrData.Xh], fun u hu he => ?_⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    simp only [Prod.mk.injEq, CVar.f.injEq, and_true] at he
    subst he
    rw [List.nodup_append] at hl
    exact hl.2.2 v hw v (by simp) rfl
  · simp only [sideLabel, List.take_length]
    rw [mem_foldl_erase]
    exact ⟨hd_mem_Ch D _, fun u _ he => by simp at he⟩

theorem eventOK_evBP (v : D.TV) : EventOK D.inv (evBP D v) := by
  refine ⟨fun l u t h => ?_, ?_⟩
  · simp only [evBP] at h
    cases l with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, by simp [sideLabel, evBP, ConstrData.inv, ConstrData.Ch, ConstrData.Xh]⟩
    | cons a l => simp at h
  · simp only [sideLabel, List.take_length]
    rw [mem_foldl_erase]
    exact ⟨hd_mem_Ch D _, fun u _ he => by simp at he⟩

theorem canon_events_ok {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    {lT lu ls lb : List D.TV} (hL : ListsFor D X lT lu ls lb) :
    ∀ e ∈ canonL D O lT lu ls lb, EventOK D.inv e := by
  intro e he
  simp only [canonL, canonHead, List.mem_append] at he
  rcases he with (((((he | he) | he) | he) | he) | he) | he
  · rw [List.mem_singleton] at he; subst he; exact eventOK_evT D hL.1
  · obtain ⟨h, -, rfl⟩ := List.mem_map.1 he; exact eventOK_evH D h
  · obtain ⟨v, -, he⟩ := List.mem_flatMap.1 he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact eventOK_evH D _
    · exact eventOK_evQ D _
  · rcases List.mem_cons.1 he with rfl | he
    · exact eventOK_evH D _
    · obtain ⟨h, -, rfl⟩ := List.mem_map.1 he; exact eventOK_evH D h
  · obtain ⟨v, -, he⟩ := List.mem_flatMap.1 he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact eventOK_evH D _
    · exact eventOK_evH D _
    · exact eventOK_evQ D _
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 he; exact eventOK_evBP D v
  · rcases List.mem_cons.1 he with rfl | he
    · exact eventOK_evA D
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he; exact eventOK_fe D (final_kind D hO hs)

theorem decomp {L1 L2 p t : List (Ev D)} {e : Ev D} (h : L1 ++ L2 = p ++ e :: t) :
    (∃ t', L1 = p ++ e :: t') ∨ ∃ p', L2 = p' ++ e :: t ∧ p = L1 ++ p' := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · exact Or.inr ⟨as, h2, h1⟩
  · cases bs with
    | nil =>
      simp only [List.append_nil, List.nil_append] at h1 h2
      exact Or.inr ⟨[], by simp [h2], by simp [h1]⟩
    | cons x bs =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨bs, h1⟩

theorem canon_ok (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hX : IsIndepSet D.J X) (hXℓ : D.ℓ ≤ X.card) {lT lu ls lb : List D.TV}
    (hL : ListsFor D X lT lu ls lb) : CombOK D (canonL D O lT lu ls lb) := by
  obtain ⟨hnd, hfs⟩ := canon_src D hD hO hL
  have hH := Q427d.canon_head D hD hO hX hXℓ hL
  have hT := tail_ok D hD hO hH.2
  refine ⟨hnd, hfs, fun x hx => ⟨Finset.mem_image_of_mem _ hx, srcs_width D hD x hx⟩,
    canon_events_ok D hO hL, ?_, hT.2, ?_⟩
  · intro p e t hp
    unfold canonL at hp
    rcases decomp D hp with ⟨t', h1⟩ | ⟨p', h2, rfl⟩
    · exact hH.1 p e t' h1
    · exact hT.1 p' e t h2
  · rw [srcs_card D hD]
    have := m_ge D hD
    unfold ConstrData.α
    omega

end ReconfRes.Frozen.Dev.Q427d.PartK1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias canon_ok := ReconfRes.Frozen.Dev.Q427d.PartK1.canon_ok

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartS1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-- A permutation of a nodup list with the same finset. -/
theorem nodup_toFinset_of_perm {α : Type} [DecidableEq α] {l l₀ : List α} (hp : l.Perm l₀)
    (hn : l₀.Nodup) : l.Nodup ∧ l.toFinset = l₀.toFinset :=
  ⟨hp.nodup_iff.2 hn, List.toFinset_eq_of_perm _ _ hp⟩

/-- The `T` event with the prep list split around an adjacent pair. -/
theorem canonL_privT_split (O : D.CanonOrders) (p t lu ls lb : List D.TV) (x y : D.TV) :
    canonL D O (p ++ x :: y :: t) lu ls lb =
      [] ++ (⟨Src.C Head.T, p.map (fun v => (Src.P v, CVar.f v)) ++
          (Src.P x, CVar.f x) :: (Src.P y, CVar.f y) :: t.map (fun v => (Src.P v, CVar.f v)),
          CVar.hd Head.T⟩ : Ev D) ::
        (seg1 D O ++ unselSeg D lu ++ seg2 D O ++ selSeg D ls ++ prepSeg D lb ++ tailSeg D O) := by
  simp [canonL, canonHead, evT, List.map_append]

theorem sort_privT (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hX : IsIndepSet D.J X) (hXℓ : D.ℓ ≤ X.card) {lT lT' lu ls lb : List D.TV}
    (hL : ListsFor D X lT lu ls lb) (hL' : ListsFor D X lT' lu ls lb) :
    Link D (canonL D O lT lu ls lb) (canonL D O lT' lu ls lb) := by
  obtain ⟨hn, hf, h3, h4, h5, h6, h7, h8⟩ := hL
  have hLp : ∀ l : List D.TV, l.Perm lT → ListsFor D X l lu ls lb := by
    intro l hl
    obtain ⟨a, b⟩ := nodup_toFinset_of_perm hl hn
    exact ⟨a, b.trans hf, h3, h4, h5, h6, h7, h8⟩
  have hp' : lT'.Perm lT :=
    List.perm_of_nodup_nodup_toFinset_eq hL'.1 hn (hL'.2.1.trans hf.symm)
  refine perm_of_adjSwap (fun l l' => Link D (canonL D O l lu ls lb) (canonL D O l' lu ls lb))
    lT ?_ ?_ ?_ (List.Perm.refl lT) hp'
  · intro l hl
    exact link_refl (canon_ok D hD hO hX hXℓ (hLp l hl))
  · intro a b c _ _ _ hab hbc
    exact link_trans hab hbc
  · intro p x y t hl
    have hl' : (p ++ y :: x :: t).Perm lT :=
      (List.Perm.append_left p (List.Perm.swap x y t)).trans hl
    have h₁ := canon_ok D hD hO hX hXℓ (hLp _ hl)
    have h₂ := canon_ok D hD hO hX hXℓ (hLp _ hl')
    show CombLink 2 D.formula D.W (2 * D.α - 1) D.inv D.srcs Src.G _ _
    unfold CombOK at h₁ h₂
    rw [canonL_privT_split] at h₁ h₂ ⊢
    rw [canonL_privT_split]
    exact link_prepSwap (by norm_num) h₁ h₂

end ReconfRes.Frozen.Dev.Q427d.PartS1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ## Part S: sorting the set orders -/
alias sort_privT := ReconfRes.Frozen.Dev.Q427d.PartS1.sort_privT

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartS1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-- The canonical list with the `prepB` order split around an adjacent pair. -/
theorem canonL_prepB_split (O : D.CanonOrders) (lT lu ls p t : List D.TV) (x y : D.TV) :
    canonL D O lT lu ls (p ++ x :: y :: t) =
      ([evT D lT] ++ seg1 D O ++ unselSeg D lu ++ seg2 D O ++ selSeg D ls ++ prepSeg D p) ++
        evBP D x :: evBP D y :: (prepSeg D t ++ tailSeg D O) := by
  simp [canonL, canonHead, prepSeg, List.map_append]

theorem hd_not_mem_side_evBP (x y : D.TV) :
    (CVar.hd (Head.b y), false) ∉
      (sideLabel D.inv (evBP D x) (evBP D x).prep.length).erase ((evBP D x).pivot, true) := by
  simp [sideLabel, evBP, ConstrData.inv, ConstrData.Ch, ConstrData.deps, ConstrData.Xh]

theorem sort_prepB (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hX : IsIndepSet D.J X) (hXℓ : D.ℓ ≤ X.card) {lT lu ls lb lb' : List D.TV}
    (hL : ListsFor D X lT lu ls lb) (hL' : ListsFor D X lT lu ls lb') :
    Link D (canonL D O lT lu ls lb) (canonL D O lT lu ls lb') := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hn, hf⟩ := hL
  have hLp : ∀ l : List D.TV, l.Perm lb → ListsFor D X lT lu ls l := by
    intro l hl
    obtain ⟨a, b⟩ := nodup_toFinset_of_perm hl hn
    exact ⟨h1, h2, h3, h4, h5, h6, a, b.trans hf⟩
  have hp' : lb'.Perm lb :=
    List.perm_of_nodup_nodup_toFinset_eq hL'.2.2.2.2.2.2.1 hn (hL'.2.2.2.2.2.2.2.trans hf.symm)
  refine perm_of_adjSwap (fun l l' => Link D (canonL D O lT lu ls l) (canonL D O lT lu ls l'))
    lb ?_ ?_ ?_ (List.Perm.refl lb) hp'
  · intro l hl
    exact link_refl (canon_ok D hD hO hX hXℓ (hLp l hl))
  · intro a b c _ _ _ hab hbc
    exact link_trans hab hbc
  · intro p x y t hl
    have hl' : (p ++ y :: x :: t).Perm lb :=
      (List.Perm.append_left p (List.Perm.swap x y t)).trans hl
    have h₁ := canon_ok D hD hO hX hXℓ (hLp _ hl)
    have h₂ := canon_ok D hD hO hX hXℓ (hLp _ hl')
    show CombLink 2 D.formula D.W (2 * D.α - 1) D.inv D.srcs Src.G _ _
    unfold CombOK at h₁ h₂
    rw [canonL_prepB_split] at h₁ h₂ ⊢
    rw [canonL_prepB_split]
    refine link_swap' (by norm_num) h₁ h₂ ?_
    simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact step_comm _ _ _ _ (hd_not_mem_side_evBP D x y) (hd_not_mem_side_evBP D y x)

end ReconfRes.Frozen.Dev.Q427d.PartS1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias sort_prepB := ReconfRes.Frozen.Dev.Q427d.PartS1.sort_prepB

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartS2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
theorem card_TV : Fintype.card D.TV = D.m := by
  simp [ConstrData.m, ConstrData.TV, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

theorem mem_foldl_erase {α β : Type} [DecidableEq α] (g : β → α) (x : α) :
    ∀ (l : List β) (c : Finset α),
      x ∈ l.foldl (fun c u => c.erase (g u)) c ↔ x ∈ c ∧ ∀ u ∈ l, x ≠ g u
  | [], c => by simp
  | u :: l, c => by
    rw [List.foldl_cons, mem_foldl_erase g x l]
    simp only [Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

/-- The events before `U` in the canonical list (with unselected order `lu`). -/
def M (O : D.CanonOrders) (lT lu : List D.TV) : List (Ev D) :=
  [evT D lT] ++ seg1 D O ++ unselSeg D lu

theorem mem_ord1 {O : D.CanonOrders} (hO : O.Valid) {h : Head D.TV} (hh : h ∈ O.ord1) :
    ∃ p, h = Head.i1 p := by
  have : h ∈ D.inner1 := by rw [← hO.2.1]; exact List.mem_toFinset.2 hh
  simp only [ConstrData.inner1, Finset.mem_image] at this
  obtain ⟨p, _, rfl⟩ := this
  exact ⟨p, rfl⟩

theorem mem_M {O : D.CanonOrders} (hO : O.Valid) {lT lu : List D.TV} {e : Ev D}
    (he : e ∈ M D O lT lu) :
    e = evT D lT ∨ (∃ p, e = evH D (Head.i1 p)) ∨
      ∃ u ∈ lu, e = evH D (Head.a u) ∨ e = evQ D u := by
  simp only [M, seg1, unselSeg, List.mem_append, List.mem_map,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (he | ⟨h, hh, rfl⟩) | ⟨u, hu, he⟩
  · exact Or.inl he
  · obtain ⟨p, rfl⟩ := mem_ord1 D hO hh
    exact Or.inr (Or.inl ⟨p, rfl⟩)
  · exact Or.inr (Or.inr ⟨u, hu, he⟩)

theorem pivot_M {O : D.CanonOrders} (hO : O.Valid) {lT lu : List D.TV} {e : Ev D}
    (he : e ∈ M D O lT lu) : e.pivot ≠ CVar.hd Head.U ∧ e.pivot ≠ CVar.A := by
  rcases mem_M D hO he with rfl | ⟨p, rfl⟩ | ⟨u, _, rfl | rfl⟩ <;>
    simp [evT, evH, evQ]

theorem side_M {O : D.CanonOrders} (hO : O.Valid) {lT lu : List D.TV} {e : Ev D}
    (he : e ∈ M D O lT lu) {v : D.TV}
    (hv : (CVar.f v, false) ∈ sideLabel D.inv e e.prep.length) : v ∉ lT ∨ v ∈ lu := by
  rcases mem_M D hO he with rfl | ⟨p, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · left
    intro hvT
    simp only [sideLabel, evT, List.take_length] at hv
    rw [mem_foldl_erase (fun u : Src D.TV × CVar D.TV => (u.2, false))] at hv
    exact hv.2 (Src.P v, CVar.f v) (by simp [hvT]) rfl
  · simp [sideLabel, evH, ConstrData.inv, ConstrData.Ch, ConstrData.deps, ConstrData.Xh] at hv
  · right
    simp [sideLabel, evH, ConstrData.inv, ConstrData.Ch, ConstrData.deps, ConstrData.Xh] at hv
    rw [hv]; exact hu
  · simp [sideLabel, evQ, ConstrData.inv] at hv

theorem width (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hXℓ : D.ℓ ≤ X.card) {lT lu : List D.TV} (hT : lT.toFinset = X) (hu : lu.toFinset = Xᶜ)
    {P t P' : List (Ev D)} (hok : CombOK D (P ++ t)) (hM : ∀ e ∈ P, e ∈ M D O lT lu)
    (hs : P'.Sublist P) : (goal D P').card ≤ D.W := by
  have hA : ∀ e ∈ P, e.pivot ≠ CVar.A := fun e he => (pivot_M D hO (hM e he)).2
  have hsh := shape_sublist D (shape_of_ok D hD hok hA) hs
  rw [card_goal_shape D hD hsh]
  have hU : Head.U ∉ expd D P' := by
    simp only [expd, Finset.mem_filter, not_and, not_exists]
    intro _ e he hpiv
    exact (pivot_M D hO (hM e (hs.subset he))).1 hpiv
  rw [if_neg hU]
  have hb : bag D P' ⊆ Xᶜ := by
    intro v hv
    rw [mem_bag] at hv
    obtain ⟨p₁, e, t₁, hp, hmem, _⟩ := hv
    have he : e ∈ P := hs.subset (by rw [hp]; simp)
    rcases side_M D hO (hM e he) hmem with h | h
    · rw [Finset.mem_compl, ← hT]; simpa using h
    · rw [← hu]; simpa using h
  have hc := Finset.card_le_card hb
  rw [Finset.card_compl, card_TV] at hc
  simp only [ConstrData.W, ConstrData.q, ConstrData.ℓ] at hc hXℓ ⊢
  omega

theorem mem_goal_snoc {p : List (Ev D)} {e : Ev D} {l : Literal (CVar D.TV)}
    (h : l ∈ goal D p) (hne : l ≠ (e.pivot, false)) : l ∈ goal D (p ++ [e]) := by
  simp only [goal, goalLabel_snoc, stepG, Finset.mem_union, Finset.mem_erase]
  exact Or.inr ⟨hne, h⟩

theorem mem_goal_side {p : List (Ev D)} {e : Ev D} {l : Literal (CVar D.TV)}
    (h : l ∈ sideLabel D.inv e e.prep.length) (hne : l ≠ (e.pivot, true)) :
    l ∈ goal D (p ++ [e]) := by
  simp only [goal, goalLabel_snoc, stepG, Finset.mem_union, Finset.mem_erase]
  exact Or.inl ⟨hne, h⟩

theorem mem_goal_of_snoc {p : List (Ev D)} {e : Ev D} {l : Literal (CVar D.TV)}
    (h : l ∈ goal D (p ++ [e])) (hns : l ∉ sideLabel D.inv e e.prep.length) : l ∈ goal D p := by
  simp only [goal, goalLabel_snoc, stepG, Finset.mem_union, Finset.mem_erase] at h
  rcases h with h | h
  · exact absurd h.2 hns
  · exact h.2

/-- One adjacent goal swap among the events before `U`. -/
theorem uswap (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hXℓ : D.ℓ ≤ X.card) {lT lu : List D.TV} (hT : lT.toFinset = X) (hu : lu.toFinset = Xᶜ)
    {A B : List (Ev D)} {e₁ e₂ : Ev D} (hok : CombOK D (A ++ e₁ :: e₂ :: B))
    (hM : ∀ e ∈ A ++ [e₁, e₂], e ∈ M D O lT lu)
    (hp₂ : (e₂.pivot, false) ∈ goal D A) (hp₁ : (e₁.pivot, false) ∈ goal D (A ++ [e₂]))
    (hc₁ : (e₂.pivot, false) ∉ (sideLabel D.inv e₁ e₁.prep.length).erase (e₁.pivot, true))
    (hc₂ : (e₁.pivot, false) ∉ (sideLabel D.inv e₂ e₂.prep.length).erase (e₂.pivot, true)) :
    Link D (A ++ e₁ :: e₂ :: B) (A ++ e₂ :: e₁ :: B) := by
  have hok' : CombOK D ((A ++ [e₁, e₂]) ++ B) := by
    rw [List.append_assoc]; exact hok
  have hw := width D hD hO hXℓ hT hu hok' hM
    (List.Sublist.append_left (List.sublist_cons_self e₁ [e₂]) A)
  refine link_swap (by norm_num) hok hp₂ hp₁ hw ?_
  simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact step_comm _ _ _ _ hc₁ hc₂

/-- The canonical list with the unselected order split around an adjacent pair. -/
theorem canonL_unsel_split (O : D.CanonOrders) (lT ls lb p t : List D.TV) (x y : D.TV) :
    canonL D O lT (p ++ x :: y :: t) ls lb =
      ([evT D lT] ++ seg1 D O ++ unselSeg D p) ++
        evH D (Head.a x) :: evQ D x :: evH D (Head.a y) :: evQ D y ::
          (unselSeg D t ++ seg2 D O ++ selSeg D ls ++ prepSeg D lb ++ tailSeg D O) := by
  simp [canonL, canonHead, unselSeg, List.flatMap_append]

theorem fx_mem_a (x : D.TV) :
    (CVar.f x, false) ∈ sideLabel D.inv (evH D (Head.a x)) (evH D (Head.a x)).prep.length := by
  simp [sideLabel, evH, ConstrData.inv, ConstrData.Ch, ConstrData.Xh]

theorem fy_not_a {x y : D.TV} (hxy : x ≠ y) :
    (CVar.f y, false) ∉ sideLabel D.inv (evH D (Head.a x)) (evH D (Head.a x)).prep.length := by
  simp [sideLabel, evH, ConstrData.inv, ConstrData.Ch, ConstrData.Xh, ConstrData.deps, Ne.symm hxy]

theorem hd_not_a (x y : D.TV) :
    (CVar.hd (Head.a y), false) ∉
      sideLabel D.inv (evH D (Head.a x)) (evH D (Head.a x)).prep.length := by
  simp [sideLabel, evH, ConstrData.inv, ConstrData.Ch, ConstrData.Xh, ConstrData.deps]

theorem not_side_Q (x : D.TV) (l : Literal (CVar D.TV)) (hl : l.2 = false) :
    l ∉ sideLabel D.inv (evQ D x) (evQ D x).prep.length := by
  obtain ⟨a, b⟩ := l
  simp only at hl
  subst hl
  simp [sideLabel, evQ, ConstrData.inv]

/-- The block `a_x Q_x a_y Q_y ↦ a_y Q_y a_x Q_x` before `U`, by four goal swaps. -/
theorem unsel_block (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hXℓ : D.ℓ ≤ X.card) {lT lu : List D.TV} (hT : lT.toFinset = X) (hu : lu.toFinset = Xᶜ)
    {pre post : List (Ev D)} {x y : D.TV} (hxy : x ≠ y)
    (hM0 : ∀ e ∈ pre ++ [evH D (Head.a x), evQ D x, evH D (Head.a y), evQ D y],
      e ∈ M D O lT lu)
    (h₀ : CombOK D (pre ++ evH D (Head.a x) :: evQ D x :: evH D (Head.a y) :: evQ D y :: post)) :
    Link D (pre ++ evH D (Head.a x) :: evQ D x :: evH D (Head.a y) :: evQ D y :: post)
      (pre ++ evH D (Head.a y) :: evQ D y :: evH D (Head.a x) :: evQ D x :: post) := by
  have hM : ∀ L : List (Ev D), (∀ e ∈ L, e ∈ pre ∨ e = evH D (Head.a x) ∨ e = evQ D x ∨
      e = evH D (Head.a y) ∨ e = evQ D y) → ∀ e ∈ L, e ∈ M D O lT lu := by
    intro L hL e he
    apply hM0
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact hL e he
  have c1 : (CVar.hd (Head.a x), false) ∈ goal D pre :=
    (h₀.2.2.2.2.1 pre _ _ rfl).1
  have c2 : (CVar.hd (Head.a y), false) ∈ goal D ((pre ++ [evH D (Head.a x)]) ++ [evQ D x]) := by
    have := (h₀.2.2.2.2.1 (pre ++ [evH D (Head.a x), evQ D x]) (evH D (Head.a y)) (evQ D y :: post)
      (by simp)).1
    rw [List.append_assoc]; exact this
  have hay : (CVar.hd (Head.a y), false) ∈ goal D pre :=
    mem_goal_of_snoc D (mem_goal_of_snoc D c2 (not_side_Q D x _ rfl)) (hd_not_a D x y)
  -- step 1: Q_x ↔ a_y
  have l1 := uswap D hD hO hXℓ hT hu (A := pre ++ [evH D (Head.a x)])
    (B := evQ D y :: post) (e₁ := evQ D x) (e₂ := evH D (Head.a y))
    (by rw [List.append_assoc]; exact h₀)
    (hM _ (by intro e he; simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at he; tauto))
    (mem_goal_snoc D hay (by simp [evH, Ne.symm hxy]))
    (mem_goal_snoc D (mem_goal_side D (fx_mem_a D x) (by simp [evH])) (by simp [evH, evQ]))
    (fun h => not_side_Q D x _ rfl (Finset.mem_of_mem_erase h))
    (fun h => fy_not_a D (Ne.symm hxy) (Finset.mem_of_mem_erase h))
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at l1
  -- step 2: a_x ↔ a_y
  have l2 := uswap D hD hO hXℓ hT hu (A := pre)
    (B := evQ D x :: evQ D y :: post) (e₁ := evH D (Head.a x)) (e₂ := evH D (Head.a y))
    l1.2.1
    (hM _ (by intro e he; simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at he; tauto))
    hay (mem_goal_snoc D c1 (by simp [evH, hxy]))
    (fun h => hd_not_a D x y (Finset.mem_of_mem_erase h))
    (fun h => hd_not_a D y x (Finset.mem_of_mem_erase h))
  -- step 3: Q_x ↔ Q_y
  have fy1 : (CVar.f y, false) ∈ goal D (pre ++ [evH D (Head.a y)]) :=
    mem_goal_side D (fx_mem_a D y) (by simp [evH])
  have fy2 : (CVar.f y, false) ∈ goal D (pre ++ [evH D (Head.a y), evH D (Head.a x)]) := by
    have := mem_goal_snoc D fy1 (e := evH D (Head.a x)) (by simp [evH])
    rw [List.append_assoc] at this; exact this
  have fx2 : (CVar.f x, false) ∈ goal D (pre ++ [evH D (Head.a y), evH D (Head.a x)]) := by
    have := mem_goal_side D (p := pre ++ [evH D (Head.a y)]) (fx_mem_a D x) (by simp [evH])
    rw [List.append_assoc] at this; exact this
  have l3 := uswap D hD hO hXℓ hT hu (A := pre ++ [evH D (Head.a y), evH D (Head.a x)])
    (B := post) (e₁ := evQ D x) (e₂ := evQ D y)
    (by rw [List.append_assoc]; exact l2.2.1)
    (hM _ (by intro e he; simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at he; tauto))
    fy2 (mem_goal_snoc D fx2 (by simp [evQ, hxy]))
    (fun h => not_side_Q D x _ rfl (Finset.mem_of_mem_erase h))
    (fun h => not_side_Q D y _ rfl (Finset.mem_of_mem_erase h))
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at l3
  -- step 4: a_x ↔ Q_y
  have l4 := uswap D hD hO hXℓ hT hu (A := pre ++ [evH D (Head.a y)])
    (B := evQ D x :: post) (e₁ := evH D (Head.a x)) (e₂ := evQ D y)
    (by rw [List.append_assoc]; exact l3.2.1)
    (hM _ (by intro e he; simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at he; tauto))
    fy1 (mem_goal_snoc D (mem_goal_snoc D c1 (by simp [evH, hxy])) (by simp [evH, evQ]))
    (fun h => fy_not_a D hxy (Finset.mem_of_mem_erase h))
    (fun h => not_side_Q D y _ rfl (Finset.mem_of_mem_erase h))
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at l4
  exact link_trans (link_trans (link_trans l1 l2) l3) l4

theorem sort_unsel (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hX : IsIndepSet D.J X) (hXℓ : D.ℓ ≤ X.card) {lT lu lu' ls lb : List D.TV}
    (hL : ListsFor D X lT lu ls lb) (hL' : ListsFor D X lT lu' ls lb) :
    Link D (canonL D O lT lu ls lb) (canonL D O lT lu' ls lb) := by
  obtain ⟨h1, hT, h3, h4, hn, hf, h7, h8⟩ := hL
  have hLp : ∀ l : List D.TV, l.Perm lu → ListsFor D X lT l ls lb := by
    intro l hl
    exact ⟨h1, hT, h3, h4, hl.nodup_iff.2 hn, (List.toFinset_eq_of_perm _ _ hl).trans hf, h7, h8⟩
  have hp' : lu'.Perm lu :=
    List.perm_of_nodup_nodup_toFinset_eq hL'.2.2.2.2.1 hn (hL'.2.2.2.2.2.1.trans hf.symm)
  refine perm_of_adjSwap (fun l l' => Link D (canonL D O lT l ls lb) (canonL D O lT l' ls lb))
    lu ?_ ?_ ?_ (List.Perm.refl lu) hp'
  · intro l hl
    exact link_refl (canon_ok D hD hO hX hXℓ (hLp l hl))
  · intro a b c _ _ _ hab hbc
    exact link_trans hab hbc
  · intro p x y t hl
    have hLl := hLp _ hl
    have h₀ := canon_ok D hD hO hX hXℓ hLl
    have hxy : x ≠ y := by
      have hnd := (hLl.2.2.2.2.1.sublist (List.sublist_append_right p _))
      intro h
      subst h
      exact (List.nodup_cons.1 hnd).1 (List.mem_cons_self ..)
    show Link D _ _
    unfold CombOK at h₀
    rw [canonL_unsel_split] at h₀ ⊢
    rw [canonL_unsel_split]
    refine unsel_block D hD hO hXℓ hT hLl.2.2.2.2.2.1 hxy ?_ h₀
    intro e he
    simp only [M, unselSeg, List.flatMap_append, List.flatMap_cons, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    tauto

end ReconfRes.Frozen.Dev.Q427d.PartS2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias sort_unsel := ReconfRes.Frozen.Dev.Q427d.PartS2.sort_unsel

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartS3
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### A generic goal swap from commutation -/
/-- (M1) inside a valid comb when the two events commute and have distinct pivots. -/
theorem link_swap_comm {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {e₁ e₂ : Event ι V}
    (h : CombValid inv S start F w s (pre ++ e₁ :: e₂ :: post))
    (h₁ : (e₂.pivot, false) ∉ (sideLabel inv e₁ e₁.prep.length).erase (e₁.pivot, true))
    (h₂ : (e₁.pivot, false) ∉ (sideLabel inv e₂ e₂.prep.length).erase (e₂.pivot, true))
    (hne : e₁.pivot ≠ e₂.pivot)
    (hw : (goalLabel inv start (pre ++ [e₂])).card ≤ w) :
    CombLink k F w s inv S start (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) := by
  have v1 := (h.2.2.2.2.1 pre e₁ (e₂ :: post) rfl).1
  have v2 := (h.2.2.2.2.1 (pre ++ [e₁]) e₂ post (by simp)).1
  rw [goalLabel_snoc] at v2
  unfold stepG at v2
  refine link_swap hk h ?_ ?_ hw ?_
  · rcases Finset.mem_union.1 v2 with hx | hx
    · exact absurd hx h₁
    · exact (Finset.mem_erase.1 hx).2
  · rw [goalLabel_snoc]
    unfold stepG
    refine Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, v1⟩)
    intro he
    exact hne (Prod.mk.inj he).1
  · simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact step_comm _ _ _ _ h₁ h₂

end ReconfRes.Frozen.Dev.Q427d.PartS3
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartS3
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Side clauses and bag steps (as in Part K2) -/
theorem mem_foldl_erase {V : Type} [DecidableEq V] {ι : Type} (x : Literal V)
    (us : List (ι × V)) (c : Clause V) :
    x ∈ us.foldl (fun c u => c.erase (u.2, false)) c ↔ x ∈ c ∧ ∀ u ∈ us, x ≠ (u.2, false) := by
  induction us generalizing c with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, ih, Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

theorem f_mem_Ch (h : Head D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ D.Ch h ↔ CVar.f v ∈ D.Xh h := by
  simp [ConstrData.Ch]

theorem side_evH (h : Head D.TV) :
    sideLabel D.inv (evH D h) (evH D h).prep.length = D.Ch h := by
  simp [sideLabel, evH, ConstrData.inv]

theorem side_evQ (w : D.TV) :
    sideLabel D.inv (evQ D w) (evQ D w).prep.length = {(CVar.f w, true)} := by
  simp [sideLabel, evQ, ConstrData.inv]

theorem f_mem_side_evT (l : List D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ sideLabel D.inv (evT D l) (evT D l).prep.length ↔ v ∉ l := by
  simp only [sideLabel, evT, List.take_length]
  rw [mem_foldl_erase]
  have h1 : (CVar.f v, false) ∈ D.inv (Src.C Head.T) := by
    simp [ConstrData.inv, f_mem_Ch, ConstrData.Xh]
  constructor
  · rintro ⟨_, h⟩ hv
    exact h _ (List.mem_map_of_mem hv) rfl
  · intro hv
    refine ⟨h1, fun u hu he => ?_⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    simp only [Prod.mk.injEq, CVar.f.injEq, and_true] at he
    exact hv (he ▸ hw)

theorem bag_nil : bag D [] = ∅ := by
  ext v
  rw [mem_bag]
  simp

theorem bag_evT (p : List (Ev D)) (l : List D.TV) (v : D.TV) :
    v ∈ bag D (p ++ [evT D l]) ↔ v ∉ l ∨ v ∈ bag D p := by
  rw [mem_bag_snoc, f_mem_side_evT]
  simp [evT]

theorem bag_evH (p : List (Ev D)) (h : Head D.TV) (v : D.TV) :
    v ∈ bag D (p ++ [evH D h]) ↔ CVar.f v ∈ D.Xh h ∨ v ∈ bag D p := by
  rw [mem_bag_snoc, side_evH, f_mem_Ch]
  simp [evH]

theorem bag_evQ (p : List (Ev D)) (w v : D.TV) :
    v ∈ bag D (p ++ [evQ D w]) ↔ v ∈ bag D p ∧ v ≠ w := by
  rw [mem_bag_snoc, side_evQ]
  simp [evQ, eq_comm]

/-- An event that neither adds nor removes facts. -/
def Neutral (e : Ev D) : Prop :=
  (∀ v, (CVar.f v, false) ∉ sideLabel D.inv e e.prep.length) ∧ ∀ v, e.pivot ≠ CVar.f v

theorem bag_neutral {e : Ev D} (he : Neutral D e) (p : List (Ev D)) :
    bag D (p ++ [e]) = bag D p := by
  ext v
  rw [mem_bag_snoc]
  simp [he.1 v, he.2 v]

theorem bag_neutral_list {L : List (Ev D)} (hL : ∀ e ∈ L, Neutral D e) (pre : List (Ev D)) :
    bag D (pre ++ L) = bag D pre := by
  induction L generalizing pre with
  | nil => simp
  | cons x L ih =>
    have hx := hL x (by simp)
    rw [← List.singleton_append, ← List.append_assoc, ih (fun e he => hL e (by simp [he])),
      bag_neutral D hx]

theorem neutral_evH {h : Head D.TV} (hh : ∀ v, CVar.f v ∉ D.Xh h) : Neutral D (evH D h) := by
  refine ⟨fun v => ?_, fun v => by simp [evH]⟩
  rw [side_evH, f_mem_Ch]
  exact hh v

theorem inner1_sub {h : Head D.TV} (hh : h ∈ D.inner1) :
    ∃ p, h = Head.i1 p ∧ p ∈ D.t1.internalPaths ∧ p ≠ [] := by
  simp only [ConstrData.inner1, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hh
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hh
  exact ⟨p, rfl, hp, hne⟩

theorem inner2_sub {h : Head D.TV} (hh : h ∈ D.inner2) :
    ∃ p, h = Head.i2 p ∧ p ∈ D.t2.internalPaths ∧ p ≠ [] := by
  simp only [ConstrData.inner2, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hh
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hh
  exact ⟨p, rfl, hp, hne⟩

theorem neutral_ord1 {O : D.CanonOrders} (hO : O.Valid) : ∀ e ∈ seg1 D O, Neutral D e := by
  intro e he
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 he
  obtain ⟨p, rfl, -⟩ := inner1_sub D (by rw [← hO.2.1]; simpa using hh)
  exact neutral_evH D (fun v => by simp [ConstrData.Xh])

theorem neutral_seg2 {O : D.CanonOrders} (hO : O.Valid) : ∀ e ∈ seg2 D O, Neutral D e := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact neutral_evH D (fun v => by simp [ConstrData.Xh])
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 he
  obtain ⟨p, rfl, -⟩ := inner2_sub D (by rw [← hO.2.2.2.2.1]; simpa using hh)
  exact neutral_evH D (fun v => by simp [ConstrData.Xh])

theorem Xh_a (v : D.TV) : D.Xh (Head.a v) = {CVar.f v} := rfl

theorem Xh_b (v : D.TV) : D.Xh (Head.b v) = {CVar.f v} := rfl

theorem unselSeg_cons (v : D.TV) (l : List D.TV) :
    unselSeg D (v :: l) = [evH D (Head.a v), evQ D v] ++ unselSeg D l := by
  simp [unselSeg]

theorem selSeg_cons (v : D.TV) (l : List D.TV) :
    selSeg D (v :: l) = [evH D (Head.a v), evH D (Head.b v), evQ D v] ++ selSeg D l := by
  simp [selSeg]

theorem bag_unsel (lu : List D.TV) (hnd : lu.Nodup) (B : Finset D.TV) (hB : ∀ v ∈ lu, v ∉ B)
    (pre : List (Ev D)) (hbag : bag D pre = B ∪ lu.toFinset) :
    bag D (pre ++ unselSeg D lu) = B := by
  induction lu generalizing pre with
  | nil => simpa [unselSeg] using hbag
  | cons v lu ih =>
    rw [List.nodup_cons] at hnd
    have hvB : v ∉ B := hB v (by simp)
    have h1 : bag D (pre ++ [evH D (Head.a v)]) = bag D pre := by
      ext x
      rw [bag_evH, Xh_a, hbag]
      simp only [Finset.mem_singleton, CVar.f.injEq, Finset.mem_union, List.mem_toFinset,
        List.mem_cons]
      constructor
      · rintro (rfl | h) <;> tauto
      · tauto
    have h2 : bag D (pre ++ [evH D (Head.a v), evQ D v]) = B ∪ lu.toFinset := by
      ext x
      have : pre ++ [evH D (Head.a v), evQ D v] = (pre ++ [evH D (Head.a v)]) ++ [evQ D v] := by
        simp
      rw [this, bag_evQ, h1, hbag]
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro ⟨h | rfl | h, hne⟩
        · exact Or.inl h
        · exact absurd rfl hne
        · exact Or.inr h
      · rintro (h | h)
        · exact ⟨Or.inl h, fun he => hvB (he ▸ h)⟩
        · exact ⟨Or.inr (Or.inr h), fun he => hnd.1 (he ▸ h)⟩
    rw [unselSeg_cons, ← List.append_assoc]
    exact ih hnd.2 (fun x hx => hB x (by simp [hx])) _ h2

theorem bag_sel (ls : List D.TV) (pre : List (Ev D)) (hbag : bag D pre = ∅) :
    bag D (pre ++ selSeg D ls) = ∅ := by
  induction ls generalizing pre with
  | nil => simpa [selSeg] using hbag
  | cons v ls ih =>
    have h1 : bag D (pre ++ [evH D (Head.a v)]) = {v} := by
      ext x; rw [bag_evH, Xh_a, hbag]; simp
    have h2 : bag D (pre ++ [evH D (Head.a v)] ++ [evH D (Head.b v)]) = {v} := by
      ext x; rw [bag_evH, Xh_b, h1]; simp
    have h3 : bag D (pre ++ [evH D (Head.a v)] ++ [evH D (Head.b v)] ++ [evQ D v]) = ∅ := by
      ext x; rw [bag_evQ, h2]; simp
    have h3' : bag D (pre ++ [evH D (Head.a v), evH D (Head.b v), evQ D v]) = ∅ := by
      rw [← h3]; simp
    rw [selSeg_cons, ← List.append_assoc]
    exact ih _ h3'

/-! ### The prefix before two adjacent selected packets -/
/-- Everything before the selected packets of `p ++ u :: w :: t`. -/
def preS (O : D.CanonOrders) (lT lu p : List D.TV) : List (Ev D) :=
  [evT D lT] ++ seg1 D O ++ unselSeg D lu ++ seg2 D O ++ selSeg D p

/-- Everything after them. -/
def postS (O : D.CanonOrders) (t lb : List D.TV) : List (Ev D) :=
  selSeg D t ++ prepSeg D lb ++ tailSeg D O

/-- A selected packet. -/
def pk (v : D.TV) : List (Ev D) := [evH D (Head.a v), evH D (Head.b v), evQ D v]

theorem canonL_split (O : D.CanonOrders) (lT lu p t lb : List D.TV) (u w : D.TV) :
    canonL D O lT lu (p ++ u :: w :: t) lb =
      preS D O lT lu p ++ pk D u ++ pk D w ++ postS D O t lb := by
  simp [canonL, canonHead, preS, postS, pk, selSeg, List.flatMap_append]

theorem bag_preS {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV} {lT lu ls lb p : List D.TV}
    (hL : ListsFor D X lT lu ls lb) : bag D (preS D O lT lu p) = ∅ := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ := hL
  have hT : bag D [evT D lT] = Xᶜ := by
    ext v
    have := bag_evT D [] lT v
    rw [List.nil_append, bag_nil] at this
    rw [this, ← a2]; simp
  have h1 : bag D ([evT D lT] ++ seg1 D O) = Xᶜ := by
    rw [bag_neutral_list D (neutral_ord1 D hO), hT]
  have h2 : bag D ([evT D lT] ++ seg1 D O ++ unselSeg D lu) = ∅ :=
    bag_unsel D lu c1 ∅ (fun v _ => Finset.notMem_empty v) _
      (by rw [h1, Finset.empty_union, c2])
  have h3 : bag D ([evT D lT] ++ seg1 D O ++ unselSeg D lu ++ seg2 D O) = ∅ := by
    rw [bag_neutral_list D (neutral_seg2 D hO), h2]
  exact bag_sel D p _ h3

theorem pivA_evH (h : Head D.TV) : (evH D h).pivot ≠ CVar.A := by simp [evH]

theorem pivA_evQ (v : D.TV) : (evQ D v).pivot ≠ CVar.A := by simp [evQ]

theorem notA_preS {O : D.CanonOrders} (hO : O.Valid) (lT lu p : List D.TV) :
    ∀ e ∈ preS D O lT lu p, e.pivot ≠ CVar.A := by
  intro e he
  simp only [preS, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · simp only [List.mem_singleton] at he; subst he; simp [evT]
  · obtain ⟨h, -, rfl⟩ := List.mem_map.1 he; exact pivA_evH D h
  · obtain ⟨v, -, he⟩ := List.mem_flatMap.1 he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact pivA_evH D _
    · exact pivA_evQ D _
  · rcases List.mem_cons.1 he with rfl | he
    · exact pivA_evH D _
    · obtain ⟨h, -, rfl⟩ := List.mem_map.1 he; exact pivA_evH D h
  · obtain ⟨v, -, he⟩ := List.mem_flatMap.1 he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact pivA_evH D _
    · exact pivA_evH D _
    · exact pivA_evQ D _

/-! ### Moving one event left across a commuting block -/
/-- Events touching only the facts `u`, `w`, never `A`. -/
def Good (u w : D.TV) (e : Ev D) : Prop :=
  e.pivot ≠ CVar.A ∧
    ∀ v, (CVar.f v, false) ∈ sideLabel D.inv e e.prep.length → v = u ∨ v = w

/-- Two events that commute with distinct pivots. -/
def Comm (x e : Ev D) : Prop :=
  (e.pivot, false) ∉ (sideLabel D.inv x x.prep.length).erase (x.pivot, true) ∧
    (x.pivot, false) ∉ (sideLabel D.inv e e.prep.length).erase (e.pivot, true) ∧
    x.pivot ≠ e.pivot

theorem bag_sub {u w : D.TV} {pre : List (Ev D)} (h0 : bag D pre = ∅) (m : List (Ev D))
    (hm : ∀ e ∈ m, Good D u w e) : bag D (pre ++ m) ⊆ {u, w} := by
  induction m using List.reverseRecOn with
  | nil => simp [h0]
  | append_singleton m e ih =>
    intro v hv
    rw [← List.append_assoc, mem_bag_snoc] at hv
    rcases hv with hv | ⟨hv, -⟩
    · rcases (hm e (by simp)).2 v hv with rfl | rfl <;> simp
    · exact ih (fun x hx => hm x (by simp [hx])) hv

theorem q_pos (hD : D.Valid) : 1 ≤ D.q := by
  obtain ⟨h1, h2, h3, -⟩ := hD
  unfold ConstrData.q ConstrData.m ConstrData.ℓ
  have : D.b * (D.K + 1) ≤ D.b * D.n := Nat.mul_le_mul_left _ h3
  have hb : 1 ≤ D.b := by unfold ConstrData.b; omega
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

/-- One swap step of the sorting, inside a valid list. -/
theorem step_swap (hD : D.Valid) {pre post : List (Ev D)} {e₁ e₂ : Ev D}
    (h : CombOK D (pre ++ e₁ :: e₂ :: post))
    (hA : ∀ e ∈ pre ++ [e₁, e₂], e.pivot ≠ CVar.A) (hc : Comm D e₁ e₂)
    (hb : (bag D (pre ++ [e₂])).card ≤ 2) :
    Link D (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) := by
  have hs : Shape D (pre ++ [e₁, e₂]) :=
    shape_of_ok D hD (t := post) (by simpa using h) hA
  have hs' : Shape D (pre ++ [e₂]) :=
    shape_sublist D hs (List.Sublist.append_left (List.Sublist.cons _ (List.Sublist.refl _)) pre)
  have hq := q_pos D hD
  refine link_swap_comm (by norm_num) h hc.1 hc.2.1 hc.2.2 ?_
  show (goal D (pre ++ [e₂])).card ≤ D.W
  rw [card_goal_shape D hD hs']
  unfold ConstrData.W ConstrData.r
  split_ifs <;> omega

theorem cross (hD : D.Valid) {u w : D.TV} {pre : List (Ev D)} (h0 : bag D pre = ∅)
    (hpA : ∀ e ∈ pre, e.pivot ≠ CVar.A) (e : Ev D) (he : Good D u w e) (rest : List (Ev D)) :
    ∀ (xs m : List (Ev D)), (∀ x ∈ m, Good D u w x) → (∀ x ∈ xs, Good D u w x ∧ Comm D x e) →
      CombOK D (pre ++ m ++ xs ++ e :: rest) →
      Link D (pre ++ m ++ xs ++ e :: rest) (pre ++ m ++ e :: (xs ++ rest)) := by
  intro xs
  induction xs with
  | nil =>
    intro m _ _ hok
    simpa [Link, CombOK] using link_refl hok
  | cons x xs ih =>
    intro m hm hxs hok
    have hx := hxs x (by simp)
    have h1 := ih (m ++ [x]) (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact hm y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact hx.1)
      (fun y hy => hxs y (by simp [hy])) (by simpa using hok)
    have hok2 : CombOK D ((pre ++ m) ++ x :: e :: (xs ++ rest)) := by
      have := h1.2.1
      simpa [CombOK] using this
    have h2 := step_swap D hD hok2 (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · rcases List.mem_append.1 hy with hy | hy
          · exact hpA y hy
          · exact (hm y hy).1
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact hx.1.1
          · exact he.1) hx.2 (by
        have hsub := bag_sub D h0 (m ++ [e]) (fun y hy => by
          rcases List.mem_append.1 hy with hy | hy
          · exact hm y hy
          · simp only [List.mem_singleton] at hy; subst hy; exact he)
        rw [List.append_assoc]
        exact (Finset.card_le_card hsub).trans Finset.card_le_two)
    have h1' : Link D (pre ++ m ++ (x :: xs) ++ e :: rest)
        ((pre ++ m) ++ x :: e :: (xs ++ rest)) := by simpa using h1
    have h2' : Link D ((pre ++ m) ++ x :: e :: (xs ++ rest))
        (pre ++ m ++ e :: (x :: xs ++ rest)) := by simpa using h2
    exact link_trans h1' h2'

/-! ### The adjacent exchange of two selected packets -/
theorem good_pk {u w : D.TV} : ∀ e ∈ pk D u, Good D u w e := by
  intro e he
  simp only [pk, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;>
    refine ⟨by simp [evH, evQ], fun v hv => ?_⟩
  · rw [side_evH, f_mem_Ch, Xh_a] at hv; simp at hv; exact Or.inl hv
  · rw [side_evH, f_mem_Ch, Xh_b] at hv; simp at hv; exact Or.inl hv
  · rw [side_evQ] at hv; simp at hv

theorem good_pk' {u w : D.TV} : ∀ e ∈ pk D w, Good D u w e := by
  intro e he
  obtain ⟨h1, h2⟩ := good_pk D (u := w) (w := u) e he
  exact ⟨h1, fun v hv => (h2 v hv).symm⟩

theorem comm_pk {u w : D.TV} (huw : u ≠ w) (hadj : ¬D.J.Adj u w) (hadj' : ¬D.J.Adj w u) :
    ∀ x ∈ pk D u, ∀ e ∈ pk D w, Comm D x e := by
  intro x hx e he
  simp only [pk, List.mem_cons, List.not_mem_nil, or_false] at hx he
  rcases hx with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl <;>
    simp [Comm, sideLabel, ConstrData.inv, evH, evQ, ConstrData.Ch, ConstrData.deps,
      ConstrData.Xh, huw, hadj, hadj', Ne.symm huw] <;>
    (intro a b hab he; rw [he] at hab; first | exact hadj hab | exact hadj' hab)

theorem swap_adj (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    {lT lu ls lb p t : List D.TV} {u w : D.TV} (hL : ListsFor D X lT lu ls lb)
    (huw : u ≠ w) (hadj : ¬D.J.Adj u w) (hadj' : ¬D.J.Adj w u)
    (hok : CombOK D (canonL D O lT lu (p ++ u :: w :: t) lb)) :
    Link D (canonL D O lT lu (p ++ u :: w :: t) lb) (canonL D O lT lu (p ++ w :: u :: t) lb) := by
  rw [canonL_split] at hok ⊢
  rw [canonL_split]
  have h0 := bag_preS D hO (p := p) hL
  have hpA := notA_preS D hO lT lu p
  have hc := comm_pk D huw hadj hadj'
  have hgu := good_pk D (u := u) (w := w)
  have hgw := good_pk' D (u := u) (w := w)
  have hxs : ∀ e ∈ pk D w, ∀ x ∈ pk D u, Good D u w x ∧ Comm D x e :=
    fun e he x hx => ⟨hgu x hx, hc x hx e he⟩
  set P := preS D O lT lu p
  set Q := postS D O t lb
  -- move a_w
  have s1 := cross D hD h0 hpA (evH D (Head.a w)) (hgw _ (by simp [pk]))
    ([evH D (Head.b w), evQ D w] ++ Q) (pk D u) [] (by simp)
    (hxs _ (by simp [pk])) (by simpa [pk] using hok)
  have s2 := cross D hD h0 hpA (evH D (Head.b w)) (hgw _ (by simp [pk]))
    ([evQ D w] ++ Q) (pk D u) [evH D (Head.a w)]
    (fun x hx => hgw x (by simp at hx; simp [pk, hx]))
    (hxs _ (by simp [pk])) (by simpa [pk, CombOK] using s1.2.1)
  have s3 := cross D hD h0 hpA (evQ D w) (hgw _ (by simp [pk]))
    Q (pk D u) [evH D (Head.a w), evH D (Head.b w)]
    (fun x hx => hgw x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [pk]))
    (hxs _ (by simp [pk])) (by simpa [pk, CombOK] using s2.2.1)
  have t1 : Link D (P ++ pk D u ++ pk D w ++ Q)
      (P ++ [evH D (Head.a w)] ++ pk D u ++ evH D (Head.b w) :: ([evQ D w] ++ Q)) := by
    simpa [pk] using s1
  have t2 : Link D (P ++ [evH D (Head.a w)] ++ pk D u ++ evH D (Head.b w) :: ([evQ D w] ++ Q))
      (P ++ [evH D (Head.a w), evH D (Head.b w)] ++ pk D u ++ evQ D w :: Q) := by
    simpa [pk] using s2
  have t3 : Link D (P ++ [evH D (Head.a w), evH D (Head.b w)] ++ pk D u ++ evQ D w :: Q)
      (P ++ pk D w ++ pk D u ++ Q) := by
    simpa [pk] using s3
  exact link_trans (link_trans t1 t2) t3

/-- A permutation of a nodup list with the same finset. -/
theorem nodup_toFinset_of_perm {α : Type} [DecidableEq α] {l l₀ : List α} (hp : l.Perm l₀)
    (hn : l₀.Nodup) : l.Nodup ∧ l.toFinset = l₀.toFinset :=
  ⟨hp.nodup_iff.2 hn, List.toFinset_eq_of_perm _ _ hp⟩

theorem sort_sel (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hX : IsIndepSet D.J X) (hXℓ : D.ℓ ≤ X.card) {lT lu ls ls' lb : List D.TV}
    (hL : ListsFor D X lT lu ls lb) (hL' : ListsFor D X lT lu ls' lb) :
    Link D (canonL D O lT lu ls lb) (canonL D O lT lu ls' lb) := by
  obtain ⟨h1, h2, hn, hf, h5, h6, h7, h8⟩ := hL
  have hLp : ∀ l : List D.TV, l.Perm ls → ListsFor D X lT lu l lb := by
    intro l hl
    obtain ⟨a, b⟩ := nodup_toFinset_of_perm hl hn
    exact ⟨h1, h2, a, b.trans hf, h5, h6, h7, h8⟩
  have hp' : ls'.Perm ls :=
    List.perm_of_nodup_nodup_toFinset_eq hL'.2.2.1 hn (hL'.2.2.2.1.trans hf.symm)
  refine perm_of_adjSwap (fun l l' => Link D (canonL D O lT lu l lb) (canonL D O lT lu l' lb))
    ls ?_ ?_ ?_ (List.Perm.refl ls) hp'
  · intro l hl
    exact link_refl (canon_ok D hD hO hX hXℓ (hLp l hl))
  · intro a b c _ _ _ hab hbc
    exact link_trans hab hbc
  · intro p x y t hl
    have hL1 := hLp _ hl
    have hxy : x ≠ y := by
      have := hL1.2.2.1
      simp [List.nodup_append] at this
      tauto
    have hxX : x ∈ X := by rw [← hL1.2.2.2.1]; simp
    have hyX : y ∈ X := by rw [← hL1.2.2.2.1]; simp
    exact swap_adj D hD hO hL1 hxy (hX x hxX y hyX) (hX y hyX x hxX)
      (canon_ok D hD hO hX hXℓ hL1)

end ReconfRes.Frozen.Dev.Q427d.PartS3
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias sort_sel := ReconfRes.Frozen.Dev.Q427d.PartS3.sort_sel

/-! ## Part D: deleting a selected vertex `v` (Y = insert v X selected, ending with X)

Fixed: `lx` the privT order of `X`, `ls` the sel order of `X`, `lu`, `lb` orders of
`(insert v X)ᶜ`. -/
/-- The hypotheses of the deletion phases. -/
def DelSetting (O : D.CanonOrders) (X : Finset D.TV) (v : D.TV) (lx lu ls lb : List D.TV) :
    Prop :=
  D.Valid ∧ O.Valid ∧ v ∉ X ∧ IsIndepSet D.J (insert v X) ∧ D.ℓ ≤ X.card ∧
  ListsFor D (insert v X) (lx ++ [v]) lu (v :: ls) lb

/-- Start: the canonical list of `insert v X` with `v` last at `T` and first among the packets. -/
def delL0 (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) : List (Ev D) :=
  canonL D O (lx ++ [v]) lu (v :: ls) lb

/-- After splitting `P_v` off `T`. -/
def delL1 (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) : List (Ev D) :=
  [evT D lx, evP D v] ++ seg1 D O ++ unselSeg D lu ++ seg2 D O ++ selSeg D (v :: ls) ++
    prepSeg D lb ++ tailSeg D O

/-- `P_v` carried to just before `U`. -/
def delL1' (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) : List (Ev D) :=
  [evT D lx] ++ seg1 D O ++ unselSeg D lu ++ [evP D v] ++ seg2 D O ++ selSeg D (v :: ls) ++
    prepSeg D lb ++ tailSeg D O

/-- `P_v` carried to just before `a_v`. -/
def delL2 (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) : List (Ev D) :=
  [evT D lx] ++ seg1 D O ++ unselSeg D lu ++ seg2 D O ++ [evP D v] ++ selSeg D (v :: ls) ++
    prepSeg D lb ++ tailSeg D O

/-- After the transfer `P, a, b, Q ↦ a, Q, b[P]`. -/
def delL3 (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) : List (Ev D) :=
  [evT D lx] ++ seg1 D O ++ unselSeg D lu ++ seg2 D O ++
    [evH D (Head.a v), evQ D v, evBP D v] ++ selSeg D ls ++ prepSeg D lb ++ tailSeg D O

/-- The pair `a_v, Q_v` carried left to just after `U`. -/
def delL3' (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) : List (Ev D) :=
  [evT D lx] ++ seg1 D O ++ unselSeg D lu ++ [evH D Head.U, evH D (Head.a v), evQ D v] ++
    O.ord2.map (evH D) ++ [evBP D v] ++ selSeg D ls ++ prepSeg D lb ++ tailSeg D O

/-- The pair `a_v, Q_v` carried left to the end of the unselected batch. -/
def delL4 (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) : List (Ev D) :=
  [evT D lx] ++ seg1 D O ++ unselSeg D (lu ++ [v]) ++ seg2 D O ++ [evBP D v] ++ selSeg D ls ++
    prepSeg D lb ++ tailSeg D O

/-- End: the canonical list of `X`. -/
def delL5 (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) : List (Ev D) :=
  canonL D O lx (lu ++ [v]) ls (v :: lb)

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### A generic goal swap from commutation (as in Part S3) -/
/-- (M1) inside a valid comb when the two events commute and have distinct pivots. -/
theorem link_swap_comm {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {e₁ e₂ : Event ι V}
    (h : CombValid inv S start F w s (pre ++ e₁ :: e₂ :: post))
    (h₁ : (e₂.pivot, false) ∉ (sideLabel inv e₁ e₁.prep.length).erase (e₁.pivot, true))
    (h₂ : (e₁.pivot, false) ∉ (sideLabel inv e₂ e₂.prep.length).erase (e₂.pivot, true))
    (hne : e₁.pivot ≠ e₂.pivot)
    (hw : (goalLabel inv start (pre ++ [e₂])).card ≤ w) :
    CombLink k F w s inv S start (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) := by
  have v1 := (h.2.2.2.2.1 pre e₁ (e₂ :: post) rfl).1
  have v2 := (h.2.2.2.2.1 (pre ++ [e₁]) e₂ post (by simp)).1
  rw [goalLabel_snoc] at v2
  unfold stepG at v2
  refine link_swap hk h ?_ ?_ hw ?_
  · rcases Finset.mem_union.1 v2 with hx | hx
    · exact absurd hx h₁
    · exact (Finset.mem_erase.1 hx).2
  · rw [goalLabel_snoc]
    unfold stepG
    refine Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, v1⟩)
    intro he
    exact hne (Prod.mk.inj he).1
  · simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact step_comm _ _ _ _ h₁ h₂

end ReconfRes.Frozen.Dev.Q427d.PartD1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Side clauses and bags (as in Parts S2, S3) -/
theorem card_TV : Fintype.card D.TV = D.m := by
  simp [ConstrData.m, ConstrData.TV, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

theorem mem_foldl_erase {V : Type} [DecidableEq V] {ι : Type} (x : Literal V)
    (us : List (ι × V)) (c : Clause V) :
    x ∈ us.foldl (fun c u => c.erase (u.2, false)) c ↔ x ∈ c ∧ ∀ u ∈ us, x ≠ (u.2, false) := by
  induction us generalizing c with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, ih, Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

theorem f_mem_Ch (h : Head D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ D.Ch h ↔ CVar.f v ∈ D.Xh h := by
  simp [ConstrData.Ch]

theorem side_evH (h : Head D.TV) :
    sideLabel D.inv (evH D h) (evH D h).prep.length = D.Ch h := by
  simp [sideLabel, evH, ConstrData.inv]

theorem side_evQ (w : D.TV) :
    sideLabel D.inv (evQ D w) (evQ D w).prep.length = {(CVar.f w, true)} := by
  simp [sideLabel, evQ, ConstrData.inv]

theorem side_evP (w : D.TV) :
    sideLabel D.inv (evP D w) (evP D w).prep.length = {(CVar.f w, true)} := by
  simp [sideLabel, evP, ConstrData.inv]

theorem f_mem_side_evT (l : List D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ sideLabel D.inv (evT D l) (evT D l).prep.length ↔ v ∉ l := by
  simp only [sideLabel, evT, List.take_length]
  rw [mem_foldl_erase]
  have h1 : (CVar.f v, false) ∈ D.inv (Src.C Head.T) := by
    simp [ConstrData.inv, f_mem_Ch, ConstrData.Xh]
  constructor
  · rintro ⟨_, h⟩ hv
    exact h _ (List.mem_map_of_mem hv) rfl
  · intro hv
    refine ⟨h1, fun u hu he => ?_⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    simp only [Prod.mk.injEq, CVar.f.injEq, and_true] at he
    exact hv (he ▸ hw)

theorem T_mem_heads : Head.T ∈ D.heads := by simp [ConstrData.heads]

/-! ### The events of the first phase -/
/-- The events crossed by `P_v`: first-tree heads and unselected pairs. -/
def Cls0 (lu : List D.TV) (e : Ev D) : Prop :=
  (∃ p, e = evH D (Head.i1 p)) ∨ ∃ u ∈ lu, e = evH D (Head.a u) ∨ e = evQ D u

/-- The events before `U` in the lists of D1/D2a. -/
def Cls (lx lu : List D.TV) (v : D.TV) (e : Ev D) : Prop :=
  e = evT D lx ∨ e = evP D v ∨ Cls0 D lu e

theorem width_of_shape (hD : D.Valid) {X : Finset D.TV} (hXℓ : D.ℓ ≤ X.card)
    {lx lu : List D.TV} {v : D.TV} (hX : X ⊆ lx.toFinset) (hu : lu.toFinset ⊆ Xᶜ)
    {P : List (Ev D)} (hsh : Shape D P) (hP : ∀ e ∈ P, Cls D lx lu v e) :
    (goal D P).card ≤ D.W := by
  rw [card_goal_shape D hD hsh]
  have hU : Head.U ∉ expd D P := by
    simp only [expd, Finset.mem_filter, not_and, not_exists]
    intro _ e he hpiv
    rcases hP e he with rfl | rfl | ⟨p, rfl⟩ | ⟨u, _, rfl | rfl⟩ <;>
      simp [evT, evP, evH, evQ] at hpiv
  rw [if_neg hU]
  have hb : bag D P ⊆ Xᶜ := by
    intro w hw
    rw [mem_bag] at hw
    obtain ⟨p₁, e, t₁, hp, hmem, _⟩ := hw
    have he : e ∈ P := by rw [hp]; simp
    rw [Finset.mem_compl]
    rcases hP e he with rfl | rfl | ⟨p, rfl⟩ | ⟨u, hu', rfl | rfl⟩
    · rw [f_mem_side_evT] at hmem
      intro hwX
      exact hmem (by simpa using hX hwX)
    · rw [side_evP] at hmem; simp at hmem
    · rw [side_evH, f_mem_Ch] at hmem; simp [ConstrData.Xh] at hmem
    · rw [side_evH, f_mem_Ch] at hmem
      simp [ConstrData.Xh] at hmem
      subst hmem
      exact Finset.mem_compl.1 (hu (List.mem_toFinset.2 hu'))
    · rw [side_evQ] at hmem; simp at hmem
  have hc := Finset.card_le_card hb
  rw [Finset.card_compl, card_TV] at hc
  simp only [ConstrData.W, ConstrData.q, ConstrData.ℓ] at hc hXℓ ⊢
  omega

theorem shape_evT (lx : List D.TV) : Shape D [evT D lx] := by
  refine ⟨?_, by simp, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    refine Or.inl ⟨Head.T, T_mem_heads D, rfl, rfl, ?_⟩
    intro u hu
    simp only [evT, List.mem_map] at hu
    obtain ⟨w, _, rfl⟩ := hu
    exact ⟨w, Or.inl rfl, by simp [ConstrData.Xh]⟩
  · intro p₁ p₂ p₃ e₁ e₂ h d hp
    have := congrArg List.length hp
    simp at this
    omega

theorem facts {X : Finset D.TV} {v : D.TV} {lx lu ls lb : List D.TV} (hv : v ∉ X)
    (hL : ListsFor D (insert v X) (lx ++ [v]) lu (v :: ls) lb) :
    v ∉ lx ∧ X ⊆ lx.toFinset ∧ lu.toFinset ⊆ Xᶜ ∧ v ∉ lu := by
  obtain ⟨n1, f1, -, -, -, f3, -, -⟩ := hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [List.nodup_append] at n1
    exact n1.2.2 v h v (by simp) rfl
  · intro w hw
    have : w ∈ (lx ++ [v]).toFinset := by rw [f1]; exact Finset.mem_insert_of_mem hw
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset,
      List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty,
      or_false] at this
    rcases this with h | rfl
    · exact List.mem_toFinset.2 h
    · exact absurd hw hv
  · intro w hw
    rw [f3] at hw
    simp only [Finset.mem_compl, Finset.mem_insert, not_or] at hw ⊢
    exact hw.2
  · intro h
    have := List.mem_toFinset.2 h
    rw [f3] at this
    simp at this

/-! ### D1: splitting `P_v` off `T` -/
/-- The events after `T` in `delL0`/`delL1`. -/
def restL (O : D.CanonOrders) (lu ls lb : List D.TV) (v : D.TV) : List (Ev D) :=
  seg1 D O ++ unselSeg D lu ++ seg2 D O ++ selSeg D (v :: ls) ++ prepSeg D lb ++ tailSeg D O

theorem delL0_eq (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) :
    delL0 D O v lx lu ls lb = [] ++ (⟨Src.C Head.T, lx.map (fun w => (Src.P w, CVar.f w)) ++
      [(Src.P v, CVar.f v)], CVar.hd Head.T⟩ : Ev D) :: restL D O lu ls lb v := by
  simp [delL0, canonL, canonHead, evT, restL]

theorem delL1_eq (O : D.CanonOrders) (v : D.TV) (lx lu ls lb : List D.TV) :
    delL1 D O v lx lu ls lb = [] ++ (⟨Src.C Head.T, lx.map (fun w => (Src.P w, CVar.f w)),
      CVar.hd Head.T⟩ : Ev D) :: (⟨Src.P v, [], CVar.f v⟩ : Ev D) :: restL D O lu ls lb v := by
  simp [delL1, evT, evP, restL]

theorem f_not_Gc (v : D.TV) : (CVar.f v, false) ∉ D.Gc := by
  simp [ConstrData.Gc]

theorem split_heq (lx : List D.TV) (v : D.TV) :
    goal D ([] ++ [(⟨Src.C Head.T, lx.map (fun w => (Src.P w, CVar.f w)), CVar.hd Head.T⟩ : Ev D),
      ⟨Src.P v, [], CVar.f v⟩]) =
    goal D ([] ++ [(⟨Src.C Head.T, lx.map (fun w => (Src.P w, CVar.f w)) ++
      [(Src.P v, CVar.f v)], CVar.hd Head.T⟩ : Ev D)]) := by
  have hG := f_not_Gc D v
  ext l
  simp only [goalLabel_eq_foldl, List.nil_append, List.foldl_cons, List.foldl_nil, stepG,
    sideLabel, List.take_length, List.take_nil, List.foldl_nil, List.foldl_append,
    ConstrData.inv,
    Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2 | h2⟩)
    · exact absurd h2 h1
    · exact Or.inl ⟨h2.1, h1, h2.2⟩
    · exact Or.inr h2
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, Or.inl ⟨h1, h3⟩⟩
    · refine Or.inr ⟨?_, Or.inr ⟨h1, h2⟩⟩
      rintro rfl
      exact hG h2

/-- (D1) `T[.., P_v] ↦ T, P_v`. -/
theorem del_split {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV} {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) (hok : CombOK D (delL0 D O v lx lu ls lb)) :
    Link D (delL0 D O v lx lu ls lb) (delL1 D O v lx lu ls lb) := by
  obtain ⟨hD, hO, hv, hind, hXℓ, hL⟩ := hs
  obtain ⟨hvlx, hX, hu, hvlu⟩ := facts D hv hL
  unfold CombOK at hok
  rw [delL0_eq] at hok
  unfold Link
  rw [delL0_eq, delL1_eq]
  refine link_splitAfter (u := (Src.P v, CVar.f v)) (by norm_num) hok ?_ ?_ (split_heq D lx v)
  · show (CVar.f v, false) ∈ goal D ([] ++ [evT D lx])
    rw [goal, goalLabel_snoc]
    unfold stepG
    refine Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by simp [evT], ?_⟩)
    exact (f_mem_side_evT D lx v).2 hvlx
  · show (goal D ([] ++ [evT D lx])).card ≤ D.W
    rw [List.nil_append]
    refine width_of_shape D hD hXℓ (v := v) hX hu (shape_evT D lx) ?_
    intro e he
    simp only [List.mem_singleton] at he
    exact Or.inl he

end ReconfRes.Frozen.Dev.Q427d.PartD1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias del_split := ReconfRes.Frozen.Dev.Q427d.PartD1.del_split

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD1
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### D2a: carrying `P_v` across the first-tree heads and the unselected pairs -/
theorem cls0_pivot {lu : List D.TV} {e : Ev D} (he : Cls0 D lu e) : e.pivot ≠ CVar.A := by
  rcases he with ⟨p, rfl⟩ | ⟨u, _, rfl | rfl⟩ <;> simp [evH, evQ]

theorem cls0_ne {lu : List D.TV} {v : D.TV} (hvlu : v ∉ lu) {e : Ev D} (he : Cls0 D lu e) :
    CVar.f v ≠ e.pivot := by
  rcases he with ⟨p, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · simp [evH]
  · simp [evH]
  · simp only [evQ, ne_eq, CVar.f.injEq]
    rintro rfl
    exact hvlu hu

theorem cls0_side {lu : List D.TV} {v : D.TV} (hvlu : v ∉ lu) {e : Ev D} (he : Cls0 D lu e) :
    (CVar.f v, false) ∉ (sideLabel D.inv e e.prep.length).erase (e.pivot, true) := by
  intro hm
  have hm := Finset.mem_of_mem_erase hm
  rcases he with ⟨p, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · rw [side_evH, f_mem_Ch] at hm; simp [ConstrData.Xh] at hm
  · rw [side_evH, f_mem_Ch] at hm
    simp [ConstrData.Xh] at hm
    subst hm
    exact hvlu hu
  · rw [side_evQ] at hm; simp at hm

theorem evP_side (v : D.TV) (e : Ev D) :
    (e.pivot, false) ∉ (sideLabel D.inv (evP D v) (evP D v).prep.length).erase
      ((evP D v).pivot, true) := by
  rw [side_evP]; simp

/-- Carry `P_v` right across `N2`. -/
theorem carry (hD : D.Valid) {X : Finset D.TV} (hXℓ : D.ℓ ≤ X.card) {lx lu : List D.TV}
    {v : D.TV} (hvlu : v ∉ lu) (hX : X ⊆ lx.toFinset) (hu : lu.toFinset ⊆ Xᶜ)
    (R : List (Ev D)) :
    ∀ (N2 N1 : List (Ev D)), (∀ e ∈ N1 ++ N2, Cls0 D lu e) →
      CombOK D ([evT D lx] ++ N1 ++ evP D v :: (N2 ++ R)) →
      Link D ([evT D lx] ++ N1 ++ evP D v :: (N2 ++ R)) ([evT D lx] ++ (N1 ++ N2) ++ evP D v :: R)
  | [], N1, _, hok => by
    simp only [List.nil_append, List.append_nil]
    exact link_refl hok
  | e :: N2, N1, hN, hok => by
    have he : Cls0 D lu e := hN e (by simp)
    have hall : ∀ x ∈ [evT D lx] ++ N1 ++ [evP D v, e], x.pivot ≠ CVar.A ∧ Cls D lx lu v x := by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | hx) | rfl | rfl
      · exact ⟨by simp [evT], Or.inl rfl⟩
      · have := hN x (by simp [hx])
        exact ⟨cls0_pivot D this, Or.inr (Or.inr this)⟩
      · exact ⟨by simp [evP], Or.inr (Or.inl rfl)⟩
      · exact ⟨cls0_pivot D he, Or.inr (Or.inr he)⟩
    have hok' : CombOK D (([evT D lx] ++ N1 ++ [evP D v, e]) ++ (N2 ++ R)) := by
      simpa using hok
    have hsh := shape_sublist D (shape_of_ok D hD hok' (fun x hx => (hall x hx).1))
      (List.Sublist.append_left (List.sublist_cons_self (evP D v) [e]) ([evT D lx] ++ N1))
    have l1 : Link D (([evT D lx] ++ N1) ++ evP D v :: e :: (N2 ++ R))
        (([evT D lx] ++ N1) ++ e :: evP D v :: (N2 ++ R)) := by
      refine link_swap_comm (by norm_num) (by unfold CombOK at hok; simpa using hok) (evP_side D v e)
        (cls0_side D hvlu he) (cls0_ne D hvlu he) ?_
      refine width_of_shape D hD hXℓ (v := v) hX hu hsh ?_
      intro x hx
      have : x ∈ [evT D lx] ++ N1 ++ [evP D v, e] := by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto
      exact (hall x this).2
    have hN' : ∀ x ∈ (N1 ++ [e]) ++ N2, Cls0 D lu x := by
      intro x hx
      exact hN x (by simpa using hx)
    have l2 := carry hD hXℓ hvlu hX hu R N2 (N1 ++ [e]) hN' (by unfold CombOK; simpa using l1.2.1)
    have e1 : [evT D lx] ++ N1 ++ evP D v :: (e :: N2 ++ R) =
        ([evT D lx] ++ N1) ++ evP D v :: e :: (N2 ++ R) := by simp
    have e2 : [evT D lx] ++ (N1 ++ e :: N2) ++ evP D v :: R =
        [evT D lx] ++ (N1 ++ [e] ++ N2) ++ evP D v :: R := by simp
    have e3 : [evT D lx] ++ (N1 ++ [e]) ++ evP D v :: (N2 ++ R) =
        ([evT D lx] ++ N1) ++ e :: evP D v :: (N2 ++ R) := by simp
    rw [e1, e2]
    rw [e3] at l2
    exact link_trans l1 l2

theorem mem_ord1 {O : D.CanonOrders} (hO : O.Valid) {h : Head D.TV} (hh : h ∈ O.ord1) :
    ∃ p, h = Head.i1 p := by
  have : h ∈ D.inner1 := by rw [← hO.2.1]; exact List.mem_toFinset.2 hh
  simp only [ConstrData.inner1, Finset.mem_image] at this
  obtain ⟨p, _, rfl⟩ := this
  exact ⟨p, rfl⟩

theorem cls0_seg {O : D.CanonOrders} (hO : O.Valid) (lu : List D.TV) :
    ∀ e ∈ [] ++ (seg1 D O ++ unselSeg D lu), Cls0 D lu e := by
  intro e he
  simp only [List.nil_append, seg1, unselSeg, List.mem_append, List.mem_map,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ⟨h, hh, rfl⟩ | ⟨u, hu, he⟩
  · obtain ⟨p, rfl⟩ := mem_ord1 D hO hh
    exact Or.inl ⟨p, rfl⟩
  · exact Or.inr ⟨u, hu, he⟩

/-- (D2a) carry `P_v` right across the first-tree heads and the unselected pairs. -/
theorem del_carryP_pre {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV}
    {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) (hok : CombOK D (delL1 D O v lx lu ls lb)) :
    Link D (delL1 D O v lx lu ls lb) (delL1' D O v lx lu ls lb) := by
  obtain ⟨hD, hO, hv, hind, hXℓ, hL⟩ := hs
  obtain ⟨hvlx, hX, hu, hvlu⟩ := facts D hv hL
  set R := seg2 D O ++ selSeg D (v :: ls) ++ prepSeg D lb ++ tailSeg D O with hR
  have e0 : delL1 D O v lx lu ls lb =
      [evT D lx] ++ [] ++ evP D v :: ((seg1 D O ++ unselSeg D lu) ++ R) := by
    simp [delL1, hR]
  have e1 : delL1' D O v lx lu ls lb =
      [evT D lx] ++ ([] ++ (seg1 D O ++ unselSeg D lu)) ++ evP D v :: R := by
    simp [delL1', hR]
  rw [e0] at hok ⊢
  rw [e1]
  exact carry D hD hXℓ hvlu hX hu R _ [] (cls0_seg D hO lu) hok

end ReconfRes.Frozen.Dev.Q427d.PartD1
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias del_carryP_pre := ReconfRes.Frozen.Dev.Q427d.PartD1.del_carryP_pre

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### A generic goal swap from commutation (as in Part S3) -/
theorem link_swap_comm {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {e₁ e₂ : Event ι V}
    (h : CombValid inv S start F w s (pre ++ e₁ :: e₂ :: post))
    (h₁ : (e₂.pivot, false) ∉ (sideLabel inv e₁ e₁.prep.length).erase (e₁.pivot, true))
    (h₂ : (e₁.pivot, false) ∉ (sideLabel inv e₂ e₂.prep.length).erase (e₂.pivot, true))
    (hne : e₁.pivot ≠ e₂.pivot)
    (hw : (goalLabel inv start (pre ++ [e₂])).card ≤ w) :
    CombLink k F w s inv S start (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) := by
  have v1 := (h.2.2.2.2.1 pre e₁ (e₂ :: post) rfl).1
  have v2 := (h.2.2.2.2.1 (pre ++ [e₁]) e₂ post (by simp)).1
  rw [goalLabel_snoc] at v2
  unfold stepG at v2
  refine link_swap hk h ?_ ?_ hw ?_
  · rcases Finset.mem_union.1 v2 with hx | hx
    · exact absurd hx h₁
    · exact (Finset.mem_erase.1 hx).2
  · rw [goalLabel_snoc]
    unfold stepG
    refine Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, v1⟩)
    intro he
    exact hne (Prod.mk.inj he).1
  · simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact step_comm _ _ _ _ h₁ h₂

end ReconfRes.Frozen.Dev.Q427d.PartD2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Side clauses and bag steps (as in Parts K2, S3) -/
theorem mem_foldl_erase {V : Type} [DecidableEq V] {ι : Type} (x : Literal V)
    (us : List (ι × V)) (c : Clause V) :
    x ∈ us.foldl (fun c u => c.erase (u.2, false)) c ↔ x ∈ c ∧ ∀ u ∈ us, x ≠ (u.2, false) := by
  induction us generalizing c with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, ih, Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

theorem f_mem_Ch (h : Head D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ D.Ch h ↔ CVar.f v ∈ D.Xh h := by
  simp [ConstrData.Ch]

theorem side_evH (h : Head D.TV) :
    sideLabel D.inv (evH D h) (evH D h).prep.length = D.Ch h := by
  simp [sideLabel, evH, ConstrData.inv]

theorem side_evQ (w : D.TV) :
    sideLabel D.inv (evQ D w) (evQ D w).prep.length = {(CVar.f w, true)} := by
  simp [sideLabel, evQ, ConstrData.inv]

theorem side_evP (w : D.TV) :
    sideLabel D.inv (evP D w) (evP D w).prep.length = {(CVar.f w, true)} := by
  simp [sideLabel, evP, ConstrData.inv]

theorem f_mem_side_evT (l : List D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ sideLabel D.inv (evT D l) (evT D l).prep.length ↔ v ∉ l := by
  simp only [sideLabel, evT, List.take_length]
  rw [mem_foldl_erase]
  have h1 : (CVar.f v, false) ∈ D.inv (Src.C Head.T) := by
    simp [ConstrData.inv, f_mem_Ch, ConstrData.Xh]
  constructor
  · rintro ⟨_, h⟩ hv
    exact h _ (List.mem_map_of_mem hv) rfl
  · intro hv
    refine ⟨h1, fun u hu he => ?_⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    simp only [Prod.mk.injEq, CVar.f.injEq, and_true] at he
    exact hv (he ▸ hw)

theorem bag_nil : bag D [] = ∅ := by
  ext v
  rw [mem_bag]
  simp

theorem bag_evT (p : List (Ev D)) (l : List D.TV) (v : D.TV) :
    v ∈ bag D (p ++ [evT D l]) ↔ v ∉ l ∨ v ∈ bag D p := by
  rw [mem_bag_snoc, f_mem_side_evT]
  simp [evT]

theorem bag_evH (p : List (Ev D)) (h : Head D.TV) (v : D.TV) :
    v ∈ bag D (p ++ [evH D h]) ↔ CVar.f v ∈ D.Xh h ∨ v ∈ bag D p := by
  rw [mem_bag_snoc, side_evH, f_mem_Ch]
  simp [evH]

theorem bag_evQ (p : List (Ev D)) (w v : D.TV) :
    v ∈ bag D (p ++ [evQ D w]) ↔ v ∈ bag D p ∧ v ≠ w := by
  rw [mem_bag_snoc, side_evQ]
  simp [evQ, eq_comm]

/-- An event that neither adds nor removes facts. -/
def Neutral (e : Ev D) : Prop :=
  (∀ v, (CVar.f v, false) ∉ sideLabel D.inv e e.prep.length) ∧ ∀ v, e.pivot ≠ CVar.f v

theorem bag_neutral {e : Ev D} (he : Neutral D e) (p : List (Ev D)) :
    bag D (p ++ [e]) = bag D p := by
  ext v
  rw [mem_bag_snoc]
  simp [he.1 v, he.2 v]

theorem bag_neutral_list {L : List (Ev D)} (hL : ∀ e ∈ L, Neutral D e) (pre : List (Ev D)) :
    bag D (pre ++ L) = bag D pre := by
  induction L generalizing pre with
  | nil => simp
  | cons x L ih =>
    have hx := hL x (by simp)
    rw [← List.singleton_append, ← List.append_assoc, ih (fun e he => hL e (by simp [he])),
      bag_neutral D hx]

theorem neutral_evH {h : Head D.TV} (hh : ∀ v, CVar.f v ∉ D.Xh h) : Neutral D (evH D h) := by
  refine ⟨fun v => ?_, fun v => by simp [evH]⟩
  rw [side_evH, f_mem_Ch]
  exact hh v

theorem inner1_sub {h : Head D.TV} (hh : h ∈ D.inner1) :
    ∃ p, h = Head.i1 p ∧ p ∈ D.t1.internalPaths ∧ p ≠ [] := by
  simp only [ConstrData.inner1, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hh
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hh
  exact ⟨p, rfl, hp, hne⟩

theorem inner2_sub {h : Head D.TV} (hh : h ∈ D.inner2) :
    ∃ p, h = Head.i2 p ∧ p ∈ D.t2.internalPaths ∧ p ≠ [] := by
  simp only [ConstrData.inner2, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hh
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hh
  exact ⟨p, rfl, hp, hne⟩

theorem neutral_ord1 {O : D.CanonOrders} (hO : O.Valid) : ∀ e ∈ seg1 D O, Neutral D e := by
  intro e he
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 he
  obtain ⟨p, rfl, -⟩ := inner1_sub D (by rw [← hO.2.1]; simpa using hh)
  exact neutral_evH D (fun v => by simp [ConstrData.Xh])

theorem Xh_a (v : D.TV) : D.Xh (Head.a v) = {CVar.f v} := rfl

theorem unselSeg_cons (v : D.TV) (l : List D.TV) :
    unselSeg D (v :: l) = [evH D (Head.a v), evQ D v] ++ unselSeg D l := by
  simp [unselSeg]

theorem bag_unsel (lu : List D.TV) (hnd : lu.Nodup) (B : Finset D.TV) (hB : ∀ v ∈ lu, v ∉ B)
    (pre : List (Ev D)) (hbag : bag D pre = B ∪ lu.toFinset) :
    bag D (pre ++ unselSeg D lu) = B := by
  induction lu generalizing pre with
  | nil => simpa [unselSeg] using hbag
  | cons v lu ih =>
    rw [List.nodup_cons] at hnd
    have hvB : v ∉ B := hB v (by simp)
    have h1 : bag D (pre ++ [evH D (Head.a v)]) = bag D pre := by
      ext x
      rw [bag_evH, Xh_a, hbag]
      simp only [Finset.mem_singleton, CVar.f.injEq, Finset.mem_union, List.mem_toFinset,
        List.mem_cons]
      constructor
      · rintro (rfl | h) <;> tauto
      · tauto
    have h2 : bag D (pre ++ [evH D (Head.a v), evQ D v]) = B ∪ lu.toFinset := by
      ext x
      have : pre ++ [evH D (Head.a v), evQ D v] = (pre ++ [evH D (Head.a v)]) ++ [evQ D v] := by
        simp
      rw [this, bag_evQ, h1, hbag]
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro ⟨h | rfl | h, hne⟩
        · exact Or.inl h
        · exact absurd rfl hne
        · exact Or.inr h
      · rintro (h | h)
        · exact ⟨Or.inl h, fun he => hvB (he ▸ h)⟩
        · exact ⟨Or.inr (Or.inr h), fun he => hnd.1 (he ▸ h)⟩
    rw [unselSeg_cons, ← List.append_assoc]
    exact ih hnd.2 (fun x hx => hB x (by simp [hx])) _ h2

theorem pivA_evH (h : Head D.TV) : (evH D h).pivot ≠ CVar.A := by simp [evH]

theorem pivA_evQ (v : D.TV) : (evQ D v).pivot ≠ CVar.A := by simp [evQ]

theorem pivA_evP (v : D.TV) : (evP D v).pivot ≠ CVar.A := by simp [evP]

theorem q_pos (hD : D.Valid) : 1 ≤ D.q := by
  obtain ⟨h1, h2, h3, -⟩ := hD
  unfold ConstrData.q ConstrData.m ConstrData.ℓ
  have : D.b * (D.K + 1) ≤ D.b * D.n := Nat.mul_le_mul_left _ h3
  have hb : 1 ≤ D.b := by unfold ConstrData.b; omega
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

/-! ### Commuting swaps with small bags -/
/-- Two events that commute with distinct pivots. -/
def Comm (x e : Ev D) : Prop :=
  (e.pivot, false) ∉ (sideLabel D.inv x x.prep.length).erase (x.pivot, true) ∧
    (x.pivot, false) ∉ (sideLabel D.inv e e.prep.length).erase (e.pivot, true) ∧
    x.pivot ≠ e.pivot

/-- Events whose fact literals lie in `B`, never `A`. -/
def GoodB (B : Finset D.TV) (e : Ev D) : Prop :=
  e.pivot ≠ CVar.A ∧ ∀ v, (CVar.f v, false) ∈ sideLabel D.inv e e.prep.length → v ∈ B

theorem bag_subB {B : Finset D.TV} {pre : List (Ev D)} (h0 : bag D pre ⊆ B) (m : List (Ev D))
    (hm : ∀ e ∈ m, GoodB D B e) : bag D (pre ++ m) ⊆ B := by
  induction m using List.reverseRecOn with
  | nil => simpa using h0
  | append_singleton m e ih =>
    intro v hv
    rw [← List.append_assoc, mem_bag_snoc] at hv
    rcases hv with hv | ⟨hv, -⟩
    · exact (hm e (by simp)).2 v hv
    · exact ih (fun x hx => hm x (by simp [hx])) hv

/-- One swap step inside a valid list. -/
theorem step_swap (hD : D.Valid) {pre post : List (Ev D)} {e₁ e₂ : Ev D}
    (h : CombOK D (pre ++ e₁ :: e₂ :: post))
    (hA : ∀ e ∈ pre ++ [e₁, e₂], e.pivot ≠ CVar.A) (hc : Comm D e₁ e₂)
    (hb : (bag D (pre ++ [e₂])).card ≤ 2) :
    Link D (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) := by
  have hs : Shape D (pre ++ [e₁, e₂]) :=
    shape_of_ok D hD (t := post) (by simpa using h) hA
  have hs' : Shape D (pre ++ [e₂]) :=
    shape_sublist D hs (List.Sublist.append_left (List.Sublist.cons _ (List.Sublist.refl _)) pre)
  have hq := q_pos D hD
  refine link_swap_comm (by norm_num) h hc.1 hc.2.1 hc.2.2 ?_
  show (goal D (pre ++ [e₂])).card ≤ D.W
  rw [card_goal_shape D hD hs']
  unfold ConstrData.W ConstrData.r
  split_ifs <;> omega

/-- Move `e` left across `xs`. -/
theorem crossL (hD : D.Valid) {B : Finset D.TV} (hB : B.card ≤ 2) {pre : List (Ev D)}
    (h0 : bag D pre ⊆ B) (hpA : ∀ e ∈ pre, e.pivot ≠ CVar.A) (e : Ev D) (he : GoodB D B e)
    (rest : List (Ev D)) :
    ∀ (xs m : List (Ev D)), (∀ x ∈ m, GoodB D B x) → (∀ x ∈ xs, GoodB D B x ∧ Comm D x e) →
      CombOK D (pre ++ m ++ xs ++ e :: rest) →
      Link D (pre ++ m ++ xs ++ e :: rest) (pre ++ m ++ e :: (xs ++ rest)) := by
  intro xs
  induction xs with
  | nil =>
    intro m _ _ hok
    simpa [Link, CombOK] using link_refl hok
  | cons x xs ih =>
    intro m hm hxs hok
    have hx := hxs x (by simp)
    have h1 := ih (m ++ [x]) (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact hm y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact hx.1)
      (fun y hy => hxs y (by simp [hy])) (by simpa using hok)
    have hok2 : CombOK D ((pre ++ m) ++ x :: e :: (xs ++ rest)) := by
      have := h1.2.1
      simpa [CombOK] using this
    have h2 := step_swap D hD hok2 (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · rcases List.mem_append.1 hy with hy | hy
          · exact hpA y hy
          · exact (hm y hy).1
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact hx.1.1
          · exact he.1) hx.2 (by
        have hsub := bag_subB D h0 (m ++ [e]) (fun y hy => by
          rcases List.mem_append.1 hy with hy | hy
          · exact hm y hy
          · simp only [List.mem_singleton] at hy; subst hy; exact he)
        rw [List.append_assoc]
        exact (Finset.card_le_card hsub).trans hB)
    have h1' : Link D (pre ++ m ++ (x :: xs) ++ e :: rest)
        ((pre ++ m) ++ x :: e :: (xs ++ rest)) := by simpa using h1
    have h2' : Link D ((pre ++ m) ++ x :: e :: (xs ++ rest))
        (pre ++ m ++ e :: (x :: xs ++ rest)) := by simpa using h2
    exact link_trans h1' h2'

/-- Move `e` right across `xs`. -/
theorem crossR (hD : D.Valid) {B : Finset D.TV} (hB : B.card ≤ 2) {pre : List (Ev D)}
    (h0 : bag D pre ⊆ B) (hpA : ∀ e ∈ pre, e.pivot ≠ CVar.A) (e : Ev D) (he : e.pivot ≠ CVar.A)
    (rest : List (Ev D)) :
    ∀ (xs m : List (Ev D)), (∀ x ∈ m, GoodB D B x) → (∀ x ∈ xs, GoodB D B x ∧ Comm D e x) →
      CombOK D (pre ++ m ++ e :: (xs ++ rest)) →
      Link D (pre ++ m ++ e :: (xs ++ rest)) (pre ++ m ++ xs ++ e :: rest) := by
  intro xs
  induction xs with
  | nil =>
    intro m _ _ hok
    simpa [Link, CombOK] using link_refl hok
  | cons x xs ih =>
    intro m hm hxs hok
    have hx := hxs x (by simp)
    have hok1 : CombOK D ((pre ++ m) ++ e :: x :: (xs ++ rest)) := by simpa using hok
    have h1 := step_swap D hD hok1 (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · rcases List.mem_append.1 hy with hy | hy
          · exact hpA y hy
          · exact (hm y hy).1
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact he
          · exact hx.1.1) hx.2 (by
        have hsub := bag_subB D h0 (m ++ [x]) (fun y hy => by
          rcases List.mem_append.1 hy with hy | hy
          · exact hm y hy
          · simp only [List.mem_singleton] at hy; subst hy; exact hx.1)
        rw [List.append_assoc]
        exact (Finset.card_le_card hsub).trans hB)
    have hok2 : CombOK D (pre ++ (m ++ [x]) ++ e :: (xs ++ rest)) := by
      have := h1.2.1
      simpa [CombOK] using this
    have h2 := ih (m ++ [x]) (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact hm y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact hx.1)
      (fun y hy => hxs y (by simp [hy])) hok2
    have h1' : Link D (pre ++ m ++ e :: (x :: xs ++ rest))
        (pre ++ (m ++ [x]) ++ e :: (xs ++ rest)) := by simpa using h1
    have h2' : Link D (pre ++ (m ++ [x]) ++ e :: (xs ++ rest))
        (pre ++ m ++ (x :: xs) ++ e :: rest) := by simpa using h2
    exact link_trans h1' h2'

/-! ### Second-tree heads -/
theorem head2_ne_a (p : List Bool) (v : D.TV) : D.head2 p ≠ Head.a v := by
  unfold ConstrData.head2
  split
  · simp
  · split_ifs <;> simp
  · simp

/-- `U` or a second-tree internal head. -/
def T2 (h : Head D.TV) : Prop := h = Head.U ∨ ∃ p, h = Head.i2 p

theorem t2_seg2 {O : D.CanonOrders} (hO : O.Valid) {e : Ev D} (he : e ∈ seg2 D O) :
    ∃ h, e = evH D h ∧ T2 D h := by
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨_, rfl, Or.inl rfl⟩
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 he
  obtain ⟨p, rfl, -⟩ := inner2_sub D (by rw [← hO.2.2.2.2.1]; simpa using hh)
  exact ⟨_, rfl, Or.inr ⟨p, rfl⟩⟩

theorem t2_ord2 {O : D.CanonOrders} (hO : O.Valid) {e : Ev D} (he : e ∈ O.ord2.map (evH D)) :
    ∃ h, e = evH D h ∧ T2 D h :=
  t2_seg2 D hO (List.mem_cons_of_mem _ he)

theorem neutral_T2 {h : Head D.TV} (hh : T2 D h) : Neutral D (evH D h) := by
  rcases hh with rfl | ⟨p, rfl⟩ <;> exact neutral_evH D (fun v => by simp [ConstrData.Xh])

theorem good_T2 (B : Finset D.TV) {h : Head D.TV} (hh : T2 D h) : GoodB D B (evH D h) :=
  ⟨pivA_evH D h, fun w hw => absurd hw ((neutral_T2 D hh).1 w)⟩

theorem comm_P_T2 (v : D.TV) {h : Head D.TV} (hh : T2 D h) : Comm D (evP D v) (evH D h) := by
  refine ⟨?_, ?_, by simp [evP, evH]⟩
  · rw [side_evP]; simp [evH, evP]
  · rw [side_evH]
    rcases hh with rfl | ⟨p, rfl⟩ <;> simp [evP, evH, ConstrData.Ch, ConstrData.Xh]

theorem comm_T2_a (v : D.TV) {h : Head D.TV} (hh : T2 D h) : Comm D (evH D h) (evH D (Head.a v)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [side_evH]
    rcases hh with rfl | ⟨p, rfl⟩ <;>
      simp [evH, ConstrData.Ch, ConstrData.Xh, ConstrData.deps, head2_ne_a, eq_comm]
  · rw [side_evH]
    rcases hh with rfl | ⟨p, rfl⟩ <;>
      simp [evH, ConstrData.Ch, ConstrData.Xh, ConstrData.deps]
  · rcases hh with rfl | ⟨p, rfl⟩ <;> simp [evH]

theorem comm_T2_Q (v : D.TV) {h : Head D.TV} (hh : T2 D h) : Comm D (evH D h) (evQ D v) := by
  refine ⟨?_, ?_, by simp [evQ, evH]⟩
  · rw [side_evH]
    rcases hh with rfl | ⟨p, rfl⟩ <;> simp [evH, evQ, ConstrData.Ch, ConstrData.Xh]
  · rw [side_evQ]; simp [evH, evQ]

theorem good_a (v : D.TV) : GoodB D {v} (evH D (Head.a v)) := by
  refine ⟨pivA_evH D _, fun w hw => ?_⟩
  rw [side_evH, f_mem_Ch, Xh_a] at hw
  simpa using hw

theorem good_Q (B : Finset D.TV) (v : D.TV) : GoodB D B (evQ D v) := by
  refine ⟨pivA_evQ D _, fun w hw => ?_⟩
  rw [side_evQ] at hw
  simp at hw

/-! ### The prefix before `U` -/
/-- `T` (raw for `v`), the first-tree heads, the unselected pairs. -/
def pre0 (O : D.CanonOrders) (lx lu : List D.TV) : List (Ev D) :=
  [evT D lx] ++ seg1 D O ++ unselSeg D lu

theorem notA_pre0 (O : D.CanonOrders) (hO : O.Valid) (lx lu : List D.TV) :
    ∀ e ∈ pre0 D O lx lu, e.pivot ≠ CVar.A := by
  intro e he
  simp only [pre0, List.mem_append] at he
  rcases he with (he | he) | he
  · simp only [List.mem_singleton] at he; subst he; simp [evT]
  · obtain ⟨h, -, rfl⟩ := List.mem_map.1 he; exact pivA_evH D h
  · obtain ⟨v, -, he⟩ := List.mem_flatMap.1 he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact pivA_evH D _
    · exact pivA_evQ D _

theorem bag_pre0 {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV} {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) : bag D (pre0 D O lx lu) = {v} := by
  obtain ⟨hD, hO, hvX, -, -, a1, a2, -, -, c1, c2, -, -⟩ := hs
  have hvlx : v ∉ lx := by
    intro h
    have := (List.nodup_append.1 a1).2.2 v h v (by simp)
    exact this rfl
  have hlx : ∀ w, w ∈ lx ↔ w ∈ X := by
    intro w
    constructor
    · intro hw
      have : w ∈ insert v X := by rw [← a2]; simp [hw]
      rcases Finset.mem_insert.1 this with rfl | h
      · exact absurd hw hvlx
      · exact h
    · intro hw
      have : w ∈ (lx ++ [v]).toFinset := by rw [a2]; exact Finset.mem_insert_of_mem hw
      simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset,
        List.mem_singleton] at this
      rcases this with h | rfl
      · exact h
      · exact absurd hw hvX
  have hT : bag D [evT D lx] = {v} ∪ lu.toFinset := by
    ext w
    have := bag_evT D [] lx w
    rw [List.nil_append, bag_nil] at this
    rw [this, c2, hlx]
    simp only [Finset.notMem_empty, or_false, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_compl, Finset.mem_insert]
    by_cases hw : w = v
    · subst hw; simp [hvX]
    · simp [hw]
  have h1 : bag D ([evT D lx] ++ seg1 D O) = {v} ∪ lu.toFinset := by
    rw [bag_neutral_list D (neutral_ord1 D hO), hT]
  refine bag_unsel D lu c1 {v} (fun w hw => ?_) _ h1
  have : w ∈ lu.toFinset := List.mem_toFinset.2 hw
  rw [c2] at this
  simp only [Finset.mem_compl, Finset.mem_insert, not_or] at this
  simpa using this.1

theorem card_single (v : D.TV) : ({v} : Finset D.TV).card ≤ 2 := by simp

/-! ### The targets -/
/-- (D2b) carry `P_v` right across `U` and the second-tree heads. -/
theorem del_carryP_post {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV}
    {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) (hok : CombOK D (delL1' D O v lx lu ls lb)) :
    Link D (delL1' D O v lx lu ls lb) (delL2 D O v lx lu ls lb) := by
  have hD := hs.1
  have hO := hs.2.1
  set R := selSeg D (v :: ls) ++ prepSeg D lb ++ tailSeg D O
  have h := crossR D hD (card_single D v) (bag_pre0 D hs).le (notA_pre0 D O hO lx lu)
    (evP D v) (pivA_evP D v) R (seg2 D O) []
    (by simp)
    (fun x hx => by
      obtain ⟨h, rfl, hh⟩ := t2_seg2 D hO hx
      exact ⟨good_T2 D _ hh, comm_P_T2 D v hh⟩)
    (by simpa [delL1', pre0, R] using hok)
  have e1 : delL1' D O v lx lu ls lb = pre0 D O lx lu ++ [] ++ evP D v :: (seg2 D O ++ R) := by
    simp [delL1', pre0, R]
  have e2 : delL2 D O v lx lu ls lb = pre0 D O lx lu ++ [] ++ seg2 D O ++ evP D v :: R := by
    simp [delL2, pre0, R]
  rw [e1, e2]
  exact h

end ReconfRes.Frozen.Dev.Q427d.PartD2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias del_carryP_post := ReconfRes.Frozen.Dev.Q427d.PartD2.del_carryP_post

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD3
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
/-! ### A generic goal swap from commutation (as in Part S3) -/
theorem link_swap_comm {k : ℕ} (hk : 2 ≤ k) {F : CNF V} {w s : ℕ} {inv : ι → Clause V}
    {S : Finset ι} {start : ι} {pre post : List (Event ι V)} {e₁ e₂ : Event ι V}
    (h : CombValid inv S start F w s (pre ++ e₁ :: e₂ :: post))
    (h₁ : (e₂.pivot, false) ∉ (sideLabel inv e₁ e₁.prep.length).erase (e₁.pivot, true))
    (h₂ : (e₁.pivot, false) ∉ (sideLabel inv e₂ e₂.prep.length).erase (e₂.pivot, true))
    (hne : e₁.pivot ≠ e₂.pivot)
    (hw : (goalLabel inv start (pre ++ [e₂])).card ≤ w) :
    CombLink k F w s inv S start (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) := by
  have v1 := (h.2.2.2.2.1 pre e₁ (e₂ :: post) rfl).1
  have v2 := (h.2.2.2.2.1 (pre ++ [e₁]) e₂ post (by simp)).1
  rw [goalLabel_snoc] at v2
  unfold stepG at v2
  refine link_swap hk h ?_ ?_ hw ?_
  · rcases Finset.mem_union.1 v2 with hx | hx
    · exact absurd hx h₁
    · exact (Finset.mem_erase.1 hx).2
  · rw [goalLabel_snoc]
    unfold stepG
    refine Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, v1⟩)
    intro he
    exact hne (Prod.mk.inj he).1
  · simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact step_comm _ _ _ _ h₁ h₂

end ReconfRes.Frozen.Dev.Q427d.PartD3
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD3
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### Side clauses and bag steps (as in Parts K2, S3) -/
theorem mem_foldl_erase {V : Type} [DecidableEq V] {ι : Type} (x : Literal V)
    (us : List (ι × V)) (c : Clause V) :
    x ∈ us.foldl (fun c u => c.erase (u.2, false)) c ↔ x ∈ c ∧ ∀ u ∈ us, x ≠ (u.2, false) := by
  induction us generalizing c with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, ih, Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
    tauto

theorem f_mem_Ch (h : Head D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ D.Ch h ↔ CVar.f v ∈ D.Xh h := by
  simp [ConstrData.Ch]

theorem side_evH (h : Head D.TV) :
    sideLabel D.inv (evH D h) (evH D h).prep.length = D.Ch h := by
  simp [sideLabel, evH, ConstrData.inv]

theorem side_evQ (w : D.TV) :
    sideLabel D.inv (evQ D w) (evQ D w).prep.length = {(CVar.f w, true)} := by
  simp [sideLabel, evQ, ConstrData.inv]

theorem side_evP (w : D.TV) :
    sideLabel D.inv (evP D w) (evP D w).prep.length = {(CVar.f w, true)} := by
  simp [sideLabel, evP, ConstrData.inv]

theorem f_mem_side_evT (l : List D.TV) (v : D.TV) :
    (CVar.f v, false) ∈ sideLabel D.inv (evT D l) (evT D l).prep.length ↔ v ∉ l := by
  simp only [sideLabel, evT, List.take_length]
  rw [mem_foldl_erase]
  have h1 : (CVar.f v, false) ∈ D.inv (Src.C Head.T) := by
    simp [ConstrData.inv, f_mem_Ch, ConstrData.Xh]
  constructor
  · rintro ⟨_, h⟩ hv
    exact h _ (List.mem_map_of_mem hv) rfl
  · intro hv
    refine ⟨h1, fun u hu he => ?_⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    simp only [Prod.mk.injEq, CVar.f.injEq, and_true] at he
    exact hv (he ▸ hw)

theorem bag_nil : bag D [] = ∅ := by
  ext v
  rw [mem_bag]
  simp

theorem bag_evT (p : List (Ev D)) (l : List D.TV) (v : D.TV) :
    v ∈ bag D (p ++ [evT D l]) ↔ v ∉ l ∨ v ∈ bag D p := by
  rw [mem_bag_snoc, f_mem_side_evT]
  simp [evT]

theorem bag_evH (p : List (Ev D)) (h : Head D.TV) (v : D.TV) :
    v ∈ bag D (p ++ [evH D h]) ↔ CVar.f v ∈ D.Xh h ∨ v ∈ bag D p := by
  rw [mem_bag_snoc, side_evH, f_mem_Ch]
  simp [evH]

theorem bag_evQ (p : List (Ev D)) (w v : D.TV) :
    v ∈ bag D (p ++ [evQ D w]) ↔ v ∈ bag D p ∧ v ≠ w := by
  rw [mem_bag_snoc, side_evQ]
  simp [evQ, eq_comm]

/-- An event that neither adds nor removes facts. -/
def Neutral (e : Ev D) : Prop :=
  (∀ v, (CVar.f v, false) ∉ sideLabel D.inv e e.prep.length) ∧ ∀ v, e.pivot ≠ CVar.f v

theorem bag_neutral {e : Ev D} (he : Neutral D e) (p : List (Ev D)) :
    bag D (p ++ [e]) = bag D p := by
  ext v
  rw [mem_bag_snoc]
  simp [he.1 v, he.2 v]

theorem bag_neutral_list {L : List (Ev D)} (hL : ∀ e ∈ L, Neutral D e) (pre : List (Ev D)) :
    bag D (pre ++ L) = bag D pre := by
  induction L generalizing pre with
  | nil => simp
  | cons x L ih =>
    have hx := hL x (by simp)
    rw [← List.singleton_append, ← List.append_assoc, ih (fun e he => hL e (by simp [he])),
      bag_neutral D hx]

theorem neutral_evH {h : Head D.TV} (hh : ∀ v, CVar.f v ∉ D.Xh h) : Neutral D (evH D h) := by
  refine ⟨fun v => ?_, fun v => by simp [evH]⟩
  rw [side_evH, f_mem_Ch]
  exact hh v

theorem inner1_sub {h : Head D.TV} (hh : h ∈ D.inner1) :
    ∃ p, h = Head.i1 p ∧ p ∈ D.t1.internalPaths ∧ p ≠ [] := by
  simp only [ConstrData.inner1, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hh
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hh
  exact ⟨p, rfl, hp, hne⟩

theorem inner2_sub {h : Head D.TV} (hh : h ∈ D.inner2) :
    ∃ p, h = Head.i2 p ∧ p ∈ D.t2.internalPaths ∧ p ≠ [] := by
  simp only [ConstrData.inner2, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hh
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hh
  exact ⟨p, rfl, hp, hne⟩

theorem neutral_ord1 {O : D.CanonOrders} (hO : O.Valid) : ∀ e ∈ seg1 D O, Neutral D e := by
  intro e he
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 he
  obtain ⟨p, rfl, -⟩ := inner1_sub D (by rw [← hO.2.1]; simpa using hh)
  exact neutral_evH D (fun v => by simp [ConstrData.Xh])

theorem Xh_a (v : D.TV) : D.Xh (Head.a v) = {CVar.f v} := rfl

theorem unselSeg_cons (v : D.TV) (l : List D.TV) :
    unselSeg D (v :: l) = [evH D (Head.a v), evQ D v] ++ unselSeg D l := by
  simp [unselSeg]

theorem bag_unsel (lu : List D.TV) (hnd : lu.Nodup) (B : Finset D.TV) (hB : ∀ v ∈ lu, v ∉ B)
    (pre : List (Ev D)) (hbag : bag D pre = B ∪ lu.toFinset) :
    bag D (pre ++ unselSeg D lu) = B := by
  induction lu generalizing pre with
  | nil => simpa [unselSeg] using hbag
  | cons v lu ih =>
    rw [List.nodup_cons] at hnd
    have hvB : v ∉ B := hB v (by simp)
    have h1 : bag D (pre ++ [evH D (Head.a v)]) = bag D pre := by
      ext x
      rw [bag_evH, Xh_a, hbag]
      simp only [Finset.mem_singleton, CVar.f.injEq, Finset.mem_union, List.mem_toFinset,
        List.mem_cons]
      constructor
      · rintro (rfl | h) <;> tauto
      · tauto
    have h2 : bag D (pre ++ [evH D (Head.a v), evQ D v]) = B ∪ lu.toFinset := by
      ext x
      have : pre ++ [evH D (Head.a v), evQ D v] = (pre ++ [evH D (Head.a v)]) ++ [evQ D v] := by
        simp
      rw [this, bag_evQ, h1, hbag]
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro ⟨h | rfl | h, hne⟩
        · exact Or.inl h
        · exact absurd rfl hne
        · exact Or.inr h
      · rintro (h | h)
        · exact ⟨Or.inl h, fun he => hvB (he ▸ h)⟩
        · exact ⟨Or.inr (Or.inr h), fun he => hnd.1 (he ▸ h)⟩
    rw [unselSeg_cons, ← List.append_assoc]
    exact ih hnd.2 (fun x hx => hB x (by simp [hx])) _ h2

theorem pivA_evH (h : Head D.TV) : (evH D h).pivot ≠ CVar.A := by simp [evH]

theorem pivA_evQ (v : D.TV) : (evQ D v).pivot ≠ CVar.A := by simp [evQ]

theorem pivA_evP (v : D.TV) : (evP D v).pivot ≠ CVar.A := by simp [evP]

theorem q_pos (hD : D.Valid) : 1 ≤ D.q := by
  obtain ⟨h1, h2, h3, -⟩ := hD
  unfold ConstrData.q ConstrData.m ConstrData.ℓ
  have : D.b * (D.K + 1) ≤ D.b * D.n := Nat.mul_le_mul_left _ h3
  have hb : 1 ≤ D.b := by unfold ConstrData.b; omega
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

/-! ### Commuting swaps with small bags -/
/-- Two events that commute with distinct pivots. -/
def Comm (x e : Ev D) : Prop :=
  (e.pivot, false) ∉ (sideLabel D.inv x x.prep.length).erase (x.pivot, true) ∧
    (x.pivot, false) ∉ (sideLabel D.inv e e.prep.length).erase (e.pivot, true) ∧
    x.pivot ≠ e.pivot

/-- Events whose fact literals lie in `B`, never `A`. -/
def GoodB (B : Finset D.TV) (e : Ev D) : Prop :=
  e.pivot ≠ CVar.A ∧ ∀ v, (CVar.f v, false) ∈ sideLabel D.inv e e.prep.length → v ∈ B

theorem bag_subB {B : Finset D.TV} {pre : List (Ev D)} (h0 : bag D pre ⊆ B) (m : List (Ev D))
    (hm : ∀ e ∈ m, GoodB D B e) : bag D (pre ++ m) ⊆ B := by
  induction m using List.reverseRecOn with
  | nil => simpa using h0
  | append_singleton m e ih =>
    intro v hv
    rw [← List.append_assoc, mem_bag_snoc] at hv
    rcases hv with hv | ⟨hv, -⟩
    · exact (hm e (by simp)).2 v hv
    · exact ih (fun x hx => hm x (by simp [hx])) hv

/-- One swap step inside a valid list. -/
theorem step_swap (hD : D.Valid) {pre post : List (Ev D)} {e₁ e₂ : Ev D}
    (h : CombOK D (pre ++ e₁ :: e₂ :: post))
    (hA : ∀ e ∈ pre ++ [e₁, e₂], e.pivot ≠ CVar.A) (hc : Comm D e₁ e₂)
    (hb : (bag D (pre ++ [e₂])).card ≤ 2) :
    Link D (pre ++ e₁ :: e₂ :: post) (pre ++ e₂ :: e₁ :: post) := by
  have hs : Shape D (pre ++ [e₁, e₂]) :=
    shape_of_ok D hD (t := post) (by simpa using h) hA
  have hs' : Shape D (pre ++ [e₂]) :=
    shape_sublist D hs (List.Sublist.append_left (List.Sublist.cons _ (List.Sublist.refl _)) pre)
  have hq := q_pos D hD
  refine link_swap_comm (by norm_num) h hc.1 hc.2.1 hc.2.2 ?_
  show (goal D (pre ++ [e₂])).card ≤ D.W
  rw [card_goal_shape D hD hs']
  unfold ConstrData.W ConstrData.r
  split_ifs <;> omega

/-- Move `e` right across `xs`. -/
theorem crossR (hD : D.Valid) {B : Finset D.TV} (hB : B.card ≤ 2) {pre : List (Ev D)}
    (h0 : bag D pre ⊆ B) (hpA : ∀ e ∈ pre, e.pivot ≠ CVar.A) (e : Ev D) (he : e.pivot ≠ CVar.A)
    (rest : List (Ev D)) :
    ∀ (xs m : List (Ev D)), (∀ x ∈ m, GoodB D B x) → (∀ x ∈ xs, GoodB D B x ∧ Comm D e x) →
      CombOK D (pre ++ m ++ e :: (xs ++ rest)) →
      Link D (pre ++ m ++ e :: (xs ++ rest)) (pre ++ m ++ xs ++ e :: rest) := by
  intro xs
  induction xs with
  | nil =>
    intro m _ _ hok
    simpa [Link, CombOK] using link_refl hok
  | cons x xs ih =>
    intro m hm hxs hok
    have hx := hxs x (by simp)
    have hok1 : CombOK D ((pre ++ m) ++ e :: x :: (xs ++ rest)) := by simpa using hok
    have h1 := step_swap D hD hok1 (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · rcases List.mem_append.1 hy with hy | hy
          · exact hpA y hy
          · exact (hm y hy).1
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact he
          · exact hx.1.1) hx.2 (by
        have hsub := bag_subB D h0 (m ++ [x]) (fun y hy => by
          rcases List.mem_append.1 hy with hy | hy
          · exact hm y hy
          · simp only [List.mem_singleton] at hy; subst hy; exact hx.1)
        rw [List.append_assoc]
        exact (Finset.card_le_card hsub).trans hB)
    have hok2 : CombOK D (pre ++ (m ++ [x]) ++ e :: (xs ++ rest)) := by
      have := h1.2.1
      simpa [CombOK] using this
    have h2 := ih (m ++ [x]) (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact hm y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact hx.1)
      (fun y hy => hxs y (by simp [hy])) hok2
    have h1' : Link D (pre ++ m ++ e :: (x :: xs ++ rest))
        (pre ++ (m ++ [x]) ++ e :: (xs ++ rest)) := by simpa using h1
    have h2' : Link D (pre ++ (m ++ [x]) ++ e :: (xs ++ rest))
        (pre ++ m ++ (x :: xs) ++ e :: rest) := by simpa using h2
    exact link_trans h1' h2'

/-! ### Second-tree heads -/

/-- `U` or a second-tree internal head. -/
def T2 (h : Head D.TV) : Prop := h = Head.U ∨ ∃ p, h = Head.i2 p

theorem t2_seg2 {O : D.CanonOrders} (hO : O.Valid) {e : Ev D} (he : e ∈ seg2 D O) :
    ∃ h, e = evH D h ∧ T2 D h := by
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨_, rfl, Or.inl rfl⟩
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 he
  obtain ⟨p, rfl, -⟩ := inner2_sub D (by rw [← hO.2.2.2.2.1]; simpa using hh)
  exact ⟨_, rfl, Or.inr ⟨p, rfl⟩⟩

theorem neutral_T2 {h : Head D.TV} (hh : T2 D h) : Neutral D (evH D h) := by
  rcases hh with rfl | ⟨p, rfl⟩ <;> exact neutral_evH D (fun v => by simp [ConstrData.Xh])

theorem good_a (v : D.TV) : GoodB D {v} (evH D (Head.a v)) := by
  refine ⟨pivA_evH D _, fun w hw => ?_⟩
  rw [side_evH, f_mem_Ch, Xh_a] at hw
  simpa using hw

theorem good_Q (B : Finset D.TV) (v : D.TV) : GoodB D B (evQ D v) := by
  refine ⟨pivA_evQ D _, fun w hw => ?_⟩
  rw [side_evQ] at hw
  simp at hw

/-! ### The prefix before `U` -/
/-- `T` (raw for `v`), the first-tree heads, the unselected pairs. -/
def pre0 (O : D.CanonOrders) (lx lu : List D.TV) : List (Ev D) :=
  [evT D lx] ++ seg1 D O ++ unselSeg D lu

theorem notA_pre0 (O : D.CanonOrders) (hO : O.Valid) (lx lu : List D.TV) :
    ∀ e ∈ pre0 D O lx lu, e.pivot ≠ CVar.A := by
  intro e he
  simp only [pre0, List.mem_append] at he
  rcases he with (he | he) | he
  · simp only [List.mem_singleton] at he; subst he; simp [evT]
  · obtain ⟨h, -, rfl⟩ := List.mem_map.1 he; exact pivA_evH D h
  · obtain ⟨v, -, he⟩ := List.mem_flatMap.1 he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact pivA_evH D _
    · exact pivA_evQ D _

theorem bag_pre0 {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV} {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) : bag D (pre0 D O lx lu) = {v} := by
  obtain ⟨hD, hO, hvX, -, -, a1, a2, -, -, c1, c2, -, -⟩ := hs
  have hvlx : v ∉ lx := by
    intro h
    have := (List.nodup_append.1 a1).2.2 v h v (by simp)
    exact this rfl
  have hlx : ∀ w, w ∈ lx ↔ w ∈ X := by
    intro w
    constructor
    · intro hw
      have : w ∈ insert v X := by rw [← a2]; simp [hw]
      rcases Finset.mem_insert.1 this with rfl | h
      · exact absurd hw hvlx
      · exact h
    · intro hw
      have : w ∈ (lx ++ [v]).toFinset := by rw [a2]; exact Finset.mem_insert_of_mem hw
      simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset,
        List.mem_singleton] at this
      rcases this with h | rfl
      · exact h
      · exact absurd hw hvX
  have hT : bag D [evT D lx] = {v} ∪ lu.toFinset := by
    ext w
    have := bag_evT D [] lx w
    rw [List.nil_append, bag_nil] at this
    rw [this, c2, hlx]
    simp only [Finset.notMem_empty, or_false, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_compl, Finset.mem_insert]
    by_cases hw : w = v
    · subst hw; simp [hvX]
    · simp [hw]
  have h1 : bag D ([evT D lx] ++ seg1 D O) = {v} ∪ lu.toFinset := by
    rw [bag_neutral_list D (neutral_ord1 D hO), hT]
  refine bag_unsel D lu c1 {v} (fun w hw => ?_) _ h1
  have : w ∈ lu.toFinset := List.mem_toFinset.2 hw
  rw [c2] at this
  simp only [Finset.mem_compl, Finset.mem_insert, not_or] at this
  simpa using this.1

theorem card_single (v : D.TV) : ({v} : Finset D.TV).card ≤ 2 := by simp

/-! ### Part D3 -/
theorem absorb_eq {V : Type} [DecidableEq V] (C g : Clause V) (a b : Literal V) (nb : Literal V)
    (pb : Literal V) (haC : a ∈ C) (hag : a ∈ g) (h1 : a ≠ pb) (h2 : a ≠ nb) (h3 : b ≠ a) :
    C.erase pb ∪ ((({b} : Clause V).erase b ∪ g.erase a).erase nb) = (C.erase a).erase pb ∪ g.erase nb := by
  ext l
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  by_cases hl : l = a
  · subst hl; tauto
  · tauto

theorem heq_absorb (g : Clause (CVar D.TV)) (v : D.TV) (hg : (CVar.f v, false) ∈ g) :
    stepG D.inv (stepG D.inv g (evP D v)) (evH D (Head.b v)) = stepG D.inv g (evBP D v) := by
  have hC : (CVar.f v, false) ∈ D.Ch (Head.b v) := by simp [ConstrData.Ch, ConstrData.Xh]
  have := absorb_eq (D.Ch (Head.b v)) g (CVar.f v, false) (CVar.f v, true)
    (CVar.hd (Head.b v), false) (CVar.hd (Head.b v), true) hC hg (by simp) (by simp) (by simp)
  simpa [stepG, sideLabel, evP, evH, evBP, ConstrData.inv] using this

theorem pivA_evBP (v : D.TV) : (evBP D v).pivot ≠ CVar.A := by simp [evBP]

theorem side_evBP (v : D.TV) :
    sideLabel D.inv (evBP D v) (evBP D v).prep.length = (D.Ch (Head.b v)).erase (CVar.f v, false) := by
  simp [sideLabel, evBP, ConstrData.inv]

theorem good_P (B : Finset D.TV) (v : D.TV) : GoodB D B (evP D v) := by
  refine ⟨pivA_evP D _, fun w hw => ?_⟩
  rw [side_evP] at hw
  simp at hw

theorem good_b (v : D.TV) : GoodB D {v} (evH D (Head.b v)) := by
  refine ⟨pivA_evH D _, fun w hw => ?_⟩
  rw [side_evH, f_mem_Ch] at hw
  simpa [ConstrData.Xh] using hw

theorem comm_a_b (v : D.TV) : Comm D (evH D (Head.a v)) (evH D (Head.b v)) := by
  refine ⟨?_, ?_, by simp [evH]⟩
  · rw [side_evH]; simp [evH, ConstrData.Ch, ConstrData.Xh, ConstrData.deps]
    rintro x y h rfl; exact D.J.irrefl h
  · rw [side_evH]; simp [evH, ConstrData.Ch, ConstrData.Xh, ConstrData.deps]

theorem comm_BP_a (v u : D.TV) (hu : ¬ D.J.Adj u v) : Comm D (evBP D v) (evH D (Head.a u)) := by
  refine ⟨?_, ?_, by simp [evH, evBP]⟩
  · rw [side_evBP]; simp [evH, evBP, ConstrData.Ch, ConstrData.Xh, ConstrData.deps]
  · rw [side_evH]; simp [evH, evBP, ConstrData.Ch, ConstrData.Xh, ConstrData.deps]
    rintro x y h rfl; exact hu h

theorem comm_BP_b (v u : D.TV) (hu : u ≠ v) : Comm D (evBP D v) (evH D (Head.b u)) := by
  refine ⟨?_, ?_, by simp [evH, evBP, Ne.symm hu]⟩
  · rw [side_evBP]; simp [evH, evBP, ConstrData.Ch, ConstrData.Xh, ConstrData.deps, hu]
  · rw [side_evH]; simp [evH, evBP, ConstrData.Ch, ConstrData.Xh, ConstrData.deps]

theorem comm_BP_Q (v u : D.TV) : Comm D (evBP D v) (evQ D u) := by
  refine ⟨?_, ?_, by simp [evQ, evBP]⟩
  · rw [side_evBP]; simp [evQ, evBP, ConstrData.Ch, ConstrData.Xh, ConstrData.deps]
  · rw [side_evQ]; simp [evQ, evBP]

/-- The prefix through the second-tree heads. -/
def pfx (O : D.CanonOrders) (lx lu : List D.TV) : List (Ev D) := pre0 D O lx lu ++ seg2 D O

theorem notA_pfx (O : D.CanonOrders) (hO : O.Valid) (lx lu : List D.TV) :
    ∀ e ∈ pfx D O lx lu, e.pivot ≠ CVar.A := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact notA_pre0 D O hO lx lu e he
  · obtain ⟨h, rfl, -⟩ := t2_seg2 D hO he
    exact pivA_evH D h

theorem bag_pfx {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV} {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) : bag D (pfx D O lx lu) = {v} := by
  unfold pfx
  rw [bag_neutral_list D (fun e he => by
    obtain ⟨h, rfl, hh⟩ := t2_seg2 D hs.2.1 he
    exact neutral_T2 D hh), bag_pre0 D hs]

theorem notA_cons {pre : List (Ev D)} (hpre : ∀ e ∈ pre, e.pivot ≠ CVar.A) (m : List (Ev D))
    (hm : ∀ e ∈ m, e.pivot ≠ CVar.A) : ∀ e ∈ pre ++ m, e.pivot ≠ CVar.A := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact hpre e he
  · exact hm e he

/-- (D3) `P, a, b, Q ↦ P, b, a, Q ↦ b[P], a, Q ↦ a, b[P], Q ↦ a, Q, b[P]`. -/
theorem del_transfer {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV}
    {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) (hok : CombOK D (delL2 D O v lx lu ls lb)) :
    Link D (delL2 D O v lx lu ls lb) (delL3 D O v lx lu ls lb) := by
  have hD := hs.1
  have hO := hs.2.1
  set R := selSeg D ls ++ prepSeg D lb ++ tailSeg D O
  set P := pfx D O lx lu
  have hP := bag_pfx D hs
  have hPA := notA_pfx D O hO lx lu
  have cardB : ∀ m : List (Ev D), (∀ e ∈ m, GoodB D {v} e) → (bag D (P ++ m)).card ≤ 2 :=
    fun m hm => (Finset.card_le_card (bag_subB D hP.le m hm)).trans (card_single D v)
  have e0 : delL2 D O v lx lu ls lb =
      (P ++ [evP D v]) ++ evH D (Head.a v) :: evH D (Head.b v) :: (evQ D v :: R) := by
    simp [delL2, P, pfx, pre0, R, selSeg]
  -- step 1
  have s1 : Link D ((P ++ [evP D v]) ++ evH D (Head.a v) :: evH D (Head.b v) :: (evQ D v :: R))
      ((P ++ [evP D v]) ++ evH D (Head.b v) :: evH D (Head.a v) :: (evQ D v :: R)) := by
    refine step_swap D hD (by rw [← e0]; exact hok) ?_ (comm_a_b D v) ?_
    · refine notA_cons D (notA_cons D hPA _ (by simp [evP])) _ ?_
      simp [evH]
    · rw [List.append_assoc]
      refine cardB _ ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl)
      · exact good_P D _ v
      · exact good_b D v
  -- step 2
  have hvP : (CVar.f v, false) ∈ goal D P := by
    have : v ∈ bag D P := by rw [hP]; simp
    simpa [bag] using this
  have s2 : Link D (P ++ evP D v :: evH D (Head.b v) :: (evH D (Head.a v) :: evQ D v :: R))
      (P ++ evBP D v :: (evH D (Head.a v) :: evQ D v :: R)) := by
    have hok2 : CombOK D (P ++ evP D v :: evH D (Head.b v) ::
        (evH D (Head.a v) :: evQ D v :: R)) := by
      simpa [CombOK] using s1.2.1
    exact link_absorb (u := (Src.P v, CVar.f v)) (sd := Src.C (Head.b v)) (l := [])
      (x := CVar.hd (Head.b v)) (by norm_num) hok2 rfl
      (by simp [sideLabel, ConstrData.inv, ConstrData.Ch, ConstrData.Xh])
      (by simp [sideLabel, ConstrData.inv, ConstrData.Ch])
      (by
        simp only [goalLabel_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact heq_absorb D _ v hvP)
  -- step 3
  have s3 : Link D (P ++ evBP D v :: evH D (Head.a v) :: (evQ D v :: R))
      (P ++ evH D (Head.a v) :: evBP D v :: (evQ D v :: R)) := by
    refine step_swap D hD s2.2.1 ?_ (comm_BP_a D v v (D.J.irrefl)) ?_
    · refine notA_cons D hPA _ ?_
      simp [evH, evBP]
    · refine cardB _ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e rfl
      exact good_a D v
  -- step 4
  have s4 : Link D ((P ++ [evH D (Head.a v)]) ++ evBP D v :: evQ D v :: R)
      ((P ++ [evH D (Head.a v)]) ++ evQ D v :: evBP D v :: R) := by
    refine step_swap D hD (by simpa [CombOK] using s3.2.1) ?_ (comm_BP_Q D v v) ?_
    · refine notA_cons D (notA_cons D hPA _ (by simp [evH])) _ ?_
      simp [evQ, evBP]
    · rw [List.append_assoc]
      refine cardB _ ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl)
      · exact good_a D v
      · exact good_Q D _ v
  have e4 : delL3 D O v lx lu ls lb = P ++ evH D (Head.a v) :: evQ D v :: evBP D v :: R := by
    simp [delL3, P, pfx, pre0, R]
  rw [e0, e4]
  refine link_trans s1 (link_trans ?_ (link_trans s2 (link_trans s3 ?_)))
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using link_refl s1.2.1
  · have s4' : Link D (P ++ evH D (Head.a v) :: evBP D v :: evQ D v :: R)
        (P ++ evH D (Head.a v) :: evQ D v :: evBP D v :: R) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using s4
    exact s4'

end ReconfRes.Frozen.Dev.Q427d.PartD3
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias del_transfer := ReconfRes.Frozen.Dev.Q427d.PartD3.del_transfer

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-- (D4a) carry the pair `a_v, Q_v` left across the second-tree heads. -/
theorem del_carryAQ_post {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV}
    {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) (hok : CombOK D (delL3 D O v lx lu ls lb)) :
    Link D (delL3 D O v lx lu ls lb) (delL3' D O v lx lu ls lb) := by
  have hD := hs.1
  have hO := hs.2.1
  set R := selSeg D ls ++ prepSeg D lb ++ tailSeg D O
  set P := pre0 D O lx lu ++ [evH D Head.U]
  set M := O.ord2.map (evH D)
  have h0 : bag D P ⊆ {v} := by
    simp only [P]
    rw [bag_neutral D (neutral_T2 D (Or.inl rfl)), bag_pre0 D hs]
  have hpA : ∀ e ∈ P, e.pivot ≠ CVar.A := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact notA_pre0 D O hO lx lu e he
    · simp only [List.mem_singleton] at he; subst he; exact pivA_evH D _
  have s1 := crossL D hD (card_single D v) h0 hpA (evH D (Head.a v)) (good_a D v)
    (evQ D v :: evBP D v :: R) M [] (by simp)
    (fun x hx => by
      obtain ⟨h, rfl, hh⟩ := t2_ord2 D hO hx
      exact ⟨good_T2 D _ hh, comm_T2_a D v hh⟩)
    (by simpa [delL3, pre0, P, M, R, seg2] using hok)
  have s2 := crossL D hD (card_single D v) h0 hpA (evQ D v) (good_Q D _ v)
    (evBP D v :: R) M [evH D (Head.a v)]
    (by simpa using good_a D v)
    (fun x hx => by
      obtain ⟨h, rfl, hh⟩ := t2_ord2 D hO hx
      exact ⟨good_T2 D _ hh, comm_T2_Q D v hh⟩)
    (by simpa [CombOK] using s1.2.1)
  have t1 : Link D (delL3 D O v lx lu ls lb)
      (P ++ [] ++ evH D (Head.a v) :: (M ++ evQ D v :: evBP D v :: R)) := by
    have e : delL3 D O v lx lu ls lb = P ++ [] ++ M ++ evH D (Head.a v) :: evQ D v ::
        evBP D v :: R := by
      simp [delL3, pre0, P, M, R, seg2]
    rw [e]; exact s1
  have t2 : Link D (P ++ [] ++ evH D (Head.a v) :: (M ++ evQ D v :: evBP D v :: R))
      (delL3' D O v lx lu ls lb) := by
    have e1 : P ++ [] ++ evH D (Head.a v) :: (M ++ evQ D v :: evBP D v :: R) =
        P ++ [evH D (Head.a v)] ++ M ++ evQ D v :: evBP D v :: R := by simp
    have e2 : delL3' D O v lx lu ls lb =
        P ++ [evH D (Head.a v)] ++ evQ D v :: (M ++ evBP D v :: R) := by
      simp [delL3', pre0, P, M, R]
    rw [e1, e2]; exact s2
  exact link_trans t1 t2

end ReconfRes.Frozen.Dev.Q427d.PartD2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias del_carryAQ_post := ReconfRes.Frozen.Dev.Q427d.PartD2.del_carryAQ_post

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD2
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-- (D4b) carry the pair `a_v, Q_v` left across `U`. -/
theorem del_carryAQ_U {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV}
    {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) (hok : CombOK D (delL3' D O v lx lu ls lb)) :
    Link D (delL3' D O v lx lu ls lb) (delL4 D O v lx lu ls lb) := by
  have hD := hs.1
  have hO := hs.2.1
  set R := O.ord2.map (evH D) ++ [evBP D v] ++ selSeg D ls ++ prepSeg D lb ++ tailSeg D O
  have h := crossR D hD (card_single D v) (bag_pre0 D hs).le (notA_pre0 D O hO lx lu)
    (evH D Head.U) (pivA_evH D _) R [evH D (Head.a v), evQ D v] []
    (by simp)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨good_a D v, comm_T2_a D v (Or.inl rfl)⟩
      · exact ⟨good_Q D _ v, comm_T2_Q D v (Or.inl rfl)⟩)
    (by simpa [delL3', pre0, R] using hok)
  have e1 : delL3' D O v lx lu ls lb =
      pre0 D O lx lu ++ [] ++ evH D Head.U :: ([evH D (Head.a v), evQ D v] ++ R) := by
    simp [delL3', pre0, R]
  have e2 : delL4 D O v lx lu ls lb =
      pre0 D O lx lu ++ [] ++ [evH D (Head.a v), evQ D v] ++ evH D Head.U :: R := by
    simp [delL4, pre0, R, unselSeg, List.flatMap_append, seg2]
  rw [e1, e2]
  exact h

end ReconfRes.Frozen.Dev.Q427d.PartD2
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias del_carryAQ_U := ReconfRes.Frozen.Dev.Q427d.PartD2.del_carryAQ_U

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d.PartD3
open ReconfRes.Frozen ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
/-! ### D5 -/
theorem selSeg_cons (u : D.TV) (l : List D.TV) :
    selSeg D (u :: l) = [evH D (Head.a u), evH D (Head.b u), evQ D u] ++ selSeg D l := by
  simp [selSeg]

theorem notA_selSeg (l : List D.TV) : ∀ e ∈ selSeg D l, e.pivot ≠ CVar.A := by
  intro e he
  obtain ⟨u, -, he⟩ := List.mem_flatMap.1 he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact pivA_evH D _
  · exact pivA_evH D _
  · exact pivA_evQ D _

theorem bag_packet (P : List (Ev D)) (hP : bag D P = ∅) (u : D.TV) :
    bag D (P ++ [evH D (Head.a u), evH D (Head.b u), evQ D u]) = ∅ := by
  ext w
  have : P ++ [evH D (Head.a u), evH D (Head.b u), evQ D u] =
      ((P ++ [evH D (Head.a u)]) ++ [evH D (Head.b u)]) ++ [evQ D u] := by simp
  rw [this, bag_evQ, bag_evH, bag_evH, hP]
  simp [ConstrData.Xh]

theorem bag_sel (l : List D.TV) : ∀ P : List (Ev D), bag D P = ∅ → bag D (P ++ selSeg D l) = ∅ := by
  induction l with
  | nil => intro P hP; simpa [selSeg] using hP
  | cons u l ih =>
    intro P hP
    rw [selSeg_cons, ← List.append_assoc]
    exact ih _ (bag_packet D P hP u)

theorem carry_packets (hD : D.Valid) {v : D.TV} {Q : List (Ev D)} (hQ : bag D Q = ∅)
    (hQA : ∀ e ∈ Q, e.pivot ≠ CVar.A) (Rest : List (Ev D)) :
    ∀ l₂ l₁ : List D.TV, (∀ u ∈ l₂, u ≠ v ∧ ¬ D.J.Adj u v) →
      CombOK D (Q ++ selSeg D l₁ ++ evBP D v :: (selSeg D l₂ ++ Rest)) →
      Link D (Q ++ selSeg D l₁ ++ evBP D v :: (selSeg D l₂ ++ Rest))
        (Q ++ selSeg D (l₁ ++ l₂) ++ evBP D v :: Rest) := by
  intro l₂
  induction l₂ with
  | nil =>
    intro l₁ _ hok
    have h' : Link D (Q ++ selSeg D l₁ ++ evBP D v :: (selSeg D [] ++ Rest))
        (Q ++ selSeg D l₁ ++ evBP D v :: (selSeg D [] ++ Rest)) := link_refl hok
    simpa [selSeg] using h'
  | cons u l₂ ih =>
    intro l₁ hu hok
    obtain ⟨huv, hadj⟩ := hu u (by simp)
    have h0 : bag D (Q ++ selSeg D l₁) ⊆ {u} := by
      rw [bag_sel D l₁ Q hQ]; exact Finset.empty_subset _
    have hpA := notA_cons D hQA _ (notA_selSeg D l₁)
    have c := crossR D hD (card_single D u) h0 hpA (evBP D v) (pivA_evBP D v)
      (selSeg D l₂ ++ Rest) [evH D (Head.a u), evH D (Head.b u), evQ D u] [] (by simp)
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨good_a D u, comm_BP_a D v u hadj⟩
        · exact ⟨good_b D u, comm_BP_b D v u huv⟩
        · exact ⟨good_Q D _ u, comm_BP_Q D v u⟩)
      (by simpa [selSeg_cons] using hok)
    have c' : Link D (Q ++ selSeg D l₁ ++ evBP D v :: (selSeg D (u :: l₂) ++ Rest))
        (Q ++ selSeg D (l₁ ++ [u]) ++ evBP D v :: (selSeg D l₂ ++ Rest)) := by
      have e1 : Q ++ selSeg D l₁ ++ evBP D v :: (selSeg D (u :: l₂) ++ Rest) =
          Q ++ selSeg D l₁ ++ [] ++ evBP D v ::
            ([evH D (Head.a u), evH D (Head.b u), evQ D u] ++ (selSeg D l₂ ++ Rest)) := by
        simp [selSeg_cons]
      have e2 : Q ++ selSeg D (l₁ ++ [u]) ++ evBP D v :: (selSeg D l₂ ++ Rest) =
          Q ++ selSeg D l₁ ++ [] ++ [evH D (Head.a u), evH D (Head.b u), evQ D u] ++
            evBP D v :: (selSeg D l₂ ++ Rest) := by
        simp [selSeg]
      rw [e1, e2]; exact c
    have ih' := ih (l₁ ++ [u]) (fun w hw => hu w (by simp [hw])) c'.2.1
    have e3 : l₁ ++ [u] ++ l₂ = l₁ ++ u :: l₂ := by simp
    rw [e3] at ih'
    exact link_trans c' ih'

/-- (D5) carry `b_v[P_v]` right across the remaining selected packets. -/
theorem del_carryB {O : D.CanonOrders} {X : Finset D.TV} {v : D.TV}
    {lx lu ls lb : List D.TV}
    (hs : DelSetting D O X v lx lu ls lb) (hok : CombOK D (delL4 D O v lx lu ls lb)) :
    Link D (delL4 D O v lx lu ls lb) (delL5 D O v lx lu ls lb) := by
  have hD := hs.1
  have hO := hs.2.1
  obtain ⟨-, -, hvX, hind, -, -, -, b1, b2, -, -, -, -⟩ := id hs
  set Q := pfx D O lx (lu ++ [v])
  set Rest := prepSeg D lb ++ tailSeg D O
  have hQe : Q = pre0 D O lx lu ++ [evH D (Head.a v), evQ D v] ++ seg2 D O := by
    simp [Q, pfx, pre0, unselSeg, List.flatMap_append]
  have hQ : bag D Q = ∅ := by
    have h0 := bag_pre0 D hs
    have h1 : bag D (pre0 D O lx lu ++ [evH D (Head.a v), evQ D v]) = ∅ := by
      ext w
      have : pre0 D O lx lu ++ [evH D (Head.a v), evQ D v] =
          (pre0 D O lx lu ++ [evH D (Head.a v)]) ++ [evQ D v] := by simp
      rw [this, bag_evQ, bag_evH, h0]
      simp [ConstrData.Xh]
    rw [hQe, bag_neutral_list D (fun e he => by
      obtain ⟨h, rfl, hh⟩ := t2_seg2 D hO he
      exact neutral_T2 D hh), h1]
  have hQA : ∀ e ∈ Q, e.pivot ≠ CVar.A := by
    rw [hQe]
    refine notA_cons D (notA_cons D (notA_pre0 D O hO lx lu) _ ?_) _ ?_
    · simp [evH, evQ]
    · intro e he
      obtain ⟨h, rfl, -⟩ := t2_seg2 D hO he
      exact pivA_evH D h
  have hls : ∀ u ∈ ls, u ≠ v ∧ ¬ D.J.Adj u v := by
    intro u hu
    have hvls : v ∉ ls := (List.nodup_cons.1 b1).1
    have huX : u ∈ insert v X := by rw [← b2]; simp [hu]
    exact ⟨fun h => hvls (h ▸ hu), hind u huX v (Finset.mem_insert_self v X)⟩
  have h := carry_packets D hD hQ hQA Rest ls [] hls (by simpa [delL4, Q, pfx, pre0, Rest, selSeg] using hok)
  have e1 : delL4 D O v lx lu ls lb = Q ++ selSeg D [] ++ evBP D v :: (selSeg D ls ++ Rest) := by
    simp [delL4, Q, pfx, pre0, Rest, selSeg]
  have e2 : delL5 D O v lx lu ls lb = Q ++ selSeg D ([] ++ ls) ++ evBP D v :: Rest := by
    simp [delL5, canonL, canonHead, Q, pfx, pre0, Rest, prepSeg]
  rw [e1, e2]
  exact h

end ReconfRes.Frozen.Dev.Q427d.PartD3
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427d
open ConstrData
variable (D : ConstrData)
alias del_carryB := ReconfRes.Frozen.Dev.Q427d.PartD3.del_carryB

/-! ## Assembly -/

theorem link_sort (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    (hX : IsIndepSet D.J X) (hXℓ : D.ℓ ≤ X.card) {lT lu ls lb lT' lu' ls' lb' : List D.TV}
    (hL : ListsFor D X lT lu ls lb) (hL' : ListsFor D X lT' lu' ls' lb') :
    Link D (canonL D O lT lu ls lb) (canonL D O lT' lu' ls' lb') := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ := hL
  obtain ⟨a1', a2', b1', b2', c1', c2', d1', d2'⟩ := hL'
  have h1 := sort_privT D hD hO hX hXℓ (lT := lT) (lT' := lT') (lu := lu) (ls := ls) (lb := lb)
    ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ ⟨a1', a2', b1, b2, c1, c2, d1, d2⟩
  have h2 := sort_unsel D hD hO hX hXℓ (lT := lT') (lu := lu) (lu' := lu') (ls := ls) (lb := lb)
    ⟨a1', a2', b1, b2, c1, c2, d1, d2⟩ ⟨a1', a2', b1, b2, c1', c2', d1, d2⟩
  have h3 := sort_sel D hD hO hX hXℓ (lT := lT') (lu := lu') (ls := ls) (ls' := ls') (lb := lb)
    ⟨a1', a2', b1, b2, c1', c2', d1, d2⟩ ⟨a1', a2', b1', b2', c1', c2', d1, d2⟩
  have h4 := sort_prepB D hD hO hX hXℓ (lT := lT') (lu := lu') (ls := ls') (lb := lb) (lb' := lb')
    ⟨a1', a2', b1', b2', c1', c2', d1, d2⟩ ⟨a1', a2', b1', b2', c1', c2', d1', d2'⟩
  exact link_trans (link_trans (link_trans h1 h2) h3) h4

theorem link_delete (hD : D.Valid) {O : D.CanonOrders} (hO : O.Valid) {X : Finset D.TV}
    {v : D.TV} (hv : v ∉ X) (hind : IsIndepSet D.J (insert v X)) (hXℓ : D.ℓ ≤ X.card)
    (LY LX : D.SetOrders) (hLY : ConstrData.SetOrders.ValidFor D LY (insert v X))
    (hLX : ConstrData.SetOrders.ValidFor D LX X) :
    Link D (D.canonEvents O LY) (D.canonEvents O LX) := by
  set lx := X.toList with hlx
  set lu := (insert v X)ᶜ.toList with hlu
  have hlxnd : lx.Nodup := Finset.nodup_toList X
  have hlxf : lx.toFinset = X := Finset.toList_toFinset X
  have hlund : lu.Nodup := Finset.nodup_toList _
  have hluf : lu.toFinset = (insert v X)ᶜ := Finset.toList_toFinset _
  have hvlx : v ∉ lx := by rw [Finset.mem_toList]; exact hv
  have hvlu : v ∉ lu := by rw [Finset.mem_toList]; simp
  have hY : ListsFor D (insert v X) (lx ++ [v]) lu (v :: lx) lu := by
    refine ⟨?_, ?_, List.nodup_cons.2 ⟨hvlx, hlxnd⟩, ?_, hlund, hluf, hlund, hluf⟩
    · exact List.Nodup.append hlxnd (List.nodup_singleton v) (by simpa using hvlx)
    · rw [List.toFinset_append, hlxf]; ext x; simp
    · rw [List.toFinset_cons, hlxf]
  have hXl : ListsFor D X lx (lu ++ [v]) lx (v :: lu) := by
    have hc : (lu ++ [v]).toFinset = Xᶜ := by
      rw [List.toFinset_append, hluf]; ext x; by_cases hx : x = v <;> simp [hx, hv]
    have hc' : (v :: lu).toFinset = Xᶜ := by
      rw [List.toFinset_cons, hluf]; ext x; by_cases hx : x = v <;> simp [hx, hv]
    refine ⟨hlxnd, hlxf, hlxnd, hlxf, ?_, hc, List.nodup_cons.2 ⟨hvlu, hlund⟩, hc'⟩
    exact List.Nodup.append hlund (List.nodup_singleton v) (by simpa using hvlu)
  have hs : DelSetting D O X v lx lu lx lu := ⟨hD, hO, hv, hind, hXℓ, hY⟩
  have hYℓ : D.ℓ ≤ (insert v X).card := hXℓ.trans (Finset.card_le_card (Finset.subset_insert _ _))
  have hXind : IsIndepSet D.J X :=
    fun a ha b hb => hind a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
  have s1 : Link D (D.canonEvents O LY) (delL0 D O v lx lu lx lu) := by
    rw [canonEvents_eq]
    exact link_sort D hD hO hind hYℓ ((validFor_iff D LY _).1 hLY) hY
  have e1 := del_split D hs s1.2.1
  have e2 := del_carryP_pre D hs e1.2.1
  have e3 := del_carryP_post D hs e2.2.1
  have e4 := del_transfer D hs e3.2.1
  have e5 := del_carryAQ_post D hs e4.2.1
  have e6 := del_carryAQ_U D hs e5.2.1
  have e7 := del_carryB D hs e6.2.1
  have s2 : Link D (delL5 D O v lx lu lx lu) (D.canonEvents O LX) := by
    rw [canonEvents_eq]
    exact link_sort D hD hO hXind hXℓ hXl ((validFor_iff D LX _).1 hLX)
  exact link_trans (link_trans (link_trans (link_trans (link_trans (link_trans (link_trans
    (link_trans s1 e1) e2) e3) e4) e5) e6) e7) s2

theorem chk_lemma_3_62 (D : ConstrData) (hD : D.Valid) (O : D.CanonOrders) (hO : O.Valid)
    (X Y : Finset D.TV) (hX : IsIndepSet D.J X) (hY : IsIndepSet D.J Y)
    (hXℓ : D.ℓ ≤ X.card) (hYℓ : D.ℓ ≤ Y.card)
    (hXY : (∃ v, v ∉ X ∧ Y = insert v X) ∨ (∃ v, v ∉ Y ∧ X = insert v Y))
    (LX LY : D.SetOrders) (RX RY : ProofDag (CVar D.TV))
    (posX : Src D.TV → Fin RX.n) (posY : Src D.TV → Fin RY.n)
    (hRX : D.IsCanonical O X LX RX posX) (hRY : D.IsCanonical O Y LY RY posY) :
    IndexedFrozenConnected 2 D.formula D.W (2 * D.α - 1) D.inv D.srcs ⟨RX, posX⟩ ⟨RY, posY⟩ := by
  have hL : Link D (D.canonEvents O LX) (D.canonEvents O LY) := by
    rcases hXY with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · exact link_symm (link_delete D hD hO hv hY hXℓ LY LX hRY.1 hRX.1)
    · exact link_delete D hD hO hv hX hYℓ LX LY hRX.1 hRY.1
  exact hL.2.2 RX posX RY posY hRX.2 hRY.2

end ReconfRes.Frozen.Dev.Q427d
end
end

section
open MultiplierAssoc206.Resolution Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen
theorem chk_lemma_3_62 (D : ConstrData) (hD : D.Valid) (O : D.CanonOrders) (hO : O.Valid)
    (X Y : Finset D.TV) (hX : IsIndepSet D.J X) (hY : IsIndepSet D.J Y)
    (hXℓ : D.ℓ ≤ X.card) (hYℓ : D.ℓ ≤ Y.card)
    (hXY : (∃ v, v ∉ X ∧ Y = insert v X) ∨ (∃ v, v ∉ Y ∧ X = insert v Y))
    (LX LY : D.SetOrders) (RX RY : ProofDag (CVar D.TV))
    (posX : Src D.TV → Fin RX.n) (posY : Src D.TV → Fin RY.n)
    (hRX : D.IsCanonical O X LX RX posX) (hRY : D.IsCanonical O Y LY RY posY) :
    IndexedFrozenConnected 2 D.formula D.W (2 * D.α - 1) D.inv D.srcs ⟨RX, posX⟩ ⟨RY, posY⟩ :=
  Dev.Q427d.chk_lemma_3_62 D hD O hO X Y hX hY hXℓ hYℓ hXY LX LY RX RY posX posY hRX hRY

end ReconfRes.Frozen
end
end

open ReconfRes.Frozen in
theorem solution : type_of% @ReconfRes.Frozen.chk_lemma_3_62 := @ReconfRes.Frozen.chk_lemma_3_62
