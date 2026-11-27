-- Prove2me | solution 1 for RankingQueryCost.Joint.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:56:09.807779+00:00
-- url     : https://prove2.me/submissions/fade6cd7-ad06-4600-94bb-9d79e369e3f4

import Definitions.Def_RankingQueryCost_Joint_Pivot

set_option autoImplicit false
set_option maxHeartbeats 400000


noncomputable section

namespace RQCPivot
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The block chosen by the breadth-first rule, if any. Independent of the seed. -/
def selIndex (L : ℕ) (P : PivotState n) : Option ℕ :=
  if (liveBlocks 1 L P.slots).isEmpty then none else
  some (((liveBlocks 1 L P.slots).mergeSort fun i j =>
    decide (((P.slots[i]?).map Prod.snd).getD 0 ≤ ((P.slots[j]?).map Prod.snd).getD 0)).headD 0)

/-- The star of a pivot inside a block, in the public lexicographic order. -/
def starOf (U : Finset (Fin n)) (p : Fin n) : List (Pair n) :=
  (pairList n).filter fun e => decide ((e.1.1 = p ∨ e.1.2 = p) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U)

/-- Split the slot `k` of `P` using pivot `p`. -/
def splitAt (W : ComparisonWorld n) (h : ℕ) (P : PivotState n) (k : ℕ) (p : Fin n) : PivotState n :=
  let Ud := (P.slots[k]?).getD (∅, 0)
  let star := starOf Ud.1 p
  let S := star.foldl (fun S e => (readIdentity h W S [] e).2) P.interaction
  let left := Ud.1.filter fun i => RecordedForward S.ledger i p
  let right := Ud.1.filter fun i => RecordedForward S.ledger p i
  let children := [(left, Ud.2 + 1), ({p}, Ud.2 + 1), (right, Ud.2 + 1)]
    |>.filter fun child => decide (0 < child.1.card)
  ⟨P.slots.take k ++ children ++ P.slots.drop (k + 1), S, P.requests ++ star⟩

theorem pivotStep_eq (L : ℕ) (W : ComparisonWorld n) (h : ℕ) (seed : PivotSeed n) (j : ℕ)
    (P : PivotState n) :
    pivotStep 1 L (fun _ _ => 0) true W h seed j P =
      match selIndex L P with
      | none => P
      | some k =>
        let Ud := (P.slots[k]?).getD (∅, 0)
        let priority := if hj : j < n then seed ⟨j, hj⟩ else Equiv.refl (Fin n)
        match (Ud.1.toList.mergeSort fun i j => decide (priority i ≤ priority j)).head? with
        | none => P
        | some p => splitAt W h P k p := by
  unfold pivotStep selIndex
  by_cases hc : (liveBlocks 1 L P.slots).isEmpty
  · simp [hc]
  · simp only [hc, if_false, Bool.false_eq_true]
    rfl

theorem mem_liveBlocks (L : ℕ) (slots : PivotSlots n) (k : ℕ) :
    k ∈ liveBlocks 1 L slots ↔ ∃ h : k < slots.length, 1 < (slots[k]).1.card ∧ (slots[k]).2 < L := by
  unfold liveBlocks
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hk, hd⟩
    refine ⟨hk, ?_⟩
    rw [List.getElem?_eq_getElem hk] at hd
    simpa using hd
  · rintro ⟨hk, hd⟩
    refine ⟨hk, ?_⟩
    rw [List.getElem?_eq_getElem hk]
    simpa using hd

theorem selIndex_some (L : ℕ) (P : PivotState n) (k : ℕ) (hk : selIndex L P = some k) :
    ∃ h : k < P.slots.length, 1 < (P.slots[k]).1.card ∧ (P.slots[k]).2 < L := by
  unfold selIndex at hk
  split_ifs at hk with hc
  simp only [Option.some.injEq] at hk
  rw [← mem_liveBlocks]
  set l := (liveBlocks 1 L P.slots).mergeSort fun i j =>
    decide (((P.slots[i]?).map Prod.snd).getD 0 ≤ ((P.slots[j]?).map Prod.snd).getD 0)
  have hne : l ≠ [] := by
    intro h0
    have : (liveBlocks 1 L P.slots) = [] := by
      have := List.mergeSort_perm (liveBlocks 1 L P.slots) (fun i j =>
        decide (((P.slots[i]?).map Prod.snd).getD 0 ≤ ((P.slots[j]?).map Prod.snd).getD 0))
      rw [← List.length_eq_zero_iff, ← this.length_eq]; simp [l] at h0; simp [h0]
    simp [this] at hc
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  have hmem : x ∈ l := by rw [hx]; exact List.mem_cons_self
  rw [List.mem_mergeSort] at hmem
  rw [← hk, hx]; simpa using hmem

theorem selIndex_none (L : ℕ) (P : PivotState n) (hk : selIndex L P = none) :
    ∀ k (h : k < P.slots.length), ¬ (1 < (P.slots[k]).1.card ∧ (P.slots[k]).2 < L) := by
  intro k h hc
  unfold selIndex at hk
  split_ifs at hk with he
  rw [List.isEmpty_iff] at he
  have : k ∈ liveBlocks 1 L P.slots := (mem_liveBlocks L P.slots k).2 ⟨h, hc⟩
  rw [he] at this; simp at this

/-- The pivot: the minimal-priority member of a nonempty block. -/
theorem head_mergeSort_min (U : Finset (Fin n)) (σ : Rank n) (hU : U.Nonempty) :
    ∃ p, (U.toList.mergeSort fun i j => decide (σ i ≤ σ j)).head? = some p ∧ p ∈ U ∧
      ∀ x ∈ U, σ p ≤ σ x := by
  set l := U.toList.mergeSort fun i j => decide (σ i ≤ σ j)
  have hperm := List.mergeSort_perm U.toList (fun i j => decide (σ i ≤ σ j))
  have hsort : l.Pairwise (fun i j => decide (σ i ≤ σ j) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c hab hbc
      have h1 : σ a ≤ σ b := of_decide_eq_true hab
      have h2 : σ b ≤ σ c := of_decide_eq_true hbc
      exact decide_eq_true (le_trans h1 h2)
    · intro a b
      rcases le_total (σ a) (σ b) with h | h
      · simp [h]
      · simp [h]
  have hne : l ≠ [] := by
    intro h0
    have := hperm.length_eq
    rw [show (U.toList.mergeSort fun i j => decide (σ i ≤ σ j)) = l from rfl, h0] at this
    simp at this
    exact hU.ne_empty (Finset.card_eq_zero.1 this.symm)
  obtain ⟨p, ps, hp⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨p, by rw [hp]; rfl, ?_, ?_⟩
  · have : p ∈ l := by rw [hp]; exact List.mem_cons_self
    have := hperm.mem_iff.1 this
    simpa using this
  · intro x hx
    have hxl : x ∈ l := hperm.mem_iff.2 (by simpa using hx)
    rw [hp] at hxl hsort
    rcases List.mem_cons.1 hxl with rfl | hxs
    · exact le_refl _
    · have := List.rel_of_pairwise_cons hsort hxs
      simpa using this

/-- The unique arg-min of a permutation over a nonempty block. -/
def argminIn (U : Finset (Fin n)) (σ : Rank n) (hU : U.Nonempty) : Fin n :=
  Classical.choose (head_mergeSort_min U σ hU)

theorem argminIn_spec (U : Finset (Fin n)) (σ : Rank n) (hU : U.Nonempty) :
    (U.toList.mergeSort fun i j => decide (σ i ≤ σ j)).head? = some (argminIn U σ hU) ∧
      argminIn U σ hU ∈ U ∧ ∀ x ∈ U, σ (argminIn U σ hU) ≤ σ x :=
  Classical.choose_spec (head_mergeSort_min U σ hU)

/-- Reading a list of pairs through the ledger. -/
def foldRead (W : ComparisonWorld n) (h : ℕ) (l : List (Pair n)) (S : InteractionState n) :
    InteractionState n := l.foldl (fun S e => (readIdentity h W S [] e).2) S

def OnlineOK (h : ℕ) (S : InteractionState n) : Prop :=
  S.online.card ≤ h ∧ ∀ f ∈ S.online, S.ledger f ≠ none

theorem read_fresh (W : ComparisonWorld n) (h : ℕ) (S : InteractionState n) (e : Pair n)
    (he : S.ledger e = none) (hok : OnlineOK h S) :
    let S1 := (readIdentity h W S [] e).2
    (∃ b, S1.ledger = Function.update S.ledger e (some b) ∧
      (b = truthful W.rank e ∨ e ∈ W.initial ∨ e ∈ S1.online \ S.online)) ∧
    (S1.online = S.online ∨ S1.online = insert e S.online) ∧ OnlineOK h S1 := by
  have heo : e ∉ S.online := fun h' => hok.2 e h' he
  have hupd : ∀ (b : Bool) (f : Pair n), f ∈ S.online → Function.update S.ledger e (some b) f ≠ none := by
    intro b f hf
    by_cases hfe : f = e
    · subst hfe; simp
    · rw [Function.update_of_ne hfe]; exact hok.2 f hf
  by_cases hnf : e ∉ W.initial ∧ (W.firstReply S.history S.online [] e).1 = true ∧ S.online.card < h
  · have hor : e ∈ W.initial ∨ (e ∉ W.initial ∧ (W.firstReply S.history S.online [] e).1 = true ∧
        S.online.card < h) := Or.inr hnf
    simp only [readIdentity, he, if_pos hnf, if_pos hor]
    refine ⟨⟨_, rfl, Or.inr (Or.inr ?_)⟩, by simp, ?_, ?_⟩
    · simp [heo]
    · rw [Finset.card_insert_of_notMem heo]; exact hnf.2.2
    · intro f hf
      rcases Finset.mem_insert.1 hf with rfl | hf
      · simp
      · exact hupd _ f hf
  · simp only [readIdentity, he, if_neg hnf]
    by_cases hi : e ∈ W.initial
    · have hor : e ∈ W.initial ∨ (e ∉ W.initial ∧ (W.firstReply S.history S.online [] e).1 = true ∧
          S.online.card < h) := Or.inl hi
      simp only [if_pos hor]
      exact ⟨⟨_, rfl, Or.inr (Or.inl hi)⟩, by simp, hok.1, fun f hf => hupd _ f hf⟩
    · have hor : ¬ (e ∈ W.initial ∨ (e ∉ W.initial ∧ (W.firstReply S.history S.online [] e).1 = true ∧
          S.online.card < h)) := by
        rintro (h1 | h1)
        · exact hi h1
        · exact hnf h1
      simp only [if_neg hor]
      exact ⟨⟨_, rfl, Or.inl rfl⟩, by simp, hok.1, fun f hf => hupd _ f hf⟩

/-- Facts about reading a list of distinct, fresh pairs. -/
theorem foldRead_spec (W : ComparisonWorld n) (h : ℕ) :
    ∀ (l : List (Pair n)) (S : InteractionState n), l.Nodup → (∀ e ∈ l, S.ledger e = none) →
      OnlineOK h S →
      (∀ e, e ∉ l → (foldRead W h l S).ledger e = S.ledger e) ∧
      (∀ e ∈ l, (foldRead W h l S).ledger e = some (truthful W.rank e) ∨ e ∈ W.initial ∨
        e ∈ (foldRead W h l S).online \ S.online) ∧
      (∀ e ∈ l, (foldRead W h l S).ledger e ≠ none) ∧
      S.online ⊆ (foldRead W h l S).online ∧
      ((foldRead W h l S).online \ S.online) ⊆ l.toFinset ∧ OnlineOK h (foldRead W h l S) := by
  intro l
  induction l with
  | nil => intro S _ _ hc; simp [foldRead, hc]
  | cons e l ih =>
    intro S hnd hfresh hok
    have he : S.ledger e = none := hfresh e List.mem_cons_self
    have hnd' := (List.nodup_cons.1 hnd)
    obtain ⟨⟨b, hb, hbv⟩, hon, hok1⟩ := read_fresh W h S e he hok
    set S1 := (readIdentity h W S [] e).2 with hS1
    have hfresh1 : ∀ f ∈ l, S1.ledger f = none := by
      intro f hf
      rw [hb, Function.update_of_ne (by intro h'; subst h'; exact hnd'.1 hf)]
      exact hfresh f (List.mem_cons_of_mem _ hf)
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih S1 hnd'.2 hfresh1 hok1
    have hfold : foldRead W h (e :: l) S = foldRead W h l S1 := rfl
    have heo : e ∉ S.online := fun h' => hok.2 e h' he
    have hsub1 : S.online ⊆ S1.online := by
      rcases hon with h' | h' <;> rw [h'] <;> simp [Finset.subset_insert]
    rw [hfold]
    refine ⟨?_, ?_, ?_, le_trans hsub1 i4, ?_, i6⟩
    · intro f hf
      rw [i1 f (fun h' => hf (List.mem_cons_of_mem _ h')), hb,
        Function.update_of_ne (by intro h'; subst h'; exact hf List.mem_cons_self)]
    · intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [i1 f hnd'.1, hb]
        simp only [Function.update_self]
        rcases hbv with h' | h' | h'
        · left; rw [h']
        · right; left; exact h'
        · right; right
          exact Finset.mem_sdiff.2 ⟨i4 (Finset.mem_sdiff.1 h').1, heo⟩
      · rcases i2 f hf with h' | h' | h'
        · left; exact h'
        · right; left; exact h'
        · right; right
          exact Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 h').1, fun h'' => (Finset.mem_sdiff.1 h').2 (hsub1 h'')⟩
    · intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [i1 f hnd'.1, hb]; simp
      · exact i3 f hf
    · intro f hf
      rw [Finset.mem_sdiff] at hf
      by_cases hf1 : f ∈ S1.online
      · rcases hon with h' | h'
        · rw [h'] at hf1; exact absurd hf1 hf.2
        · rw [h'] at hf1
          rcases Finset.mem_insert.1 hf1 with rfl | h''
          · simp
          · exact absurd h'' hf.2
      · have := i5 (Finset.mem_sdiff.2 ⟨hf.1, hf1⟩)
        simp only [List.mem_toFinset] at this ⊢
        exact List.mem_cons_of_mem _ this

theorem pairList_nodup (n : ℕ) : (pairList n).Nodup := by
  unfold pairList
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro i _
    apply List.Nodup.filterMap _ (List.nodup_finRange n)
    intro a a' b hb hb'
    split_ifs at hb hb' <;> simp_all
    rw [← hb'] at hb; exact (congrArg (fun e : Pair n => e.1.2) hb)
  · apply List.Pairwise.imp _ ((List.nodup_finRange n))
    intro i j hij
    rw [Function.onFun, List.disjoint_left]
    intro e he he'
    simp only [List.mem_filterMap, List.mem_finRange, true_and] at he he'
    obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := he'
    split_ifs at ha hb <;> simp_all
    rw [← hb] at ha
    exact hij (congrArg (fun e : Pair n => e.1.1) ha)

theorem mem_pairList (e : Pair n) : e ∈ pairList n := by
  unfold pairList
  rw [List.mem_flatMap]
  refine ⟨e.1.1, List.mem_finRange _, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨e.1.2, List.mem_finRange _, by simp [e.2]⟩

theorem mem_starOf (U : Finset (Fin n)) (p : Fin n) (e : Pair n) :
    e ∈ starOf U p ↔ (e.1.1 = p ∨ e.1.2 = p) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U := by
  unfold starOf; simp [mem_pairList]

theorem starOf_nodup (U : Finset (Fin n)) (p : Fin n) : (starOf U p).Nodup :=
  (pairList_nodup n).filter _

/-- Recorded orientation of a pair from the ledger. -/
theorem recordedForward_iff (T : Transcript n) (x y : Fin n) (hxy : x < y) :
    (RecordedForward T x y ↔ T ⟨(x, y), hxy⟩ = some true) ∧
      (RecordedForward T y x ↔ T ⟨(x, y), hxy⟩ = some false) := by
  constructor
  · constructor
    · rintro ⟨e, (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)⟩
      · have : e = ⟨(x, y), hxy⟩ := Subtype.ext (Prod.ext h1 h2)
        rw [← this]; exact h3
      · have he := e.2; rw [h1, h2] at he; exact absurd (lt_trans he hxy) (lt_irrefl _)
    · intro h; exact ⟨⟨(x, y), hxy⟩, Or.inl ⟨rfl, rfl, h⟩⟩
  · constructor
    · rintro ⟨e, (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)⟩
      · have he := e.2; rw [h1, h2] at he; exact absurd (lt_trans he hxy) (lt_irrefl _)
      · have : e = ⟨(x, y), hxy⟩ := Subtype.ext (Prod.ext h1 h2)
        rw [← this]; exact h3
    · intro h; exact ⟨⟨(x, y), hxy⟩, Or.inr ⟨rfl, rfl, h⟩⟩

theorem not_recordedForward_self (T : Transcript n) (x : Fin n) : ¬ RecordedForward T x x := by
  rintro ⟨e, (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩)⟩ <;>
    (have he := e.2; rw [h1, h2] at he; exact lt_irrefl _ he)

/-- With the pair answered, exactly one orientation is recorded. -/
theorem recorded_dichotomy (T : Transcript n) (x y : Fin n) (hxy : x ≠ y)
    (hT : ∀ e : Pair n, (e.1.1 = x ∧ e.1.2 = y) ∨ (e.1.1 = y ∧ e.1.2 = x) → T e ≠ none) :
    (RecordedForward T x y ∨ RecordedForward T y x) ∧ ¬ (RecordedForward T x y ∧ RecordedForward T y x) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨h1, h2⟩ := recordedForward_iff T x y h
    have hs := hT ⟨(x, y), h⟩ (Or.inl ⟨rfl, rfl⟩)
    rw [h1, h2]
    cases hv : T ⟨(x, y), h⟩ with
    | none => exact absurd hv hs
    | some b => cases b <;> simp
  · obtain ⟨h1, h2⟩ := recordedForward_iff T y x h
    have hs := hT ⟨(y, x), h⟩ (Or.inr ⟨rfl, rfl⟩)
    rw [h1, h2]
    cases hv : T ⟨(y, x), h⟩ with
    | none => exact absurd hv hs
    | some b => cases b <;> simp

structure Good (L h : ℕ) (P : PivotState n) : Prop where
  disj : (P.slots.map Prod.fst).Pairwise Disjoint
  ne : ∀ Ud ∈ P.slots, Ud.1.Nonempty
  cover : ∀ x, ∃ Ud ∈ P.slots, x ∈ Ud.1
  depth : ∀ Ud ∈ P.slots, Ud.2 ≤ L
  fresh : ∀ Ud ∈ P.slots, ∀ e : Pair n, e.1.1 ∈ Ud.1 → e.1.2 ∈ Ud.1 → P.interaction.ledger e = none
  reqnd : P.requests.Nodup
  reqacq : ∀ e ∈ P.requests, P.interaction.ledger e ≠ none
  ok : OnlineOK h P.interaction

theorem good_start (L h : ℕ) (hn : 0 < n) : Good L h (pivotStart (n := n) (initialState n)) := by
  refine ⟨by simp [pivotStart], ?_, ?_, ?_, ?_, by simp [pivotStart], by simp [pivotStart], ?_⟩
  · intro Ud hUd
    simp [pivotStart] at hUd; subst hUd
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  · intro x; exact ⟨(Finset.univ, 0), by simp [pivotStart], Finset.mem_univ _⟩
  · intro Ud hUd; simp [pivotStart] at hUd; subst hUd; simp
  · intro Ud _ e _ _; simp [pivotStart, initialState, emptyTranscript]
  · exact ⟨by simp [pivotStart, initialState], by simp [pivotStart, initialState]⟩

/-- The three children of a split partition the block. -/
theorem split_children (U : Finset (Fin n)) (p : Fin n) (hp : p ∈ U) (T : Transcript n)
    (hT : ∀ e ∈ starOf U p, T e ≠ none) :
    let left := U.filter fun i => RecordedForward T i p
    let right := U.filter fun i => RecordedForward T p i
    Disjoint left right ∧ p ∉ left ∧ p ∉ right ∧ ∀ x ∈ U, x = p ∨ x ∈ left ∨ x ∈ right := by
  intro left right
  have hdich : ∀ x ∈ U, x ≠ p → (RecordedForward T x p ∨ RecordedForward T p x) ∧
      ¬ (RecordedForward T x p ∧ RecordedForward T p x) := by
    intro x hx hxp
    apply recorded_dichotomy T x p hxp
    intro e he
    apply hT e
    rw [mem_starOf]
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inr h2, h1 ▸ hx, h2 ▸ hp⟩
    · exact ⟨Or.inl h1, h1 ▸ hp, h2 ▸ hx⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hl hr
    have hx := (Finset.mem_filter.1 hl).1
    have hxp : x ≠ p := by rintro rfl; exact not_recordedForward_self T x (Finset.mem_filter.1 hl).2
    exact (hdich x hx hxp).2 ⟨(Finset.mem_filter.1 hl).2, (Finset.mem_filter.1 hr).2⟩
  · intro h; exact not_recordedForward_self T p (Finset.mem_filter.1 h).2
  · intro h; exact not_recordedForward_self T p (Finset.mem_filter.1 h).2
  · intro x hx
    by_cases hxp : x = p
    · exact Or.inl hxp
    · rcases (hdich x hx hxp).1 with h | h
      · exact Or.inr (Or.inl (Finset.mem_filter.2 ⟨hx, h⟩))
      · exact Or.inr (Or.inr (Finset.mem_filter.2 ⟨hx, h⟩))

theorem pairwise_replace {α : Type} (A B C : List (Finset α)) (X : Finset α)
    (h : (A ++ X :: B).Pairwise Disjoint) (hC : C.Pairwise Disjoint) (hsub : ∀ c ∈ C, c ⊆ X) :
    (A ++ C ++ B).Pairwise Disjoint := by
  rw [List.pairwise_append] at h
  obtain ⟨hA, hXB, hAXB⟩ := h
  rw [List.pairwise_cons] at hXB
  obtain ⟨hXb, hB⟩ := hXB
  rw [List.append_assoc, List.pairwise_append, List.pairwise_append]
  refine ⟨hA, ⟨hC, hB, ?_⟩, ?_⟩
  · intro c hc b hb
    exact Disjoint.mono_left (hsub c hc) (hXb b hb)
  · intro a ha y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact Disjoint.mono_right (hsub y hy) (hAXB a ha X List.mem_cons_self)
    · exact hAXB a ha y (List.mem_cons_of_mem _ hy)

theorem slots_decomp (slots : PivotSlots n) (k : ℕ) (hk : k < slots.length) :
    slots = slots.take k ++ slots[k] :: slots.drop (k + 1) := by
  conv_lhs => rw [← List.take_append_drop k slots]
  rw [List.drop_eq_getElem_cons hk]

/-- The children list of a split. -/
def childrenOf (left right : Finset (Fin n)) (p : Fin n) (d : ℕ) : List (Finset (Fin n) × ℕ) :=
  [(left, d + 1), ({p}, d + 1), (right, d + 1)].filter fun child => decide (0 < child.1.card)

theorem splitAt_eq (W : ComparisonWorld n) (h : ℕ) (P : PivotState n) (k : ℕ) (p : Fin n) :
    splitAt W h P k p =
      let Ud := (P.slots[k]?).getD (∅, 0)
      let S := foldRead W h (starOf Ud.1 p) P.interaction
      ⟨P.slots.take k ++ childrenOf (Ud.1.filter fun i => RecordedForward S.ledger i p)
        (Ud.1.filter fun i => RecordedForward S.ledger p i) p Ud.2 ++ P.slots.drop (k + 1),
        S, P.requests ++ starOf Ud.1 p⟩ := rfl

theorem good_split (L h : ℕ) (W : ComparisonWorld n) (P : PivotState n) (hP : Good L h P) (k : ℕ)
    (hk : k < P.slots.length) (hd : (P.slots[k]).2 < L) (p : Fin n) (hp : p ∈ (P.slots[k]).1) :
    Good L h (splitAt W h P k p) := by
  set U := (P.slots[k]).1
  set d := (P.slots[k]).2
  have hUd : (P.slots[k]?).getD (∅, 0) = (U, d) := by
    rw [List.getElem?_eq_getElem hk]; rfl
  rw [splitAt_eq]
  simp only [hUd]
  set S' := foldRead W h (starOf U p) P.interaction
  have hslotk : P.slots[k] ∈ P.slots := List.getElem_mem hk
  have hfreshU : ∀ e ∈ starOf U p, P.interaction.ledger e = none := by
    intro e he
    rw [mem_starOf] at he
    exact hP.fresh _ hslotk e he.2.1 he.2.2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := foldRead_spec W h (starOf U p) P.interaction (starOf_nodup U p)
    hfreshU hP.ok
  obtain ⟨hlr, hpl, hpr, hcov⟩ := split_children U p hp S'.ledger f3
  set left := U.filter fun i => RecordedForward S'.ledger i p
  set right := U.filter fun i => RecordedForward S'.ledger p i
  have hdecomp := slots_decomp P.slots k hk
  have hmemslots : ∀ Ud, Ud ∈ P.slots.take k ++ childrenOf left right p d ++ P.slots.drop (k + 1) →
      Ud ∈ P.slots ∨ Ud ∈ childrenOf left right p d := by
    intro Ud hUd
    rcases List.mem_append.1 hUd with h1 | h1
    · rcases List.mem_append.1 h1 with h2 | h2
      · exact Or.inl (List.mem_of_mem_take h2)
      · exact Or.inr h2
    · exact Or.inl (List.mem_of_mem_drop h1)
  have hchild : ∀ c ∈ childrenOf left right p d, (c.1 = left ∨ c.1 = {p} ∨ c.1 = right) ∧ c.2 = d + 1 ∧
      c.1.Nonempty := by
    intro c hc
    unfold childrenOf at hc
    rw [List.mem_filter] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hc3 : 0 < c.1.card := of_decide_eq_true hc2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc1
    rcases hc1 with rfl | rfl | rfl
    · exact ⟨Or.inl rfl, rfl, Finset.card_pos.1 hc3⟩
    · exact ⟨Or.inr (Or.inl rfl), rfl, Finset.card_pos.1 hc3⟩
    · exact ⟨Or.inr (Or.inr rfl), rfl, Finset.card_pos.1 hc3⟩
  have hchildsub : ∀ c ∈ childrenOf left right p d, c.1 ⊆ U := by
    intro c hc
    rcases (hchild c hc).1 with h1 | h1 | h1 <;> rw [h1]
    · exact Finset.filter_subset _ _
    · exact Finset.singleton_subset_iff.2 hp
    · exact Finset.filter_subset _ _
  -- the other slots are disjoint from U
  have hother : ∀ Ud ∈ P.slots.take k ++ P.slots.drop (k + 1), Disjoint Ud.1 U := by
    have hd := hP.disj
    rw [hdecomp, List.map_append, List.map_cons, List.pairwise_append] at hd
    obtain ⟨_, hd2, hd3⟩ := hd
    rw [List.pairwise_cons] at hd2
    intro Ud hUd
    rcases List.mem_append.1 hUd with h1 | h1
    · exact hd3 Ud.1 (List.mem_map_of_mem h1) U (List.mem_cons_self)
    · exact (hd2.1 Ud.1 (List.mem_map_of_mem h1)).symm
  have hledger_other : ∀ e : Pair n, ¬ (e.1.1 ∈ U ∧ e.1.2 ∈ U) → S'.ledger e = P.interaction.ledger e := by
    intro e he
    apply f1
    intro hs
    rw [mem_starOf] at hs
    exact he ⟨hs.2.1, hs.2.2⟩
  constructor
  · -- disjointness
    simp only [List.map_append]
    have hd := hP.disj
    rw [hdecomp, List.map_append, List.map_cons] at hd
    apply pairwise_replace _ _ _ U hd
    · have hsub : ((childrenOf left right p d).map Prod.fst).Sublist [left, {p}, right] := by
        unfold childrenOf
        exact List.Sublist.map Prod.fst List.filter_sublist
      apply List.Pairwise.sublist hsub
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact Finset.disjoint_singleton_right.2 hpl
        · exact hlr
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha
        exact Finset.disjoint_singleton_left.2 hpr
    · intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact hchildsub c' hc'
  · intro Ud hUd
    rcases hmemslots Ud hUd with h1 | h1
    · exact hP.ne Ud h1
    · exact (hchild Ud h1).2.2
  · intro x
    obtain ⟨Ud, hUd, hx⟩ := hP.cover x
    rw [hdecomp] at hUd
    rcases List.mem_append.1 hUd with h1 | h1
    · exact ⟨Ud, List.mem_append_left _ (List.mem_append_left _ h1), hx⟩
    · rcases List.mem_cons.1 h1 with rfl | h1
      · -- x ∈ U
        rcases hcov x hx with rfl | hl | hr
        · refine ⟨({x}, d + 1), List.mem_append_left _ (List.mem_append_right _ ?_), by simp⟩
          unfold childrenOf; rw [List.mem_filter]; exact ⟨by simp, by simp⟩
        · refine ⟨(left, d + 1), List.mem_append_left _ (List.mem_append_right _ ?_), hl⟩
          unfold childrenOf; rw [List.mem_filter]
          exact ⟨by simp, decide_eq_true (Finset.card_pos.2 ⟨x, hl⟩)⟩
        · refine ⟨(right, d + 1), List.mem_append_left _ (List.mem_append_right _ ?_), hr⟩
          unfold childrenOf; rw [List.mem_filter]
          exact ⟨by simp, decide_eq_true (Finset.card_pos.2 ⟨x, hr⟩)⟩
      · exact ⟨Ud, List.mem_append_right _ h1, hx⟩
  · intro Ud hUd
    rcases hmemslots Ud hUd with h1 | h1
    · exact hP.depth Ud h1
    · rw [(hchild Ud h1).2.1]; exact hd
  · intro Ud hUd e he1 he2
    show S'.ledger e = none
    rcases List.mem_append.1 hUd with h1 | h1
    · rcases List.mem_append.1 h1 with h2 | h2
      · have hdj := hother Ud (List.mem_append_left _ h2)
        rw [hledger_other e (fun h' => Finset.disjoint_left.1 hdj he1 h'.1)]
        exact hP.fresh Ud (List.mem_of_mem_take h2) e he1 he2
      · -- inside a child: no endpoint is p unless singleton
        have hsub := hchildsub Ud h2
        rcases (hchild Ud h2).1 with hc | hc | hc
        · rw [f1]
          · exact hP.fresh _ hslotk e (hsub he1) (hsub he2)
          · rw [mem_starOf]; rintro ⟨h3, -⟩
            rw [hc] at he1 he2
            rcases h3 with h3 | h3
            · rw [h3] at he1; exact hpl he1
            · rw [h3] at he2; exact hpl he2
        · rw [hc] at he1 he2
          simp only [Finset.mem_singleton] at he1 he2
          exact absurd (he1.trans he2.symm) e.2.ne
        · rw [f1]
          · exact hP.fresh _ hslotk e (hsub he1) (hsub he2)
          · rw [mem_starOf]; rintro ⟨h3, -⟩
            rw [hc] at he1 he2
            rcases h3 with h3 | h3
            · rw [h3] at he1; exact hpr he1
            · rw [h3] at he2; exact hpr he2
    · have hdj := hother Ud (List.mem_append_right _ h1)
      rw [hledger_other e (fun h' => Finset.disjoint_left.1 hdj he1 h'.1)]
      exact hP.fresh Ud (List.mem_of_mem_drop h1) e he1 he2
  · -- requests nodup
    rw [List.nodup_append]
    refine ⟨hP.reqnd, starOf_nodup U p, ?_⟩
    intro e he e' he' hee
    subst hee
    exact hP.reqacq e he (hfreshU e he')
  · intro e he
    rcases List.mem_append.1 he with h1 | h1
    · by_cases hs : e ∈ starOf U p
      · exact f3 e hs
      · rw [f1 e hs]; exact hP.reqacq e h1
    · exact f3 e h1
  · exact f6

end RQCPivot



noncomputable section

namespace RQCPivot
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The flattened order of a pivot state. -/
def flat (P : PivotState n) : List (Fin n) := P.slots.flatMap fun Ud => Ud.1.sort (· ≤ ·)

theorem pivotOutput_eq (P : PivotState n) (i : Fin n) : pivotOutput P i = ((flat P).idxOf i : ℝ) := rfl

def sameSlot (P : PivotState n) (x y : Fin n) : Prop := ∃ Ud ∈ P.slots, x ∈ Ud.1 ∧ y ∈ Ud.1

theorem flat_children (left right : Finset (Fin n)) (p : Fin n) (d : ℕ) :
    (childrenOf left right p d).flatMap (fun Ud => Ud.1.sort (· ≤ ·)) =
      left.sort (· ≤ ·) ++ [p] ++ right.sort (· ≤ ·) := by
  unfold childrenOf
  by_cases hl : left.Nonempty <;> by_cases hr : right.Nonempty
  · simp [List.filter_cons, hl, hr]
  · rw [Finset.not_nonempty_iff_eq_empty] at hr; subst hr; simp [List.filter_cons, hl]
  · rw [Finset.not_nonempty_iff_eq_empty] at hl; subst hl; simp [List.filter_cons, hr]
  · rw [Finset.not_nonempty_iff_eq_empty] at hl hr; subst hl hr; simp [List.filter_cons]

theorem flat_split (W : ComparisonWorld n) (h : ℕ) (P : PivotState n) (k : ℕ) (hk : k < P.slots.length)
    (p : Fin n) :
    let U := (P.slots[k]).1
    let S := foldRead W h (starOf U p) P.interaction
    flat (splitAt W h P k p) = (P.slots.take k).flatMap (fun Ud => Ud.1.sort (· ≤ ·)) ++
      ((U.filter fun i => RecordedForward S.ledger i p).sort (· ≤ ·) ++ [p] ++
        (U.filter fun i => RecordedForward S.ledger p i).sort (· ≤ ·)) ++
      (P.slots.drop (k + 1)).flatMap (fun Ud => Ud.1.sort (· ≤ ·)) ∧
    flat P = (P.slots.take k).flatMap (fun Ud => Ud.1.sort (· ≤ ·)) ++ U.sort (· ≤ ·) ++
      (P.slots.drop (k + 1)).flatMap (fun Ud => Ud.1.sort (· ≤ ·)) := by
  intro U S
  have hUd : (P.slots[k]?).getD (∅, 0) = (U, (P.slots[k]).2) := by
    rw [List.getElem?_eq_getElem hk]; rfl
  constructor
  · rw [splitAt_eq]; simp only [hUd]
    unfold flat
    simp only [List.flatMap_append, flat_children]
    rfl
  · unfold flat
    have e : P.slots.flatMap (fun Ud => Ud.1.sort (· ≤ ·)) =
        (P.slots.take k ++ P.slots[k] :: P.slots.drop (k + 1)).flatMap (fun Ud => Ud.1.sort (· ≤ ·)) := by
      rw [← slots_decomp P.slots k hk]
    rw [e, List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Position facts for a three-part list with disjoint parts. -/
theorem idxOf_mid_eq {α : Type} [DecidableEq α] (A B B' C : List α) (x : α) (hxA : x ∉ A) (hxB : x ∉ B)
    (hxB' : x ∉ B') (hlen : B.length = B'.length) :
    (A ++ B ++ C).idxOf x = (A ++ B' ++ C).idxOf x := by
  rw [List.append_assoc, List.append_assoc, List.idxOf_append_of_notMem hxA,
    List.idxOf_append_of_notMem hxA, List.idxOf_append_of_notMem hxB, List.idxOf_append_of_notMem hxB', hlen]

theorem idxOf_left_eq {α : Type} [DecidableEq α] (A B B' C : List α) (x : α) (hxA : x ∈ A) :
    (A ++ B ++ C).idxOf x = (A ++ B' ++ C).idxOf x := by
  rw [List.append_assoc, List.append_assoc, List.idxOf_append_of_mem hxA, List.idxOf_append_of_mem hxA]

theorem idxOf_in_mid {α : Type} [DecidableEq α] (A B C : List α) (x : α) (hxA : x ∉ A) (hxB : x ∈ B) :
    (A ++ B ++ C).idxOf x = A.length + B.idxOf x := by
  rw [List.append_assoc, List.idxOf_append_of_notMem hxA, List.idxOf_append_of_mem hxB]

theorem idxOf_mid_bounds {α : Type} [DecidableEq α] (A B C : List α) (x : α) (hxA : x ∉ A) (hxB : x ∈ B) :
    A.length ≤ (A ++ B ++ C).idxOf x ∧ (A ++ B ++ C).idxOf x < A.length + B.length := by
  rw [idxOf_in_mid A B C x hxA hxB]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (List.idxOf_lt_length_iff.2 hxB) _⟩

theorem idxOf_outside_bounds {α : Type} [DecidableEq α] (A B C : List α) (x : α) (hxB : x ∉ B)
    (hx : x ∈ A ∨ x ∈ C) (hAC : x ∈ A → x ∉ C) :
    (A ++ B ++ C).idxOf x < A.length ∨ A.length + B.length ≤ (A ++ B ++ C).idxOf x := by
  rcases hx with hx | hx
  · left
    rw [List.append_assoc, List.idxOf_append_of_mem hx]
    exact List.idxOf_lt_length_iff.2 hx
  · right
    by_cases hxA : x ∈ A
    · exact absurd hx (hAC hxA)
    · rw [List.append_assoc, List.idxOf_append_of_notMem hxA, List.idxOf_append_of_notMem hxB]
      omega

/-- Wrongly separated pairs. -/
def phiSet (r : Rank n) (P : PivotState n) : Finset (Pair n) :=
  Finset.univ.filter fun e => ¬ sameSlot P e.1.1 e.1.2 ∧
    ¬ ((flat P).idxOf e.1.1 < (flat P).idxOf e.1.2 ↔ r e.1.1 < r e.1.2)

/-- Misclassified members of the split block. -/
def misSet (r : Rank n) (U : Finset (Fin n)) (T : Transcript n) (p : Fin n) : Finset (Fin n) :=
  U.filter fun x => x ≠ p ∧ ¬ (RecordedForward T x p ↔ r x < r p)

/-- Positions inside `left ++ [p] ++ right`. -/
theorem idx_three (L R : List (Fin n)) (p : Fin n) (hpL : p ∉ L) (hLR : ∀ x ∈ L, x ∉ R) :
    (∀ x ∈ L, (L ++ [p] ++ R).idxOf x < L.length) ∧ (L ++ [p] ++ R).idxOf p = L.length ∧
    (∀ x ∈ R, x ≠ p → L.length < (L ++ [p] ++ R).idxOf x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [List.append_assoc, List.idxOf_append_of_mem hx]; exact List.idxOf_lt_length_iff.2 hx
  · rw [List.append_assoc, List.idxOf_append_of_notMem hpL]; simp
  · intro x hx hxp
    have hxL : x ∉ L := fun h => hLR x h hx
    rw [List.append_assoc, List.idxOf_append_of_notMem hxL, List.idxOf_append_of_notMem (by simpa using hxp)]
    simp

theorem phi_step (W : ComparisonWorld n) (h L : ℕ) (P : PivotState n) (hP : Good L h P) (k : ℕ)
    (hk : k < P.slots.length) (p : Fin n) (hp : p ∈ (P.slots[k]).1) (r : Rank n) :
    ((phiSet r (splitAt W h P k p)).card : ℝ) ≤ (phiSet r P).card +
      (((P.slots[k]).1.card : ℝ) - 1) *
        (misSet r (P.slots[k]).1 (foldRead W h (starOf (P.slots[k]).1 p) P.interaction).ledger p).card := by
  set U := (P.slots[k]).1 with hU
  set S := foldRead W h (starOf U p) P.interaction
  set T := S.ledger
  set left := U.filter fun i => RecordedForward T i p
  set right := U.filter fun i => RecordedForward T p i
  set Mis := misSet r U T p
  set A := (P.slots.take k).flatMap (fun Ud => Ud.1.sort (· ≤ ·))
  set C := (P.slots.drop (k + 1)).flatMap (fun Ud => Ud.1.sort (· ≤ ·))
  set B := U.sort (· ≤ ·)
  set B' := left.sort (· ≤ ·) ++ [p] ++ right.sort (· ≤ ·)
  have hF' : flat (splitAt W h P k p) = A ++ B' ++ C := (flat_split W h P k hk p).1
  have hF : flat P = A ++ B ++ C := (flat_split W h P k hk p).2
  have hslotk : P.slots[k] ∈ P.slots := List.getElem_mem hk
  have hfreshU : ∀ e ∈ starOf U p, P.interaction.ledger e = none := by
    intro e he; rw [mem_starOf] at he; exact hP.fresh _ hslotk e he.2.1 he.2.2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := foldRead_spec W h (starOf U p) P.interaction (starOf_nodup U p)
    hfreshU hP.ok
  obtain ⟨hlr, hpl, hpr, hcov⟩ := split_children U p hp T f3
  have hdecomp := slots_decomp P.slots k hk
  -- disjointness of the three parts
  have hdisjO : ∀ Ud ∈ P.slots.take k ++ P.slots.drop (k + 1), Disjoint Ud.1 U := by
    have hd := hP.disj
    rw [hdecomp, List.map_append, List.map_cons, List.pairwise_append] at hd
    obtain ⟨_, hd2, hd3⟩ := hd
    rw [List.pairwise_cons] at hd2
    intro Ud hUd
    rcases List.mem_append.1 hUd with h1 | h1
    · exact hd3 Ud.1 (List.mem_map_of_mem h1) U (List.mem_cons_self)
    · exact (hd2.1 Ud.1 (List.mem_map_of_mem h1)).symm
  have hdisjAC : ∀ Ud ∈ P.slots.take k, ∀ Ud' ∈ P.slots.drop (k + 1), Disjoint Ud.1 Ud'.1 := by
    have hd := hP.disj
    rw [hdecomp, List.map_append, List.map_cons, List.pairwise_append] at hd
    intro Ud h1 Ud' h2
    exact hd.2.2 Ud.1 (List.mem_map_of_mem h1) Ud'.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem h2))
  have memA : ∀ x, x ∈ A ↔ ∃ Ud ∈ P.slots.take k, x ∈ Ud.1 := by
    intro x; simp [A, List.mem_flatMap]
  have memC : ∀ x, x ∈ C ↔ ∃ Ud ∈ P.slots.drop (k + 1), x ∈ Ud.1 := by
    intro x; simp [C, List.mem_flatMap]
  have memB : ∀ x, x ∈ B ↔ x ∈ U := by intro x; simp [B]
  have memB' : ∀ x, x ∈ B' ↔ x ∈ U := by
    intro x
    simp only [B', List.mem_append, Finset.mem_sort, List.mem_singleton]
    constructor
    · rintro ((h1 | rfl) | h1)
      · exact (Finset.mem_filter.1 h1).1
      · exact hp
      · exact (Finset.mem_filter.1 h1).1
    · intro hx
      rcases hcov x hx with rfl | h1 | h1
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h1
  have hUA : ∀ x ∈ U, x ∉ A := by
    intro x hx hA; obtain ⟨Ud, hUd, hxU⟩ := (memA x).1 hA
    exact Finset.disjoint_left.1 (hdisjO Ud (List.mem_append_left _ hUd)) hxU hx
  have hUC : ∀ x ∈ U, x ∉ C := by
    intro x hx hC; obtain ⟨Ud, hUd, hxU⟩ := (memC x).1 hC
    exact Finset.disjoint_left.1 (hdisjO Ud (List.mem_append_right _ hUd)) hxU hx
  have hAC : ∀ x, x ∈ A → x ∉ C := by
    intro x hA hC
    obtain ⟨Ud, hUd, hx1⟩ := (memA x).1 hA
    obtain ⟨Ud', hUd', hx2⟩ := (memC x).1 hC
    exact Finset.disjoint_left.1 (hdisjAC Ud hUd Ud' hUd') hx1 hx2
  have hcover : ∀ x, x ∉ U → x ∈ A ∨ x ∈ C := by
    intro x hx
    obtain ⟨Ud, hUd, hxU⟩ := hP.cover x
    rw [hdecomp] at hUd
    rcases List.mem_append.1 hUd with h1 | h1
    · exact Or.inl ((memA x).2 ⟨Ud, h1, hxU⟩)
    · rcases List.mem_cons.1 h1 with rfl | h1
      · exact absurd hxU hx
      · exact Or.inr ((memC x).2 ⟨Ud, h1, hxU⟩)
  have hlenB : B.length = B'.length := by
    simp only [B, B', Finset.length_sort, List.length_append, List.length_singleton]
    have : U = left ∪ {p} ∪ right := by
      ext x; constructor
      · intro hx
        simp only [Finset.mem_union, Finset.mem_singleton]
        rcases hcov x hx with h1 | h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inr h1
      · intro hx; simp only [Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with (h1 | rfl) | h1
        · exact (Finset.mem_filter.1 h1).1
        · exact hp
        · exact (Finset.mem_filter.1 h1).1
    rw [this, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · simp
    · exact Finset.disjoint_singleton_right.2 hpl
    · rw [Finset.disjoint_union_left]
      exact ⟨hlr, Finset.disjoint_singleton_left.2 hpr⟩
  have hlenB0 : B.length = U.card := by simp [B]
  -- index facts
  set idx := (flat P).idxOf
  set idx' := (flat (splitAt W h P k p)).idxOf
  have hidx_out : ∀ x, x ∉ U → idx' x = idx x := by
    intro x hx
    simp only [idx, idx', hF, hF']
    by_cases hxA : x ∈ A
    · exact (idxOf_left_eq A B B' C x hxA).symm
    · exact (idxOf_mid_eq A B B' C x hxA (fun h' => hx ((memB x).1 h')) (fun h' => hx ((memB' x).1 h'))
        hlenB).symm
  have hidx_in : ∀ x ∈ U, (A.length ≤ idx x ∧ idx x < A.length + U.card) ∧
      (A.length ≤ idx' x ∧ idx' x < A.length + U.card) := by
    intro x hx
    simp only [idx, idx', hF, hF']
    refine ⟨?_, ?_⟩
    · have := idxOf_mid_bounds A B C x (hUA x hx) ((memB x).2 hx); rw [hlenB0] at this; exact this
    · have := idxOf_mid_bounds A B' C x (hUA x hx) ((memB' x).2 hx); rw [← hlenB, hlenB0] at this
      exact this
  have hidx_outr : ∀ x, x ∉ U → idx x < A.length ∨ A.length + U.card ≤ idx x := by
    intro x hx
    simp only [idx, hF]
    have := idxOf_outside_bounds A B C x (fun h' => hx ((memB x).1 h')) (hcover x hx) (hAC x)
    rw [hlenB0] at this; exact this
  -- same-slot facts
  have hslots' : (splitAt W h P k p).slots = P.slots.take k ++ childrenOf left right p (P.slots[k]).2 ++
      P.slots.drop (k + 1) := by
    rw [splitAt_eq]
    have hUd : (P.slots[k]?).getD (∅, 0) = (U, (P.slots[k]).2) := by
      rw [List.getElem?_eq_getElem hk]; rfl
    simp only [hUd]
    rfl
  have hchildsub : ∀ c ∈ childrenOf left right p (P.slots[k]).2, c.1 ⊆ U := by
    intro c hc
    unfold childrenOf at hc
    rw [List.mem_filter] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc.1 with rfl | rfl | rfl
    · exact Finset.filter_subset _ _
    · exact Finset.singleton_subset_iff.2 hp
    · exact Finset.filter_subset _ _
  have hsame_out : ∀ x y, ¬ (x ∈ U ∧ y ∈ U) →
      (sameSlot (splitAt W h P k p) x y ↔ sameSlot P x y) := by
    intro x y hxy
    unfold sameSlot
    rw [hslots']
    conv_rhs => rw [hdecomp]
    constructor
    · rintro ⟨Ud, hUd, hx, hy⟩
      rcases List.mem_append.1 hUd with h1 | h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact ⟨Ud, List.mem_append_left _ h2, hx, hy⟩
        · exact absurd ⟨hchildsub Ud h2 hx, hchildsub Ud h2 hy⟩ hxy
      · exact ⟨Ud, List.mem_append_right _ (List.mem_cons_of_mem _ h1), hx, hy⟩
    · rintro ⟨Ud, hUd, hx, hy⟩
      rcases List.mem_append.1 hUd with h1 | h1
      · exact ⟨Ud, List.mem_append_left _ (List.mem_append_left _ h1), hx, hy⟩
      · rcases List.mem_cons.1 h1 with rfl | h1
        · exact absurd ⟨hx, hy⟩ hxy
        · exact ⟨Ud, List.mem_append_right _ h1, hx, hy⟩
  -- the subset claim
  set Wset := Finset.univ.filter fun e : Pair n => e.1.1 ∈ U ∧ e.1.2 ∈ U ∧ (e.1.1 ∈ Mis ∨ e.1.2 ∈ Mis)
  have hsub : phiSet r (splitAt W h P k p) ⊆ phiSet r P ∪ Wset := by
    intro e he
    simp only [phiSet, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hns, hwrong⟩ := he
    by_cases hin : e.1.1 ∈ U ∧ e.1.2 ∈ U
    · apply Finset.mem_union_right
      simp only [Wset, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hin.1, hin.2, ?_⟩
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      have hnotmis : ∀ x ∈ U, x ∉ Mis → x ≠ p → (RecordedForward T x p ↔ r x < r p) := by
        intro x hx hxm hxp
        by_contra hh
        exact hxm (Finset.mem_filter.2 ⟨hx, hxp, hh⟩)
      have hgood : ∀ x ∈ U, x ∉ Mis → (x ∈ left → r x < r p) ∧ (x ∈ right → r p < r x) := by
        intro x hx hxm
        refine ⟨fun hl => ?_, fun hr => ?_⟩
        · have hxp : x ≠ p := by rintro rfl; exact hpl hl
          exact (hnotmis x hx hxm hxp).1 (Finset.mem_filter.1 hl).2
        · have hxp : x ≠ p := by rintro rfl; exact hpr hr
          have hnl : x ∉ left := fun hl => Finset.disjoint_left.1 hlr hl hr
          have hnrec : ¬ RecordedForward T x p := fun hrec => hnl (Finset.mem_filter.2 ⟨hx, hrec⟩)
          have hnlt : ¬ r x < r p := fun hlt => hnrec ((hnotmis x hx hxm hxp).2 hlt)
          have hne : r x ≠ r p := fun h' => hxp (r.injective h')
          exact lt_of_le_of_ne (not_lt.1 hnlt) (Ne.symm hne)
      -- positions inside B'
      have hpL : p ∉ left.sort (· ≤ ·) := fun h' => hpl ((Finset.mem_sort _).1 h')
      have hLR : ∀ x ∈ left.sort (· ≤ ·), x ∉ right.sort (· ≤ ·) := by
        intro x hx hx'
        rw [Finset.mem_sort] at hx hx'
        exact Finset.disjoint_left.1 hlr hx hx'
      obtain ⟨q1, q2, q3⟩ := idx_three (left.sort (· ≤ ·)) (right.sort (· ≤ ·)) p hpL hLR
      replace q1 : ∀ x ∈ left.sort (· ≤ ·), B'.idxOf x < (left.sort (· ≤ ·)).length := q1
      replace q2 : B'.idxOf p = (left.sort (· ≤ ·)).length := q2
      replace q3 : ∀ x ∈ right.sort (· ≤ ·), x ≠ p → (left.sort (· ≤ ·)).length < B'.idxOf x := q3
      have hpos : ∀ x ∈ U, idx' x = A.length + B'.idxOf x := by
        intro x hx
        simp only [idx', hF']
        exact idxOf_in_mid A B' C x (hUA x hx) ((memB' x).2 hx)
      have g1 := hgood _ hin.1 hc1
      have g2 := hgood _ hin.2 hc2
      have hne12 : e.1.1 ≠ e.1.2 := e.2.ne
      have hr12 : r e.1.1 ≠ r e.1.2 := fun h' => hne12 (r.injective h')
      -- same child is impossible
      have hsame_child : ∀ c ∈ childrenOf left right p (P.slots[k]).2, ¬ (e.1.1 ∈ c.1 ∧ e.1.2 ∈ c.1) := by
        intro c hc hboth
        apply hns
        refine ⟨c, ?_, hboth⟩
        rw [hslots']
        exact List.mem_append_left _ (List.mem_append_right _ hc)
      have hmemL : ∀ x ∈ left, (left, (P.slots[k]).2 + 1) ∈ childrenOf left right p (P.slots[k]).2 := by
        intro x hx; unfold childrenOf; rw [List.mem_filter]
        exact ⟨by simp, decide_eq_true (Finset.card_pos.2 ⟨x, hx⟩)⟩
      have hmemR : ∀ x ∈ right, (right, (P.slots[k]).2 + 1) ∈ childrenOf left right p (P.slots[k]).2 := by
        intro x hx; unfold childrenOf; rw [List.mem_filter]
        exact ⟨by simp, decide_eq_true (Finset.card_pos.2 ⟨x, hx⟩)⟩
      apply hwrong
      show idx' e.1.1 < idx' e.1.2 ↔ r e.1.1 < r e.1.2
      rw [hpos _ hin.1, hpos _ hin.2, Nat.add_lt_add_iff_left]
      have hl1 : ∀ x, x ∈ left → x ∈ left.sort (· ≤ ·) := fun x hx => by simpa using hx
      have hr1 : ∀ x, x ∈ right → x ∈ right.sort (· ≤ ·) := fun x hx => by simpa using hx
      rcases hcov _ hin.1 with h1 | h1 | h1 <;> rcases hcov _ hin.2 with h2 | h2 | h2
      · exact absurd (h1.trans h2.symm) hne12
      · rw [h1, q2]
        have a2 := q1 _ (hl1 _ h2); have b2 := g2.1 h2
        exact iff_of_false (by omega) (fun h => lt_asymm h (h1 ▸ b2))
      · rw [h1, q2]
        have a2 := q3 _ (hr1 _ h2) (by rintro rfl; exact hpr h2); have b2 := g2.2 h2
        exact iff_of_true a2 (h1 ▸ b2)
      · rw [h2, q2]
        have a1 := q1 _ (hl1 _ h1); have b1 := g1.1 h1
        exact iff_of_true a1 (h2 ▸ b1)
      · exact absurd ⟨h1, h2⟩ (hsame_child _ (hmemL _ h1))
      · have a1 := q1 _ (hl1 _ h1); have a2 := q3 _ (hr1 _ h2) (by rintro rfl; exact hpr h2)
        have b1 := g1.1 h1; have b2 := g2.2 h2
        exact iff_of_true (by omega) (lt_trans b1 b2)
      · rw [h2, q2]
        have a1 := q3 _ (hr1 _ h1) (by rintro rfl; exact hpr h1); have b1 := g1.2 h1
        exact iff_of_false (by omega) (fun h => lt_asymm h (h2 ▸ b1))
      · have a1 := q3 _ (hr1 _ h1) (by rintro rfl; exact hpr h1); have a2 := q1 _ (hl1 _ h2)
        have b1 := g1.2 h1; have b2 := g2.1 h2
        exact iff_of_false (by omega) (fun h => lt_asymm h (lt_trans b2 b1))
      · exact absurd ⟨h1, h2⟩ (hsame_child _ (hmemR _ h1))
    · apply Finset.mem_union_left
      simp only [phiSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(hsame_out _ _ hin).not.1 hns, ?_⟩
      intro hiff
      apply hwrong
      refine Iff.trans ?_ hiff
      show idx' e.1.1 < idx' e.1.2 ↔ idx e.1.1 < idx e.1.2
      by_cases h1 : e.1.1 ∈ U
      · have h2 : e.1.2 ∉ U := fun h' => hin ⟨h1, h'⟩
        rw [hidx_out _ h2]
        have b1 := hidx_in _ h1
        rcases hidx_outr _ h2 with h3 | h3 <;> constructor <;> intro h4 <;> omega
      · rw [hidx_out _ h1]
        by_cases h2 : e.1.2 ∈ U
        · have b2 := hidx_in _ h2
          rcases hidx_outr _ h1 with h3 | h3 <;> constructor <;> intro h4 <;> omega
        · rw [hidx_out _ h2]
  have hatx : ∀ x ∈ U, (Finset.univ.filter fun e : Pair n => (e.1.1 = x ∨ e.1.2 = x) ∧ e.1.1 ∈ U ∧
      e.1.2 ∈ U).card ≤ U.card - 1 := by
    intro x hx
    rw [← Finset.card_erase_of_mem hx]
    apply Finset.card_le_card_of_injOn (fun e => if e.1.1 = x then e.1.2 else e.1.1)
    · intro e he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he
      have hne : e.1.1 ≠ e.1.2 := e.2.ne
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      split_ifs with h1
      · exact ⟨he.2.2, fun h2 => hne (h1.trans h2.symm)⟩
      · rcases he.1 with h3 | h3
        · exact absurd h3 h1
        · exact ⟨he.2.1, fun h2 => hne (h2.trans h3.symm)⟩
    · intro e he f hf hef
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he hf
      have h1 : e.1.1.val < e.1.2.val := e.2
      have h2 : f.1.1.val < f.1.2.val := f.2
      simp only at hef
      apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;>
        (split_ifs at hef with ha hb hb <;> simp only [Fin.ext_iff] at ha hb hef he hf <;> omega)
  have hWsub : Wset ⊆ Mis.biUnion (fun x => Finset.univ.filter fun e : Pair n =>
      (e.1.1 = x ∨ e.1.2 = x) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U) := by
    intro e he
    simp only [Wset, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [Finset.mem_biUnion]
    rcases he.2.2 with h1 | h1
    · exact ⟨_, h1, by simp [he.1, he.2.1]⟩
    · exact ⟨_, h1, by simp [he.1, he.2.1]⟩
  have hWcard : Wset.card ≤ Mis.card * (U.card - 1) := by
    refine le_trans (Finset.card_le_card hWsub) (le_trans Finset.card_biUnion_le ?_)
    have := Finset.sum_le_card_nsmul Mis _ (U.card - 1) (fun x hx => hatx x (Finset.mem_filter.1 hx).1)
    simpa [smul_eq_mul] using this
  have hU1 : 1 ≤ U.card := Finset.card_pos.2 ⟨p, hp⟩
  have h1 : (phiSet r (splitAt W h P k p)).card ≤ (phiSet r P).card + Wset.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h2 : ((phiSet r (splitAt W h P k p)).card : ℝ) ≤ (phiSet r P).card + Mis.card * (U.card - 1 : ℕ) := by
    have := le_trans h1 (Nat.add_le_add_left hWcard _)
    exact_mod_cast this
  rw [Nat.cast_sub hU1] at h2
  push_cast at h2
  linarith


end RQCPivot



noncomputable section

namespace RQCPivot
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def wt (L d : ℕ) : ℝ := (3 / 2 : ℝ) ^ d / (3 / 2) ^ L

def gpot (L d : ℕ) : ℝ := ∑ d' ∈ Finset.Ico d L, (2 + 2 * wt L (d' + 1))

theorem gpot_succ (L d : ℕ) (hd : d < L) : gpot L d = (2 + 2 * wt L (d + 1)) + gpot L (d + 1) := by
  unfold gpot
  rw [Finset.sum_eq_sum_Ico_succ_bot hd]

theorem gpot_nonneg (L d : ℕ) : 0 ≤ gpot L d := by
  unfold gpot; apply Finset.sum_nonneg; intro i _; unfold wt; positivity

def psi (L : ℕ) (P : PivotState n) : ℝ := (P.slots.map fun Ud => wt L Ud.2 * (Ud.1.card : ℝ) ^ 2).sum

def thetaE (L : ℕ) (P : PivotState n) (e : Pair n) : ℝ :=
  (P.slots.map fun Ud => if e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1 then gpot L Ud.2 else 0).sum

def theta (L : ℕ) (W : ComparisonWorld n) (P : PivotState n) : ℝ := ∑ e ∈ W.initial, thetaE L P e

theorem psi_split (W : ComparisonWorld n) (h L : ℕ) (P : PivotState n) (k : ℕ) (hk : k < P.slots.length)
    (p : Fin n) :
    let U := (P.slots[k]).1
    let d := (P.slots[k]).2
    let S := foldRead W h (starOf U p) P.interaction
    psi L (splitAt W h P k p) = psi L P - wt L d * (U.card : ℝ) ^ 2 +
      wt L (d + 1) * (((U.filter fun i => RecordedForward S.ledger i p).card : ℝ) ^ 2 + 1 +
        ((U.filter fun i => RecordedForward S.ledger p i).card : ℝ) ^ 2) := by
  intro U d S
  have hslots' : (splitAt W h P k p).slots = P.slots.take k ++ childrenOf
      (U.filter fun i => RecordedForward S.ledger i p) (U.filter fun i => RecordedForward S.ledger p i)
      p d ++ P.slots.drop (k + 1) := by
    rw [splitAt_eq]
    have hUd : (P.slots[k]?).getD (∅, 0) = (U, d) := by rw [List.getElem?_eq_getElem hk]; rfl
    simp only [hUd]
    rfl
  have hdecomp := slots_decomp P.slots k hk
  unfold psi
  rw [hslots']
  conv_rhs => rw [hdecomp]
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  have hch : ∀ (A B : Finset (Fin n)) (q : Fin n),
      ((childrenOf A B q d).map fun Ud => wt L Ud.2 * (Ud.1.card : ℝ) ^ 2).sum =
        wt L (d + 1) * ((A.card : ℝ) ^ 2 + 1 + (B.card : ℝ) ^ 2) := by
    intro A B q
    unfold childrenOf
    by_cases hA : A.Nonempty <;> by_cases hB : B.Nonempty
    · simp [List.filter_cons, hA, hB]; ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hB; subst hB; simp [List.filter_cons, hA]; ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hA; subst hA; simp [List.filter_cons, hB]; ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hA hB; subst hA hB; simp [List.filter_cons]
  rw [hch]
  ring

theorem theta_split (W : ComparisonWorld n) (h L : ℕ) (P : PivotState n) (hP : Good L h P) (k : ℕ)
    (hk : k < P.slots.length) (hd : (P.slots[k]).2 < L) (p : Fin n) (hp : p ∈ (P.slots[k]).1) :
    theta L W (splitAt W h P k p) ≤ theta L W P -
      (2 + 2 * wt L ((P.slots[k]).2 + 1)) *
        ((W.initial.filter fun e => e.1.1 ∈ (P.slots[k]).1 ∧ e.1.2 ∈ (P.slots[k]).1).card : ℝ) := by
  set U := (P.slots[k]).1
  set d := (P.slots[k]).2
  set S := foldRead W h (starOf U p) P.interaction
  set left := U.filter fun i => RecordedForward S.ledger i p
  set right := U.filter fun i => RecordedForward S.ledger p i
  have hslotk : P.slots[k] ∈ P.slots := List.getElem_mem hk
  have hfreshU : ∀ e ∈ starOf U p, P.interaction.ledger e = none := by
    intro e he; rw [mem_starOf] at he; exact hP.fresh _ hslotk e he.2.1 he.2.2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := foldRead_spec W h (starOf U p) P.interaction (starOf_nodup U p)
    hfreshU hP.ok
  obtain ⟨hlr, hpl, hpr, hcov⟩ := split_children U p hp S.ledger f3
  have hslots' : (splitAt W h P k p).slots = P.slots.take k ++ childrenOf left right p d ++
      P.slots.drop (k + 1) := by
    rw [splitAt_eq]
    have hUd : (P.slots[k]?).getD (∅, 0) = (U, d) := by rw [List.getElem?_eq_getElem hk]; rfl
    simp only [hUd]
    rfl
  have hdecomp := slots_decomp P.slots k hk
  have hdec : ∀ e : Pair n, thetaE L (splitAt W h P k p) e ≤ thetaE L P e -
      (if e.1.1 ∈ U ∧ e.1.2 ∈ U then (2 + 2 * wt L (d + 1)) else 0) := by
    intro e
    unfold thetaE
    rw [hslots']
    conv_rhs => rw [hdecomp]
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    have hch : ((childrenOf left right p d).map fun Ud =>
        if e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1 then gpot L Ud.2 else 0).sum ≤
        if e.1.1 ∈ U ∧ e.1.2 ∈ U then gpot L (d + 1) else 0 := by
      have hne : e.1.1 ≠ e.1.2 := e.2.ne
      have hg := gpot_nonneg L (d + 1)
      unfold childrenOf
      have key : ∀ (l : List (Finset (Fin n) × ℕ)),
          (l.filter fun child => decide (0 < child.1.card)).Sublist l := fun l => List.filter_sublist
      -- bound the filtered sum by the unfiltered one
      have hsub := key [(left, d + 1), ({p}, d + 1), (right, d + 1)]
      have hle : (([(left, d + 1), ({p}, d + 1), (right, d + 1)].filter fun child =>
          decide (0 < child.1.card)).map fun Ud =>
            if e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1 then gpot L Ud.2 else 0).sum ≤
          ([(left, d + 1), ({p}, d + 1), (right, d + 1)].map fun Ud =>
            if e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1 then gpot L Ud.2 else 0).sum := by
        apply List.Sublist.sum_le_sum (hsub.map _)
        intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; split_ifs <;> simp [gpot_nonneg]
      refine le_trans hle ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases hin : e.1.1 ∈ U ∧ e.1.2 ∈ U
      · rw [if_pos hin]
        have hs : ¬ (e.1.1 ∈ ({p} : Finset (Fin n)) ∧ e.1.2 ∈ ({p} : Finset (Fin n))) := by
          simp only [Finset.mem_singleton]; rintro ⟨h1, h2⟩; exact hne (h1.trans h2.symm)
        rw [if_neg hs]
        by_cases hl : e.1.1 ∈ left ∧ e.1.2 ∈ left
        · have hr : ¬ (e.1.1 ∈ right ∧ e.1.2 ∈ right) := fun hr =>
            Finset.disjoint_left.1 hlr hl.1 hr.1
          rw [if_pos hl, if_neg hr]; simp
        · rw [if_neg hl]; split_ifs <;> simp [hg]
      · rw [if_neg hin]
        have h1 : ¬ (e.1.1 ∈ left ∧ e.1.2 ∈ left) := fun h' =>
          hin ⟨(Finset.mem_filter.1 h'.1).1, (Finset.mem_filter.1 h'.2).1⟩
        have h2 : ¬ (e.1.1 ∈ ({p} : Finset (Fin n)) ∧ e.1.2 ∈ ({p} : Finset (Fin n))) := by
          simp only [Finset.mem_singleton]; rintro ⟨h1, h2⟩; exact hne (h1.trans h2.symm)
        have h3 : ¬ (e.1.1 ∈ right ∧ e.1.2 ∈ right) := fun h' =>
          hin ⟨(Finset.mem_filter.1 h'.1).1, (Finset.mem_filter.1 h'.2).1⟩
        rw [if_neg h1, if_neg h2, if_neg h3]; simp
    have hgd := gpot_succ L d hd
    by_cases hin : e.1.1 ∈ U ∧ e.1.2 ∈ U
    · rw [if_pos hin] at hch ⊢
      have : (P.slots[k]).1 = U := rfl
      simp only [this, if_pos hin]
      linarith
    · rw [if_neg hin] at hch ⊢
      have : (P.slots[k]).1 = U := rfl
      simp only [this, if_neg hin]
      linarith
  unfold theta
  calc ∑ e ∈ W.initial, thetaE L (splitAt W h P k p) e
      ≤ ∑ e ∈ W.initial, (thetaE L P e - (if e.1.1 ∈ U ∧ e.1.2 ∈ U then (2 + 2 * wt L (d + 1)) else 0)) :=
        Finset.sum_le_sum fun e _ => hdec e
    _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]
        ring

/-- The pair joining two distinct labels. -/
def pairOf (x y : Fin n) (h : x ≠ y) : Pair n :=
  if hxy : x < y then ⟨(x, y), hxy⟩ else ⟨(y, x), lt_of_le_of_ne (not_lt.1 hxy) h.symm⟩

theorem pairOf_mem (x y : Fin n) (h : x ≠ y) :
    ((pairOf x y h).1.1 = x ∧ (pairOf x y h).1.2 = y) ∨ ((pairOf x y h).1.1 = y ∧ (pairOf x y h).1.2 = x) := by
  unfold pairOf; split_ifs <;> simp

theorem recorded_truthful (T : Transcript n) (r : Rank n) (x p : Fin n) (hxp : x ≠ p)
    (hT : T (pairOf x p hxp) = some (truthful r (pairOf x p hxp))) :
    (RecordedForward T x p ↔ r x < r p) := by
  unfold pairOf at hT
  split_ifs at hT with hlt
  · rw [(recordedForward_iff T x p hlt).1, hT]; simp [truthful]
  · have hlt' : p < x := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hxp)
    rw [(recordedForward_iff T p x hlt').2, hT]
    simp only [truthful, Option.some.injEq, decide_eq_false_iff_not, not_lt]
    have hne : r x ≠ r p := fun h' => hxp (r.injective h')
    constructor
    · intro h; exact lt_of_le_of_ne h hne
    · intro h; exact h.le

theorem pairOf_inj (x x' p : Fin n) (hx : x ≠ p) (hx' : x' ≠ p) (h : pairOf x p hx = pairOf x' p hx') :
    x = x' := by
  rcases pairOf_mem x p hx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases pairOf_mem x' p hx' with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · rw [← a1, ← b1, h]
  · rw [h] at a1 a2; exact absurd (a1.symm.trans b1) hx
  · rw [h] at a1 a2; exact absurd (b1.symm.trans a1) hx'
  · rw [← a2, ← b2, h]

theorem mis_bound (W : ComparisonWorld n) (h L : ℕ) (P : PivotState n) (hP : Good L h P) (k : ℕ)
    (hk : k < P.slots.length) (p : Fin n) (hp : p ∈ (P.slots[k]).1) :
    let U := (P.slots[k]).1
    let S := foldRead W h (starOf U p) P.interaction
    ((misSet W.rank U S.ledger p).card : ℝ) ≤
      (W.initial.filter fun e => (e.1.1 = p ∨ e.1.2 = p) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U).card +
        ((S.online.card : ℝ) - P.interaction.online.card) := by
  intro U S
  have hslotk : P.slots[k] ∈ P.slots := List.getElem_mem hk
  have hfreshU : ∀ e ∈ starOf U p, P.interaction.ledger e = none := by
    intro e he; rw [mem_starOf] at he; exact hP.fresh _ hslotk e he.2.1 he.2.2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := foldRead_spec W h (starOf U p) P.interaction (starOf_nodup U p)
    hfreshU hP.ok
  set I := W.initial.filter fun e => (e.1.1 = p ∨ e.1.2 = p) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U
  set N := S.online \ P.interaction.online
  have hmap : ∀ x ∈ misSet W.rank U S.ledger p, ∃ hxp : x ≠ p, pairOf x p hxp ∈ I ∪ N := by
    intro x hx
    obtain ⟨hxU, hxp, hmis⟩ := Finset.mem_filter.1 hx
    refine ⟨hxp, ?_⟩
    have hstar : pairOf x p hxp ∈ starOf U p := by
      rw [mem_starOf]
      rcases pairOf_mem x p hxp with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact ⟨Or.inr a2, by rw [a1]; exact hxU, by rw [a2]; exact hp⟩
      · exact ⟨Or.inl a1, by rw [a1]; exact hp, by rw [a2]; exact hxU⟩
    rcases f2 _ hstar with h1 | h1 | h1
    · exact absurd (recorded_truthful _ _ x p hxp h1) hmis
    · apply Finset.mem_union_left
      rw [Finset.mem_filter]
      refine ⟨h1, (mem_starOf U p _).1 hstar⟩
    · exact Finset.mem_union_right _ h1
  have hcard : (misSet W.rank U S.ledger p).card ≤ (I ∪ N).card := by
    rcases (misSet W.rank U S.ledger p).eq_empty_or_nonempty with he | ⟨x0, hx0⟩
    · rw [he]; simp
    obtain ⟨hx0p, -⟩ := hmap x0 hx0
    let e0 := pairOf x0 p hx0p
    apply Finset.card_le_card_of_injOn (fun x => if hxp : x ≠ p then pairOf x p hxp else e0)
    · intro x hx
      obtain ⟨hxp, hmem⟩ := hmap x hx
      simp only [dif_pos hxp]; exact hmem
    · intro x hx x' hx' hxx
      obtain ⟨hxp, -⟩ := hmap x hx
      obtain ⟨hxp', -⟩ := hmap x' hx'
      simp only [dif_pos hxp, dif_pos hxp'] at hxx
      exact pairOf_inj x x' p hxp hxp' hxx
  have hN : (N.card : ℝ) = S.online.card - P.interaction.online.card := by
    rw [Finset.card_sdiff_of_subset f4, Nat.cast_sub (Finset.card_le_card f4)]
  have := le_trans hcard (Finset.card_union_le I N)
  have : ((misSet W.rank U S.ledger p).card : ℝ) ≤ I.card + N.card := by exact_mod_cast this
  rw [hN] at this; exact this

theorem left_dev (U : Finset (Fin n)) (p : Fin n) (hp : p ∈ U) (T : Transcript n) (r : Rank n)
    (hT : ∀ e ∈ starOf U p, T e ≠ none) :
    let left := U.filter fun i => RecordedForward T i p
    let right := U.filter fun i => RecordedForward T p i
    let pr := U.filter fun x => r x < r p
    |(left.card : ℝ) - pr.card| ≤ (misSet r U T p).card ∧ left.card + right.card + 1 = U.card ∧
      pr.card < U.card := by
  intro left right pr
  obtain ⟨hlr, hpl, hpr, hcov⟩ := split_children U p hp T hT
  have hd1 : left \ pr ⊆ misSet r U T p := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hl, hnp⟩ := hx
    have hxU := (Finset.mem_filter.1 hl).1
    refine Finset.mem_filter.2 ⟨hxU, by rintro rfl; exact hpl hl, ?_⟩
    intro hiff
    exact hnp (Finset.mem_filter.2 ⟨hxU, hiff.1 (Finset.mem_filter.1 hl).2⟩)
  have hd2 : pr \ left ⊆ misSet r U T p := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hpr', hnl⟩ := hx
    have hxU := (Finset.mem_filter.1 hpr').1
    have hxp : x ≠ p := by rintro rfl; exact lt_irrefl _ (Finset.mem_filter.1 hpr').2
    refine Finset.mem_filter.2 ⟨hxU, hxp, ?_⟩
    intro hiff
    exact hnl (Finset.mem_filter.2 ⟨hxU, hiff.2 (Finset.mem_filter.1 hpr').2⟩)
  have c1 := Finset.card_le_card hd1
  have c2 := Finset.card_le_card hd2
  have e1 : left.card ≤ pr.card + (left \ pr).card := by
    have := Finset.card_sdiff_add_card_inter left pr
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := left) (s₂ := pr))
    omega
  have e2 : pr.card ≤ left.card + (pr \ left).card := by
    have := Finset.card_sdiff_add_card_inter pr left
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := pr) (s₂ := left))
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]; constructor
    · have : (pr.card : ℝ) ≤ left.card + (misSet r U T p).card := by exact_mod_cast (by omega : pr.card ≤ left.card + (misSet r U T p).card)
      linarith
    · have : (left.card : ℝ) ≤ pr.card + (misSet r U T p).card := by exact_mod_cast (by omega : left.card ≤ pr.card + (misSet r U T p).card)
      linarith
  · have hU : U = left ∪ {p} ∪ right := by
      ext x; constructor
      · intro hx
        simp only [Finset.mem_union, Finset.mem_singleton]
        rcases hcov x hx with h1 | h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inr h1
      · intro hx; simp only [Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with (h1 | rfl) | h1
        · exact (Finset.mem_filter.1 h1).1
        · exact hp
        · exact (Finset.mem_filter.1 h1).1
    rw [hU, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · simp; ring
    · exact Finset.disjoint_singleton_right.2 hpl
    · rw [Finset.disjoint_union_left]
      exact ⟨hlr, Finset.disjoint_singleton_left.2 hpr⟩
  · apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun h' => ?_⟩
    have := h' hp
    exact lt_irrefl _ (Finset.mem_filter.1 this).2

theorem argminIn_eq_iff (U : Finset (Fin n)) (σ : Rank n) (hU : U.Nonempty) (x : Fin n) :
    argminIn U σ hU = x ↔ x ∈ U ∧ ∀ y ∈ U, σ x ≤ σ y := by
  obtain ⟨-, h1, h2⟩ := argminIn_spec U σ hU
  constructor
  · rintro rfl; exact ⟨h1, h2⟩
  · rintro ⟨hx, hxy⟩
    exact σ.injective (le_antisymm (h2 x hx) (hxy _ h1))

/-- The arg-min pivot is uniform on its block. -/
theorem argmin_count (U : Finset (Fin n)) (hU : U.Nonempty) (x : Fin n) (hx : x ∈ U) :
    ((Finset.univ.filter fun σ : Rank n => argminIn U σ hU = x).card : ℝ) * U.card = (n.factorial : ℝ) := by
  classical
  have hsame : ∀ y ∈ U, (Finset.univ.filter fun σ : Rank n => argminIn U σ hU = x).card =
      (Finset.univ.filter fun σ : Rank n => argminIn U σ hU = y).card := by
    intro y hy
    apply Finset.card_bij (fun σ _ => (Equiv.swap x y).trans σ)
    · intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [argminIn_eq_iff] at hσ ⊢
      refine ⟨hy, fun z hz => ?_⟩
      simp only [Equiv.trans_apply, Equiv.swap_apply_right]
      refine hσ.2.2 _ ?_
      rw [Equiv.swap_apply_def]; split_ifs
      · exact hy
      · exact hx
      · exact hz
    · intro σ _ σ' _ h
      have := congrArg (fun τ => (Equiv.swap x y).trans τ) h
      simpa [← Equiv.trans_assoc] using this
    · intro τ hτ
      refine ⟨(Equiv.swap x y).trans τ, ?_, ?_⟩
      · rw [Finset.mem_filter] at hτ ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [argminIn_eq_iff] at hτ ⊢
        refine ⟨hx, fun z hz => ?_⟩
        simp only [Equiv.trans_apply, Equiv.swap_apply_left]
        refine hτ.2.2 _ ?_
        rw [Equiv.swap_apply_def]; split_ifs
        · exact hy
        · exact hx
        · exact hz
      · ext z; simp
  have htotal : ∑ y ∈ U, (Finset.univ.filter fun σ : Rank n => argminIn U σ hU = y).card = n.factorial := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun σ _ => (argminIn_spec U σ hU).2.1)]
    simp [Fintype.card_perm]
  have : ∑ y ∈ U, (Finset.univ.filter fun σ : Rank n => argminIn U σ hU = y).card =
      U.card * (Finset.univ.filter fun σ : Rank n => argminIn U σ hU = x).card := by
    rw [Finset.sum_congr rfl (fun y hy => (hsame y hy).symm)]; simp
  rw [this] at htotal
  rw [← htotal]; push_cast; ring

theorem argmin_avg (U : Finset (Fin n)) (hU : U.Nonempty) (G : Fin n → ℝ) :
    ∑ σ : Rank n, G (argminIn U σ hU) = (n.factorial : ℝ) / U.card * ∑ x ∈ U, G x := by
  classical
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.2 hU
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ => argminIn U σ hU) (t := U)
    (fun σ _ => (argminIn_spec U σ hU).2.1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_congr rfl (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  have := argmin_count U hU x hx
  field_simp
  rw [← this]; ring

theorem sum_dfix' (E : Finset (Pair n)) (U : Finset (Fin n)) :
    ∑ p ∈ U, ((E.filter fun e => (e.1.1 = p ∨ e.1.2 = p) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U).card : ℝ) =
      2 * (E.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card := by
  classical
  simp only [Finset.card_filter, Nat.cast_sum]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hin : e.1.1 ∈ U ∧ e.1.2 ∈ U
  · have : ∀ p ∈ U, ((if (e.1.1 = p ∨ e.1.2 = p) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U then 1 else 0 : ℕ) : ℝ) =
        (if p = e.1.1 then 1 else 0) + (if p = e.1.2 then 1 else 0) := by
      intro p _
      have hne : e.1.1 ≠ e.1.2 := e.2.ne
      by_cases h1 : p = e.1.1 <;> by_cases h2 : p = e.1.2
      · exact absurd (h1.symm.trans h2) hne
      · simp [h1, hin, hne]
      · simp [h2, hin, Ne.symm hne]
      · have : ¬ (e.1.1 = p ∨ e.1.2 = p) := by rintro (h | h) <;> [exact h1 h.symm; exact h2 h.symm]
        simp [this, h1, h2]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
      if_pos hin.1, if_pos hin.2, if_pos hin]
    norm_num
  · rw [if_neg hin]
    simp only [Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro p _
    simp [hin]

/-- Sum of squares. -/
theorem sum_range_sq (m : ℕ) : 6 * ∑ t ∈ Finset.range m, (t : ℝ) ^ 2 = (m - 1) * m * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

theorem sum_f_le (m : ℕ) (hm : 2 ≤ m) :
    ∑ t ∈ Finset.range m, ((t : ℝ) ^ 2 + ((m : ℝ) - 1 - t) ^ 2) + m ≤ 2 / 3 * (m : ℝ) ^ 3 := by
  have hrefl : ∑ t ∈ Finset.range m, ((m : ℝ) - 1 - t) ^ 2 = ∑ t ∈ Finset.range m, (t : ℝ) ^ 2 := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [Finset.sum_add_distrib, hrefl]
  have := sum_range_sq m
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem prank_sum (U : Finset (Fin n)) (r : Rank n) (F : ℕ → ℝ) :
    ∑ p ∈ U, F (U.filter fun x => r x < r p).card = ∑ t ∈ Finset.range U.card, F t := by
  classical
  set pr := fun p => (U.filter fun x => r x < r p).card
  have hinj : Set.InjOn pr U := by
    intro p hp q hq hpq
    by_contra hne
    have hne' : r p ≠ r q := fun h' => hne (r.injective h')
    rcases lt_or_gt_of_ne hne' with h | h
    · have : pr p < pr q := by
        apply Finset.card_lt_card
        refine ⟨fun x hx => ?_, fun h' => ?_⟩
        · rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 h⟩
        · have := h' (Finset.mem_filter.2 ⟨hp, h⟩)
          exact lt_irrefl _ (Finset.mem_filter.1 this).2
      exact absurd hpq (ne_of_lt this)
    · have : pr q < pr p := by
        apply Finset.card_lt_card
        refine ⟨fun x hx => ?_, fun h' => ?_⟩
        · rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 h⟩
        · have := h' (Finset.mem_filter.2 ⟨hq, h⟩)
          exact lt_irrefl _ (Finset.mem_filter.1 this).2
      exact absurd hpq.symm (ne_of_lt this)
  rw [← Finset.sum_image hinj]
  congr 1
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.mem_range]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun h' => ?_⟩
    have := h' hp
    exact lt_irrefl _ (Finset.mem_filter.1 this).2
  · rw [Finset.card_range, Finset.card_image_of_injOn hinj]

end RQCPivot



noncomputable section

namespace RQCPivot
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def Gam (L : ℕ) (W : ComparisonWorld n) (h : ℕ) (P : PivotState n) : ℝ :=
  (phiSet W.rank P).card + psi L P / 2 + theta L W P + 2 * n * ((h : ℝ) - P.interaction.online.card)

theorem wt_le_one (L d : ℕ) (hd : d ≤ L) : wt L d ≤ 1 := by
  unfold wt
  rw [div_le_one (by positivity)]
  exact pow_le_pow_right₀ (by norm_num) hd

theorem wt_succ (L d : ℕ) : wt L (d + 1) = 3 / 2 * wt L d := by
  unfold wt; rw [pow_succ]; ring

/-- The per-pivot excess. -/
def excess (L : ℕ) (W : ComparisonWorld n) (U : Finset (Fin n)) (d : ℕ) (p : Fin n) : ℝ :=
  ((U.card : ℝ) - 1) * (1 + wt L (d + 1)) *
      (W.initial.filter fun e => (e.1.1 = p ∨ e.1.2 = p) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U).card -
    (2 + 2 * wt L (d + 1)) * (W.initial.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card +
    (1 / 2) * (wt L (d + 1) * ((((U.filter fun x => W.rank x < W.rank p).card : ℕ) : ℝ) ^ 2 +
      ((U.card : ℝ) - 1 - ((U.filter fun x => W.rank x < W.rank p).card : ℕ)) ^ 2 + 1) -
      wt L d * (U.card : ℝ) ^ 2)

theorem step_path (W : ComparisonWorld n) (h L : ℕ) (P : PivotState n) (hP : Good L h P) (k : ℕ)
    (hk : k < P.slots.length) (hd : (P.slots[k]).2 < L) (p : Fin n) (hp : p ∈ (P.slots[k]).1) :
    Gam L W h (splitAt W h P k p) ≤ Gam L W h P + excess L W (P.slots[k]).1 (P.slots[k]).2 p := by
  set U := (P.slots[k]).1
  set d := (P.slots[k]).2
  set S := foldRead W h (starOf U p) P.interaction
  set T := S.ledger
  set r := W.rank
  have hslotk : P.slots[k] ∈ P.slots := List.getElem_mem hk
  have hfreshU : ∀ e ∈ starOf U p, P.interaction.ledger e = none := by
    intro e he; rw [mem_starOf] at he; exact hP.fresh _ hslotk e he.2.1 he.2.2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := foldRead_spec W h (starOf U p) P.interaction (starOf_nodup U p)
    hfreshU hP.ok
  have hphi := phi_step W h L P hP k hk p hp r
  have hpsi := psi_split W h L P k hk p
  have htheta := theta_split W h L P hP k hk hd p hp
  have hmis := mis_bound W h L P hP k hk p hp
  obtain ⟨hdev, hsize, hprlt⟩ := left_dev U p hp T r f3
  set Mis := (misSet r U T p).card
  set l := (U.filter fun i => RecordedForward T i p).card
  set rr := (U.filter fun i => RecordedForward T p i).card
  set pr := (U.filter fun x => r x < r p).card
  set m := U.card
  set I := (W.initial.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card
  set Df := (W.initial.filter fun e => (e.1.1 = p ∨ e.1.2 = p) ∧ e.1.1 ∈ U ∧ e.1.2 ∈ U).card
  have hon : P.interaction.online.card ≤ S.online.card := Finset.card_le_card f4
  have hS : (splitAt W h P k p).interaction = S := by
    rw [splitAt_eq]; simp only [List.getElem?_eq_getElem hk]; rfl
  have hw1 : wt L (d + 1) ≤ 1 := wt_le_one L (d + 1) hd
  have hw0 : 0 ≤ wt L (d + 1) := by unfold wt; positivity
  have hmn : m ≤ n := by
    have := Finset.card_le_univ U; simpa using this
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Finset.card_pos.2 ⟨p, hp⟩
  -- the quadratic bound on child masses
  have hsizeR : (l : ℝ) + rr + 1 = m := by exact_mod_cast hsize
  have hprR : (pr : ℝ) + 1 ≤ m := by exact_mod_cast hprlt
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hpr0 : (0 : ℝ) ≤ pr := Nat.cast_nonneg _
  have hquad : (l : ℝ) ^ 2 + (rr : ℝ) ^ 2 ≤ (pr : ℝ) ^ 2 + ((m : ℝ) - 1 - pr) ^ 2 + 2 * ((m : ℝ) - 1) * Mis := by
    have hr : (rr : ℝ) = m - 1 - l := by linarith
    rw [hr]
    have h1 : (l : ℝ) ^ 2 + ((m : ℝ) - 1 - l) ^ 2 - ((pr : ℝ) ^ 2 + ((m : ℝ) - 1 - pr) ^ 2) =
        ((l : ℝ) - pr) * (2 * l + 2 * pr - 2 * ((m : ℝ) - 1)) := by ring
    have h2 : |2 * (l : ℝ) + 2 * pr - 2 * ((m : ℝ) - 1)| ≤ 2 * ((m : ℝ) - 1) := by
      rw [abs_le]; constructor <;> linarith
    have h3 : ((l : ℝ) - pr) * (2 * l + 2 * pr - 2 * ((m : ℝ) - 1)) ≤
        |(l : ℝ) - pr| * (2 * ((m : ℝ) - 1)) := by
      calc ((l : ℝ) - pr) * (2 * l + 2 * pr - 2 * ((m : ℝ) - 1))
          ≤ |((l : ℝ) - pr) * (2 * l + 2 * pr - 2 * ((m : ℝ) - 1))| := le_abs_self _
        _ = |(l : ℝ) - pr| * |2 * (l : ℝ) + 2 * pr - 2 * ((m : ℝ) - 1)| := abs_mul _ _
        _ ≤ |(l : ℝ) - pr| * (2 * ((m : ℝ) - 1)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have h4 : |(l : ℝ) - pr| * (2 * ((m : ℝ) - 1)) ≤ Mis * (2 * ((m : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right hdev (by linarith)
    linarith
  unfold Gam excess
  rw [hS]
  have hMis0 : (0 : ℝ) ≤ Mis := Nat.cast_nonneg _
  have hdon : (0 : ℝ) ≤ (S.online.card : ℝ) - P.interaction.online.card := by
    have : (P.interaction.online.card : ℝ) ≤ S.online.card := by exact_mod_cast hon
    linarith
  -- combine
  have hcoef : ((m : ℝ) - 1) * (1 + wt L (d + 1)) ≤ 2 * n := by nlinarith
  have hA : ((m : ℝ) - 1) * Mis + (1 / 2) * (wt L (d + 1) * (2 * ((m : ℝ) - 1) * Mis)) ≤
      ((m : ℝ) - 1) * (1 + wt L (d + 1)) * Df +
        2 * n * ((S.online.card : ℝ) - P.interaction.online.card) := by
    have : ((m : ℝ) - 1) * Mis + (1 / 2) * (wt L (d + 1) * (2 * ((m : ℝ) - 1) * Mis)) =
        ((m : ℝ) - 1) * (1 + wt L (d + 1)) * Mis := by ring
    rw [this]
    have hm0 : (0 : ℝ) ≤ ((m : ℝ) - 1) * (1 + wt L (d + 1)) := by nlinarith
    calc ((m : ℝ) - 1) * (1 + wt L (d + 1)) * Mis
        ≤ ((m : ℝ) - 1) * (1 + wt L (d + 1)) *
            (Df + ((S.online.card : ℝ) - P.interaction.online.card)) :=
          mul_le_mul_of_nonneg_left hmis hm0
      _ ≤ _ := by nlinarith
  have hpsi' : psi L (splitAt W h P k p) ≤ psi L P - wt L d * (m : ℝ) ^ 2 +
      wt L (d + 1) * ((pr : ℝ) ^ 2 + ((m : ℝ) - 1 - pr) ^ 2 + 2 * ((m : ℝ) - 1) * Mis + 1) := by
    rw [hpsi]
    have := mul_le_mul_of_nonneg_left hquad hw0
    linarith
  linarith

theorem excess_sum (L : ℕ) (W : ComparisonWorld n) (U : Finset (Fin n)) (d : ℕ) (hm : 2 ≤ U.card) :
    ∑ p ∈ U, excess L W U d p ≤ 0 := by
  unfold excess
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_dfix', Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum]
  have hpr := prank_sum U W.rank (fun t => wt L (d + 1) * ((t : ℝ) ^ 2 + ((U.card : ℝ) - 1 - t) ^ 2 + 1) -
    wt L d * (U.card : ℝ) ^ 2)
  rw [hpr]
  have hf := sum_f_le U.card hm
  have hw := wt_succ L d
  have hw0 : 0 ≤ wt L d := by unfold wt; positivity
  set m := U.card
  set I := ((W.initial.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card : ℝ)
  have hI : 0 ≤ I := Nat.cast_nonneg _
  have hsum : ∑ t ∈ Finset.range m, (wt L (d + 1) * ((t : ℝ) ^ 2 + ((m : ℝ) - 1 - t) ^ 2 + 1) -
      wt L d * (m : ℝ) ^ 2) = wt L (d + 1) * (∑ t ∈ Finset.range m, ((t : ℝ) ^ 2 + ((m : ℝ) - 1 - t) ^ 2) + m)
        - m * (wt L d * (m : ℝ) ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const]
    simp
  rw [hsum]
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : wt L (d + 1) * (∑ t ∈ Finset.range m, ((t : ℝ) ^ 2 + ((m : ℝ) - 1 - t) ^ 2) + m) ≤
      wt L (d + 1) * (2 / 3 * (m : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hf (by unfold wt; positivity)
  rw [hw] at h1 ⊢
  nlinarith

theorem step_avg (W : ComparisonWorld n) (h L : ℕ) (P : PivotState n) (hP : Good L h P) (k : ℕ)
    (hk : k < P.slots.length) (hm : 1 < (P.slots[k]).1.card) (hd : (P.slots[k]).2 < L)
    (hU : (P.slots[k]).1.Nonempty) :
    ∑ σ : Rank n, Gam L W h (splitAt W h P k (argminIn (P.slots[k]).1 σ hU)) ≤
      (n.factorial : ℝ) * Gam L W h P := by
  have h1 : ∀ σ : Rank n, Gam L W h (splitAt W h P k (argminIn (P.slots[k]).1 σ hU)) ≤
      Gam L W h P + excess L W (P.slots[k]).1 (P.slots[k]).2 (argminIn (P.slots[k]).1 σ hU) :=
    fun σ => step_path W h L P hP k hk hd _ (argminIn_spec _ σ hU).2.1
  calc ∑ σ : Rank n, Gam L W h (splitAt W h P k (argminIn (P.slots[k]).1 σ hU))
      ≤ ∑ σ : Rank n, (Gam L W h P + excess L W (P.slots[k]).1 (P.slots[k]).2 (argminIn (P.slots[k]).1 σ hU)) :=
        Finset.sum_le_sum fun σ _ => h1 σ
    _ = (n.factorial : ℝ) * Gam L W h P +
          (n.factorial : ℝ) / (P.slots[k]).1.card * ∑ p ∈ (P.slots[k]).1, excess L W (P.slots[k]).1 (P.slots[k]).2 p := by
        rw [Finset.sum_add_distrib, argmin_avg]
        simp [Fintype.card_perm]
    _ ≤ (n.factorial : ℝ) * Gam L W h P := by
        have := excess_sum L W (P.slots[k]).1 (P.slots[k]).2 (by omega)
        have hpos : (0 : ℝ) ≤ (n.factorial : ℝ) / (P.slots[k]).1.card := by positivity
        nlinarith

end RQCPivot



noncomputable section

namespace RQCPivot
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem update_sum {R : Type} [Fintype R] [DecidableEq R] (j : Fin n) (F : (Fin n → R) → ℝ) :
    ∑ s : Fin n → R, ∑ x : R, F (Function.update s j x) = (Fintype.card R : ℝ) * ∑ s, F s := by
  classical
  set e := Equiv.piSplitAt j (fun _ : Fin n => R)
  have hupd : ∀ (y x : R) (t : {i // i ≠ j} → R), Function.update (e.symm (y, t)) j x = e.symm (x, t) := by
    intro y x t
    funext i
    by_cases hi : i = j
    · subst hi; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, Equiv.piSplitAt_symm_apply, hi, Function.update_of_ne hi]
  rw [← Fintype.sum_equiv e.symm (fun p => ∑ x, F (Function.update (e.symm p) j x)) _ (fun _ => rfl)]
  rw [← Fintype.sum_equiv e.symm (fun p => F (e.symm p)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [hupd]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

/-- Averaging one coordinate. -/
theorem coord_avg {R : Type} [Fintype R] [DecidableEq R] [Nonempty R] (j : Fin n)
    (G : (Fin n → R) → R → ℝ) (hG : ∀ s x y, G (Function.update s j x) y = G s y) :
    ∑ s : Fin n → R, G s (s j) = (1 / (Fintype.card R : ℝ)) * ∑ s : Fin n → R, ∑ y : R, G s y := by
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have := update_sum j (fun s => G s (s j))
  simp only [Function.update_self, hG] at this
  rw [this]; field_simp

/-- The run after `j` steps. -/
def Pseq (L : ℕ) (W : ComparisonWorld n) (h : ℕ) (seed : PivotSeed n) (j : ℕ) : PivotState n :=
  (List.range j).foldl (fun P i => pivotStep 1 L (fun _ _ => 0) true W h seed i P) (pivotStart (initialState n))

theorem Pseq_zero (L : ℕ) (W : ComparisonWorld n) (h : ℕ) (seed : PivotSeed n) :
    Pseq L W h seed 0 = pivotStart (initialState n) := rfl

theorem Pseq_succ (L : ℕ) (W : ComparisonWorld n) (h : ℕ) (seed : PivotSeed n) (j : ℕ) :
    Pseq L W h seed (j + 1) = pivotStep 1 L (fun _ _ => 0) true W h seed j (Pseq L W h seed j) := by
  unfold Pseq; rw [List.range_succ, List.foldl_append]; rfl

theorem pivotExecution_eq (L : ℕ) (W : ComparisonWorld n) (h : ℕ) (seed : PivotSeed n) :
    pivotExecution 1 L (fun _ _ => 0) true W h (initialState n) seed = Pseq L W h seed n := rfl

theorem pivotStep_seed (L : ℕ) (W : ComparisonWorld n) (h : ℕ) (seed seed' : PivotSeed n) (j : ℕ)
    (hj : ∀ hj : j < n, seed ⟨j, hj⟩ = seed' ⟨j, hj⟩) (P : PivotState n) :
    pivotStep 1 L (fun _ _ => 0) true W h seed j P = pivotStep 1 L (fun _ _ => 0) true W h seed' j P := by
  rw [pivotStep_eq, pivotStep_eq]
  by_cases hjn : j < n
  · simp only [dif_pos hjn, hj hjn]
  · simp only [dif_neg hjn]

theorem Pseq_update (L : ℕ) (W : ComparisonWorld n) (h : ℕ) (seed : PivotSeed n) (i : Fin n) (x : Rank n) :
    ∀ j, j ≤ i.val → Pseq L W h (Function.update seed i x) j = Pseq L W h seed j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [Pseq_succ, Pseq_succ, ih (by omega)]
    apply pivotStep_seed
    intro hjn
    rw [Function.update_of_ne]
    intro h'
    have := congrArg Fin.val h'
    simp at this; omega

theorem good_Pseq (L h : ℕ) (W : ComparisonWorld n) (seed : PivotSeed n) (hn : 0 < n) :
    ∀ j, Good L h (Pseq L W h seed j) := by
  intro j
  induction j with
  | zero => exact good_start L h hn
  | succ j ih =>
    rw [Pseq_succ, pivotStep_eq]
    rcases hsel : selIndex L (Pseq L W h seed j) with _ | k
    · exact ih
    · obtain ⟨hk, hm, hd⟩ := selIndex_some L _ k hsel
      have hUd : ((Pseq L W h seed j).slots[k]?).getD (∅, 0) = (Pseq L W h seed j).slots[k] := by
        rw [List.getElem?_eq_getElem hk]; rfl
      simp only [hUd]
      have hU : ((Pseq L W h seed j).slots[k]).1.Nonempty := Finset.card_pos.1 (by omega)
      set σ := if hj : j < n then seed ⟨j, hj⟩ else Equiv.refl (Fin n)
      rw [(argminIn_spec _ σ hU).1]
      exact good_split L h W _ ih k hk hd _ (argminIn_spec _ σ hU).2.1

/-- One step does not increase the averaged potential. -/
theorem step_seed_avg (L h : ℕ) (W : ComparisonWorld n) (P : PivotState n) (hP : Good L h P) (j : ℕ)
    (hj : j < n) :
    ∑ σ : Rank n, Gam L W h (pivotStep 1 L (fun _ _ => 0) true W h (fun _ => σ) j P) ≤
      (n.factorial : ℝ) * Gam L W h P := by
  have hcard : (Finset.univ : Finset (Rank n)).card = n.factorial := by simp [Fintype.card_perm]
  simp only [pivotStep_eq, dif_pos hj]
  rcases hsel : selIndex L P with _ | k
  · simp [hcard]
  · obtain ⟨hk, hm, hd⟩ := selIndex_some L _ k hsel
    have hUd : (P.slots[k]?).getD (∅, 0) = P.slots[k] := by rw [List.getElem?_eq_getElem hk]; rfl
    simp only [hUd]
    have hU : (P.slots[k]).1.Nonempty := Finset.card_pos.1 (by omega)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun σ _ => ?_)) (step_avg W h L P hP k hk hm hd hU)
    congr 1
    have e := (argminIn_spec _ σ hU).1
    split
    · rename_i heq
      exfalso
      have : ((P.slots[k]).1.toList.mergeSort fun i j => decide (σ i ≤ σ j)).head? =
          some (argminIn (P.slots[k]).1 σ hU) := by convert e
      rw [heq] at this; cases this
    · rename_i p heq
      have : ((P.slots[k]).1.toList.mergeSort fun i j => decide (σ i ≤ σ j)).head? =
          some (argminIn (P.slots[k]).1 σ hU) := by convert e
      rw [heq] at this
      cases this; rfl

theorem expected_Gam (L h : ℕ) (W : ComparisonWorld n) (hn : 0 < n) :
    ∀ j, j ≤ n → ∑ seed : PivotSeed n, Gam L W h (Pseq L W h seed j) ≤
      (Fintype.card (PivotSeed n) : ℝ) * Gam L W h (pivotStart (initialState n)) := by
  intro j
  induction j with
  | zero => intro _; simp [Pseq_zero]
  | succ j ih =>
    intro hj
    have hjn : j < n := by omega
    refine le_trans ?_ (ih (by omega))
    set jj : Fin n := ⟨j, hjn⟩
    -- rewrite each summand through the j-th coordinate
    have hG : ∀ seed : PivotSeed n, Gam L W h (Pseq L W h seed (j + 1)) =
        Gam L W h (pivotStep 1 L (fun _ _ => 0) true W h (fun _ => seed jj) j (Pseq L W h seed j)) := by
      intro seed
      rw [Pseq_succ]
      congr 1
    simp only [hG]
    rw [coord_avg jj (fun s σ => Gam L W h (pivotStep 1 L (fun _ _ => 0) true W h (fun _ => σ) j
      (Pseq L W h s j))) (by intro s x y; rw [Pseq_update L W h s jj x j (le_refl _)])]
    have hcard : (Fintype.card (Rank n) : ℝ) = n.factorial := by simp [Fintype.card_perm]
    rw [hcard]
    have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro seed _
    have := step_seed_avg L h W (Pseq L W h seed j) (good_Pseq L h W seed hn j) j hjn
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hfpos]
    linarith

end RQCPivot



noncomputable section

namespace RQCPivot
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem flat_nodup (L h : ℕ) (P : PivotState n) (hP : Good L h P) : (flat P).Nodup := by
  unfold flat
  rw [List.nodup_flatMap]
  refine ⟨fun Ud _ => Finset.sort_nodup _ _, ?_⟩
  have := hP.disj
  rw [List.pairwise_map] at this
  apply List.Pairwise.imp _ this
  intro a b hab
  rw [Function.onFun, List.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_sort] at hx hx'
  exact Finset.disjoint_left.1 hab hx hx'

theorem slots_length_le (L h : ℕ) (P : PivotState n) (hP : Good L h P) : P.slots.length ≤ n := by
  have h1 : P.slots.length ≤ (flat P).length := by
    unfold flat
    rw [List.length_flatMap]
    have : ∀ Ud ∈ P.slots, 1 ≤ (Ud.1.sort (· ≤ ·)).length := by
      intro Ud hUd; rw [Finset.length_sort]; exact Finset.card_pos.2 (hP.ne Ud hUd)
    calc P.slots.length = (P.slots.map fun _ => 1).sum := by simp
      _ ≤ (P.slots.map fun Ud => (Ud.1.sort (· ≤ ·)).length).sum := List.sum_le_sum this
  have h2 := (flat_nodup L h P hP).length_le_card
  simp at h2
  omega

theorem split_length (W : ComparisonWorld n) (h L : ℕ) (P : PivotState n) (hP : Good L h P) (k : ℕ)
    (hk : k < P.slots.length) (hm : 1 < (P.slots[k]).1.card) (p : Fin n) (hp : p ∈ (P.slots[k]).1) :
    P.slots.length + 1 ≤ (splitAt W h P k p).slots.length := by
  set U := (P.slots[k]).1
  set S := foldRead W h (starOf U p) P.interaction
  have hslotk : P.slots[k] ∈ P.slots := List.getElem_mem hk
  have hfreshU : ∀ e ∈ starOf U p, P.interaction.ledger e = none := by
    intro e he; rw [mem_starOf] at he; exact hP.fresh _ hslotk e he.2.1 he.2.2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := foldRead_spec W h (starOf U p) P.interaction (starOf_nodup U p)
    hfreshU hP.ok
  obtain ⟨-, hsize, -⟩ := left_dev U p hp S.ledger W.rank f3
  have hslots' : (splitAt W h P k p).slots = P.slots.take k ++ childrenOf
      (U.filter fun i => RecordedForward S.ledger i p) (U.filter fun i => RecordedForward S.ledger p i)
      p (P.slots[k]).2 ++ P.slots.drop (k + 1) := by
    rw [splitAt_eq]
    have hUd : (P.slots[k]?).getD (∅, 0) = (U, (P.slots[k]).2) := by rw [List.getElem?_eq_getElem hk]; rfl
    simp only [hUd]
    rfl
  rw [hslots']
  simp only [List.length_append, List.length_take, List.length_drop]
  have hch : 2 ≤ (childrenOf (U.filter fun i => RecordedForward S.ledger i p)
      (U.filter fun i => RecordedForward S.ledger p i) p (P.slots[k]).2).length := by
    unfold childrenOf
    by_cases hl : (U.filter fun i => RecordedForward S.ledger i p).Nonempty <;>
      by_cases hr : (U.filter fun i => RecordedForward S.ledger p i).Nonempty
    · simp [List.filter_cons, hl, hr]
    · simp [List.filter_cons, hl, hr]
    · simp [List.filter_cons, hl, hr]
    · exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hl hr
      rw [hl, hr] at hsize; simp at hsize; omega
  omega

theorem live_length (L h : ℕ) (W : ComparisonWorld n) (seed : PivotSeed n) (hn : 0 < n) :
    ∀ j, selIndex L (Pseq L W h seed j) ≠ none → j + 1 ≤ (Pseq L W h seed j).slots.length := by
  intro j
  induction j with
  | zero => intro _; simp [Pseq_zero, pivotStart]
  | succ j ih =>
    intro hlive
    have hP := good_Pseq L h W seed hn j
    rcases hsel : selIndex L (Pseq L W h seed j) with _ | k
    · exfalso
      apply hlive
      rw [Pseq_succ, pivotStep_eq, hsel]; exact hsel
    · have ih' := ih (by rw [hsel]; simp)
      obtain ⟨hk, hm, hd⟩ := selIndex_some L _ k hsel
      have hU : ((Pseq L W h seed j).slots[k]).1.Nonempty := Finset.card_pos.1 (by omega)
      set σ := if hj : j < n then seed ⟨j, hj⟩ else Equiv.refl (Fin n)
      have hstep : Pseq L W h seed (j + 1) = splitAt W h (Pseq L W h seed j) k
          (argminIn ((Pseq L W h seed j).slots[k]).1 σ hU) := by
        rw [Pseq_succ, pivotStep_eq, hsel]
        have hUd : ((Pseq L W h seed j).slots[k]?).getD (∅, 0) = (Pseq L W h seed j).slots[k] := by
          rw [List.getElem?_eq_getElem hk]; rfl
        simp only [hUd]
        have e := (argminIn_spec _ σ hU).1
        split
        · rename_i heq
          exfalso
          have : (((Pseq L W h seed j).slots[k]).1.toList.mergeSort fun i j => decide (σ i ≤ σ j)).head? =
              some (argminIn ((Pseq L W h seed j).slots[k]).1 σ hU) := by convert e
          rw [heq] at this; cases this
        · rename_i p heq
          have : (((Pseq L W h seed j).slots[k]).1.toList.mergeSort fun i j => decide (σ i ≤ σ j)).head? =
              some (argminIn ((Pseq L W h seed j).slots[k]).1 σ hU) := by convert e
          rw [heq] at this
          cases this; rfl
      rw [hstep]
      have := split_length W h L _ hP k hk hm _ (argminIn_spec _ σ hU).2.1
      omega

theorem end_dead (L h : ℕ) (W : ComparisonWorld n) (seed : PivotSeed n) (hn : 0 < n) :
    selIndex L (Pseq L W h seed n) = none := by
  by_contra hc
  have h1 := live_length L h W seed hn n hc
  have h2 := slots_length_le L h _ (good_Pseq L h W seed hn n)
  omega

theorem pairs_in_le (U : Finset (Fin n)) :
    2 * (Finset.univ.filter fun e : Pair n => e.1.1 ∈ U ∧ e.1.2 ∈ U).card ≤ U.card ^ 2 := by
  classical
  set A := Finset.univ.filter fun e : Pair n => e.1.1 ∈ U ∧ e.1.2 ∈ U
  have h1 : (A.image fun e => (e.1.1, e.1.2)).card = A.card :=
    Finset.card_image_of_injective _ (fun e f h => Subtype.ext (by simpa using h))
  have h2 : (A.image fun e => (e.1.2, e.1.1)).card = A.card :=
    Finset.card_image_of_injective _ (fun e f h => by
      simp only [Prod.mk.injEq] at h; exact Subtype.ext (Prod.ext h.2 h.1))
  have hdisj : Disjoint (A.image fun e => (e.1.1, e.1.2)) (A.image fun e => (e.1.2, e.1.1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨f, -, hf⟩ := Finset.mem_image.1 hx'
    simp only [Prod.mk.injEq] at hf
    have he := e.2; have hf2 := f.2
    rw [← hf.1, ← hf.2] at he
    exact lt_asymm he hf2
  have hsub : (A.image fun e => (e.1.1, e.1.2)) ∪ (A.image fun e => (e.1.2, e.1.1)) ⊆ U ×ˢ U := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx <;> obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx <;>
      have := (Finset.mem_filter.1 he).2 <;> simp [this.1, this.2]
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, h1, h2, Finset.card_product] at this
  rw [sq]; omega

theorem sameSlot_count (l : PivotSlots n) :
    ((Finset.univ.filter fun e : Pair n => ∃ Ud ∈ l, e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1).card : ℝ) ≤
      (l.map fun Ud => ((Finset.univ.filter fun e : Pair n => e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1).card : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons Ud l ih =>
    have hsub : (Finset.univ.filter fun e : Pair n => ∃ V ∈ Ud :: l, e.1.1 ∈ V.1 ∧ e.1.2 ∈ V.1) ⊆
        (Finset.univ.filter fun e : Pair n => e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1) ∪
        (Finset.univ.filter fun e : Pair n => ∃ V ∈ l, e.1.1 ∈ V.1 ∧ e.1.2 ∈ V.1) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at he
      obtain ⟨V, hV, h1, h2⟩ := he
      rcases hV with rfl | hV
      · exact Finset.mem_union_left _ (by simp [h1, h2])
      · exact Finset.mem_union_right _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨V, hV, h1, h2⟩)
    have := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    simp only [List.map_cons, List.sum_cons]
    have : ((Finset.univ.filter fun e : Pair n => ∃ V ∈ Ud :: l, e.1.1 ∈ V.1 ∧ e.1.2 ∈ V.1).card : ℝ) ≤
        (Finset.univ.filter fun e : Pair n => e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1).card +
        (Finset.univ.filter fun e : Pair n => ∃ V ∈ l, e.1.1 ∈ V.1 ∧ e.1.2 ∈ V.1).card := by
      exact_mod_cast this
    linarith

theorem kendall_le (L h : ℕ) (P : PivotState n) (hP : Good L h P) (hdead : selIndex L P = none)
    (r : Rank n) : (kendallCount r (pivotOutput P) : ℝ) ≤ (phiSet r P).card + psi L P / 2 := by
  classical
  set SS := Finset.univ.filter fun e : Pair n => ∃ Ud ∈ P.slots, e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1
  have hcover : ∀ x, x ∈ flat P := by
    intro x
    obtain ⟨Ud, hUd, hx⟩ := hP.cover x
    unfold flat; rw [List.mem_flatMap]; exact ⟨Ud, hUd, by simpa using hx⟩
  have hnd := flat_nodup L h P hP
  have hsub : (Finset.univ.filter fun e : Pair n => (r e.1.1 < r e.1.2 ∧ pivotOutput P e.1.2 < pivotOutput P e.1.1) ∨
      (r e.1.2 < r e.1.1 ∧ pivotOutput P e.1.1 < pivotOutput P e.1.2)) ⊆ phiSet r P ∪ SS := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pivotOutput_eq, Nat.cast_lt] at he
    by_cases hs : sameSlot P e.1.1 e.1.2
    · exact Finset.mem_union_right _ (by simp only [SS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hs)
    · apply Finset.mem_union_left
      simp only [phiSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hs, ?_⟩
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · intro hiff; have := hiff.2 h1; omega
      · intro hiff; exact lt_asymm h1 (hiff.1 h2)
  have h1 : (kendallCount r (pivotOutput P) : ℝ) ≤ (phiSet r P).card + SS.card := by
    unfold kendallCount
    have := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    exact_mod_cast this
  have h2 := sameSlot_count P.slots
  have h3 : (P.slots.map fun Ud => ((Finset.univ.filter fun e : Pair n => e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1).card : ℝ)).sum ≤
      psi L P / 2 := by
    unfold psi
    rw [div_eq_mul_inv, ← List.sum_map_mul_right]
    apply List.sum_le_sum
    intro Ud hUd
    have hp2 := pairs_in_le Ud.1
    by_cases hbig : 1 < Ud.1.card
    · have hdL : Ud.2 = L := by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hUd
        have := selIndex_none L P hdead k hk
        have := hP.depth _ hUd
        omega
      rw [hdL]
      have hw : wt L L = 1 := by unfold wt; field_simp
      rw [hw, one_mul]
      have : (2 * (Finset.univ.filter fun e : Pair n => e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1).card : ℝ) ≤
          (Ud.1.card : ℝ) ^ 2 := by exact_mod_cast hp2
      linarith
    · have hzero : (Finset.univ.filter fun e : Pair n => e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro e - ⟨h1, h2⟩
        have : 1 < Ud.1.card := Finset.one_lt_card.2 ⟨_, h1, _, h2, e.2.ne⟩
        exact hbig this
      rw [hzero]
      have : 0 ≤ wt L Ud.2 := by unfold wt; positivity
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have : (SS.card : ℝ) ≤ psi L P / 2 := le_trans h2 h3
  linarith

end RQCPivot



noncomputable section

namespace RQCPivot
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem star_length (U : Finset (Fin n)) (p : Fin n) (hp : p ∈ U) : (starOf U p).length = U.card - 1 := by
  rw [← List.toFinset_card_of_nodup (starOf_nodup U p), ← Finset.card_erase_of_mem hp]
  apply Finset.card_bij (fun e _ => if e.1.1 = p then e.1.2 else e.1.1)
  · intro e he
    rw [List.mem_toFinset, mem_starOf] at he
    have hne : e.1.1 ≠ e.1.2 := e.2.ne
    rw [Finset.mem_erase]
    split_ifs with h1
    · exact ⟨fun h2 => hne (h1.trans h2.symm), he.2.2⟩
    · rcases he.1 with h3 | h3
      · exact absurd h3 h1
      · exact ⟨fun h2 => hne (h2.trans h3.symm), he.2.1⟩
  · intro e he f hf hef
    rw [List.mem_toFinset, mem_starOf] at he hf
    have h1 : e.1.1.val < e.1.2.val := e.2
    have h2 : f.1.1.val < f.1.2.val := f.2
    apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;>
      (split_ifs at hef with ha hb hb <;> simp only [Fin.ext_iff] at ha hb hef he hf <;> omega)
  · intro x hx
    rw [Finset.mem_erase] at hx
    refine ⟨pairOf x p hx.1, ?_, ?_⟩
    · rw [List.mem_toFinset, mem_starOf]
      rcases pairOf_mem x p hx.1 with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact ⟨Or.inr a2, by rw [a1]; exact hx.2, by rw [a2]; exact hp⟩
      · exact ⟨Or.inl a1, by rw [a1]; exact hp, by rw [a2]; exact hx.2⟩
    · rcases pairOf_mem x p hx.1 with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · rw [if_neg (by rw [a1]; exact hx.1), a1]
      · rw [if_pos a1, a2]

def Rpot (L : ℕ) (P : PivotState n) : ℕ :=
  P.requests.length + (P.slots.map fun Ud => (Ud.1.card - 1) * (L - Ud.2)).sum

theorem Rpot_split (W : ComparisonWorld n) (h L : ℕ) (P : PivotState n) (hP : Good L h P) (k : ℕ)
    (hk : k < P.slots.length) (hm : 1 < (P.slots[k]).1.card) (hd : (P.slots[k]).2 < L) (p : Fin n)
    (hp : p ∈ (P.slots[k]).1) : Rpot L (splitAt W h P k p) ≤ Rpot L P := by
  set U := (P.slots[k]).1
  set d := (P.slots[k]).2
  set S := foldRead W h (starOf U p) P.interaction
  have hslotk : P.slots[k] ∈ P.slots := List.getElem_mem hk
  have hfreshU : ∀ e ∈ starOf U p, P.interaction.ledger e = none := by
    intro e he; rw [mem_starOf] at he; exact hP.fresh _ hslotk e he.2.1 he.2.2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := foldRead_spec W h (starOf U p) P.interaction (starOf_nodup U p)
    hfreshU hP.ok
  obtain ⟨-, hsize, -⟩ := left_dev U p hp S.ledger W.rank f3
  set l := (U.filter fun i => RecordedForward S.ledger i p).card
  set rr := (U.filter fun i => RecordedForward S.ledger p i).card
  have hreq : (splitAt W h P k p).requests = P.requests ++ starOf U p := by
    rw [splitAt_eq]; simp only [List.getElem?_eq_getElem hk]; rfl
  have hslots' : (splitAt W h P k p).slots = P.slots.take k ++ childrenOf
      (U.filter fun i => RecordedForward S.ledger i p) (U.filter fun i => RecordedForward S.ledger p i)
      p d ++ P.slots.drop (k + 1) := by
    rw [splitAt_eq]
    have hUd : (P.slots[k]?).getD (∅, 0) = (U, d) := by rw [List.getElem?_eq_getElem hk]; rfl
    simp only [hUd]
    rfl
  have hdecomp := slots_decomp P.slots k hk
  have hch : ((childrenOf (U.filter fun i => RecordedForward S.ledger i p)
      (U.filter fun i => RecordedForward S.ledger p i) p d).map fun Ud => (Ud.1.card - 1) * (L - Ud.2)).sum ≤
      ((l - 1) + (rr - 1)) * (L - (d + 1)) := by
    unfold childrenOf
    by_cases hl : (U.filter fun i => RecordedForward S.ledger i p).Nonempty <;>
      by_cases hr : (U.filter fun i => RecordedForward S.ledger p i).Nonempty <;>
      simp [List.filter_cons, hl, hr, l, rr] <;> ring_nf <;> omega
  unfold Rpot
  rw [hreq, hslots']
  conv_rhs => rw [hdecomp]
  simp only [List.length_append, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  rw [star_length U p hp]
  rw [show (P.slots[k]).1.card = U.card from rfl, show (P.slots[k]).2 = d from rfl]
  have hm' : l + rr + 1 = U.card := hsize
  have hkey : U.card - 1 + ((l - 1) + (rr - 1)) * (L - (d + 1)) ≤ (U.card - 1) * (L - d) := by
    have h1 : (l - 1) + (rr - 1) ≤ U.card - 2 := by omega
    have h2 : ((l - 1) + (rr - 1)) * (L - (d + 1)) ≤ (U.card - 2) * (L - (d + 1)) :=
      Nat.mul_le_mul_right _ h1
    have h3 : U.card - 1 + (U.card - 2) * (L - (d + 1)) ≤ (U.card - 1) * (L - d) := by
      obtain ⟨m', hm'⟩ : ∃ m', U.card = m' + 2 := ⟨U.card - 2, by omega⟩
      obtain ⟨t, ht⟩ : ∃ t, L - d = t + 1 := ⟨L - d - 1, by omega⟩
      have : L - (d + 1) = t := by omega
      rw [hm', ht, this]
      have e1 : m' + 2 - 1 = m' + 1 := by omega
      have e2 : m' + 2 - 2 = m' := by omega
      rw [e1, e2]; ring_nf; omega
    omega
  omega

theorem requests_bound (L h : ℕ) (W : ComparisonWorld n) (seed : PivotSeed n) (hn : 0 < n) :
    ∀ j, Rpot L (Pseq L W h seed j) ≤ (n - 1) * L := by
  intro j
  induction j with
  | zero => simp [Rpot, Pseq_zero, pivotStart]
  | succ j ih =>
    have hP := good_Pseq L h W seed hn j
    rw [Pseq_succ, pivotStep_eq]
    rcases hsel : selIndex L (Pseq L W h seed j) with _ | k
    · exact ih
    · obtain ⟨hk, hm, hd⟩ := selIndex_some L _ k hsel
      have hU : ((Pseq L W h seed j).slots[k]).1.Nonempty := Finset.card_pos.1 (by omega)
      have hUd : ((Pseq L W h seed j).slots[k]?).getD (∅, 0) = (Pseq L W h seed j).slots[k] := by
        rw [List.getElem?_eq_getElem hk]; rfl
      simp only [hUd]
      set σ := if hj : j < n then seed ⟨j, hj⟩ else Equiv.refl (Fin n)
      have e := (argminIn_spec _ σ hU).1
      split
      · exact ih
      · rename_i p heq
        have : (((Pseq L W h seed j).slots[k]).1.toList.mergeSort fun i j => decide (σ i ≤ σ j)).head? =
            some (argminIn ((Pseq L W h seed j).slots[k]).1 σ hU) := by convert e
        rw [heq] at this
        cases this
        exact le_trans (Rpot_split W h L _ hP k hk hm hd _ (argminIn_spec _ σ hU).2.1) ih

end RQCPivot



noncomputable section

namespace RQCPivot
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem geom_sum (L : ℕ) : ∑ i ∈ Finset.range L, (3 / 2 : ℝ) ^ (i + 1) = 3 * ((3 / 2 : ℝ) ^ L - 1) := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem gpot_zero_le (L : ℕ) : gpot L 0 ≤ 2 * L + 6 := by
  unfold gpot wt
  rw [← Finset.range_eq_Ico, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_div, geom_sum L]
  have hpos : (0 : ℝ) < (3 / 2) ^ L := by positivity
  have : 3 * ((3 / 2 : ℝ) ^ L - 1) / (3 / 2) ^ L ≤ 3 := by
    rw [div_le_iff₀ hpos]; linarith
  linarith

theorem pow_pivotDepth (n : ℕ) (hn : 0 < n) : (n : ℝ) ≤ (3 / 2 : ℝ) ^ pivotDepth n := by
  unfold pivotDepth
  have h1 : Real.logb (3 / 2) n ≤ ⌈Real.logb (3 / 2 : ℝ) n⌉₊ := Nat.le_ceil _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ) = (3 / 2 : ℝ) ^ Real.logb (3 / 2) n := (Real.rpow_logb (by norm_num) (by norm_num) hnR).symm
    _ ≤ (3 / 2 : ℝ) ^ ((⌈Real.logb (3 / 2 : ℝ) n⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = (3 / 2 : ℝ) ^ ⌈Real.logb (3 / 2 : ℝ) n⌉₊ := Real.rpow_natCast _ _

theorem Gam_start (W : ComparisonWorld n) (h L : ℕ) (hn : 0 < n) (hL : (n : ℝ) ≤ (3 / 2 : ℝ) ^ L) :
    Gam L W h (pivotStart (initialState n)) ≤ n / 2 + W.initial.card * (2 * L + 6) + 2 * n * h := by
  unfold Gam
  have hphi : phiSet W.rank (pivotStart (n := n) (initialState n)) = ∅ := by
    rw [phiSet, Finset.filter_eq_empty_iff]
    intro e _ h'
    exact h'.1 ⟨(Finset.univ, 0), by simp [pivotStart], Finset.mem_univ _, Finset.mem_univ _⟩
  have hpsi : psi L (pivotStart (n := n) (initialState n)) ≤ n := by
    unfold psi wt
    simp [pivotStart]
    have hpos : (0 : ℝ) < (3 / 2) ^ L := by positivity
    rw [inv_mul_le_iff₀ hpos]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have htheta : theta L W (pivotStart (n := n) (initialState n)) ≤ W.initial.card * (2 * L + 6) := by
    unfold theta thetaE
    simp only [pivotStart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Finset.mem_univ, and_self, if_true, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (gpot_zero_le L) (Nat.cast_nonneg _)
  rw [hphi]
  have hon : ((pivotStart (n := n) (initialState n)).interaction.online.card : ℝ) = 0 := by
    simp [pivotStart, initialState]
  rw [hon]
  simp only [Finset.card_empty, Nat.cast_zero, zero_add, sub_zero]
  linarith

end RQCPivot

open RankingQueryCost.Joint RQCPivot

theorem solution (n a h : ℕ) (hadm : Admissible n (a + h))
    (W : ComparisonWorld n) (hW : LegalWorld a W) :
    (1 / (Fintype.card (PivotSeed n) : ℝ)) *
      (∑ seed : PivotSeed n, (kendallCount W.rank
        (pivotOutput (pivotExecution 1 (pivotDepth n) (fun _ _ => 0) true W h (initialState n) seed)) : ℝ)) ≤
        2 * a * pivotDepth n + 6 * a + n + 2 * n * h ∧
    (∀ seed : PivotSeed n,
      let P := pivotExecution 1 (pivotDepth n) (fun _ _ => 0) true W h (initialState n) seed
      P.requests.length ≤ n * pivotDepth n ∧ P.requests.Nodup) := by
  have hn : 0 < n := by have := hadm.1; omega
  set L := pivotDepth n
  have hL := pow_pivotDepth n hn
  constructor
  · have hcard : (0 : ℝ) < Fintype.card (PivotSeed n) := by exact_mod_cast Fintype.card_pos
    have hK : ∀ seed : PivotSeed n, (kendallCount W.rank (pivotOutput (pivotExecution 1 L (fun _ _ => 0) true W h
        (initialState n) seed)) : ℝ) ≤ Gam L W h (Pseq L W h seed n) := by
      intro seed
      rw [pivotExecution_eq]
      have hP := good_Pseq L h W seed hn n
      have hk := kendall_le L h _ hP (end_dead L h W seed hn) W.rank
      unfold Gam
      have ht : 0 ≤ theta L W (Pseq L W h seed n) := by
        unfold theta; apply Finset.sum_nonneg; intro e _; unfold thetaE
        apply List.sum_nonneg; intro x hx
        obtain ⟨Ud, -, rfl⟩ := List.mem_map.1 hx
        split_ifs
        · exact gpot_nonneg _ _
        · exact le_refl _
      have ho : ((Pseq L W h seed n).interaction.online.card : ℝ) ≤ h := by exact_mod_cast hP.ok.1
      have : (0 : ℝ) ≤ 2 * n * ((h : ℝ) - (Pseq L W h seed n).interaction.online.card) := by
        apply mul_nonneg (by positivity); linarith
      linarith
    have hsum := expected_Gam L h W hn n (le_refl _)
    have hstart := Gam_start W h L hn hL
    have hinit : (W.initial.card : ℝ) ≤ a := by exact_mod_cast hW
    have h1 : ∑ seed : PivotSeed n, (kendallCount W.rank (pivotOutput (pivotExecution 1 L (fun _ _ => 0) true W h
        (initialState n) seed)) : ℝ) ≤ (Fintype.card (PivotSeed n) : ℝ) * Gam L W h (pivotStart (initialState n)) :=
      le_trans (Finset.sum_le_sum fun seed _ => hK seed) hsum
    rw [one_div, inv_mul_le_iff₀ hcard]
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hcard.le)
    have hLR : (0 : ℝ) ≤ 2 * L + 6 := by positivity
    have : (W.initial.card : ℝ) * (2 * L + 6) ≤ a * (2 * L + 6) := mul_le_mul_of_nonneg_right hinit hLR
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  · intro seed
    simp only
    rw [pivotExecution_eq]
    have hP := good_Pseq L h W seed hn n
    refine ⟨?_, hP.reqnd⟩
    have := requests_bound L h W seed hn n
    unfold Rpot at this
    have h2 : (n - 1) * L ≤ n * L := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
