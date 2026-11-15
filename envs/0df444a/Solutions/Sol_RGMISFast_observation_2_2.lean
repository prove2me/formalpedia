-- Prove2me | solution 1 for RGMISFast.observation_2_2
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T01:43:22.740584+00:00
-- url     : https://prove2.me/submissions/e4839bcc-ca00-42f6-9f6a-f8973e9bd230

import Definitions.Def_RGMISFast_AdmissibleTree
set_option autoImplicit false

namespace ObservationCorrectness
open RGMISFast
set_option autoImplicit false

private theorem fold_shortcircuit_correct {A S : Type*} (P : S → Prop)
    (f : A → S → Bool × S) (g : A → Bool)
    (hf : ∀ a st, P st → P (f a st).2 ∧ (f a st).1 = g a)
    (l : List A) (acc : Bool × S) (hp : P acc.2) :
    P (l.foldl (fun acc a => if acc.1 then acc else f a acc.2) acc).2 ∧
    (l.foldl (fun acc a => if acc.1 then acc else f a acc.2) acc).1 =
      (acc.1 || l.any g) := by
  induction l generalizing acc with
  | nil => simpa using hp
  | cons a l ih =>
    simp only [List.foldl_cons, List.any_cons]
    cases ha : acc.1 with
    | true =>
      simp only [ha, Bool.true_eq, ↓reduceIte, Bool.true_or]
      simpa [ha] using ih acc hp
    | false =>
      simp only [ha, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      obtain ⟨hs, hv⟩ := hf a acc.2 hp
      simpa [hv] using ih (f a acc.2) hs

private def Sound {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (st : RunState V) : Prop :=
  ∀ v b, st.memo v = some b → b = inMIS G r v

private theorem sound_update {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (st : RunState V)
    (hs : Sound G r st) (v : V) (b : Bool) (hb : b = inMIS G r v) :
    Sound G r {st with memo := Function.update st.memo v (some b)} := by
  classical
  intro w c hc
  by_cases hw : w = v
  · subst w
    have he : b = c := by simpa using hc
    exact he.symm.trans hb
  · exact hs w c (by simpa [Function.update_of_ne hw] using hc)

private theorem call_correct {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) st, Sound G r st →
      Sound G r (callF G r n caller v hn st).2 ∧
      (callF G r n caller v hn st).1 = inMIS G r v := by
  classical
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st hs
    simp only [callF]
    split
    next b hb => exact ⟨hs, hs v b hb⟩
    next hb =>
      let s1 : RunState V := {st with count := st.count + 1, trace := st.trace ++ [⟨caller,v,true⟩]}
      let exec := fun (w : {w // w ∈ lowerNbrs G r v}) (s : RunState V) =>
        callF G r n (some v) w.val
          (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) s
      have hf := fold_shortcircuit_correct (Sound G r) exec
        (fun w => inMIS G r w.val)
        (by intro w s h; exact ih _ _ _ _ h)
        (lowerNbrs G r v).attach (false,s1) hs
      let result := (lowerNbrs G r v).attach.foldl
        (fun acc w => if acc.1 then acc else exec w acc.2) (false,s1)
      have hr : (!result.1) = inMIS G r v := by
        rw [inMIS_eq]
        change (!result.1) = _
        rw [show result.1 = ((lowerNbrs G r v).attach.any (fun w => inMIS G r w.val)) by simpa [result] using hf.2]
        exact List.not_any_eq_all_not
      exact ⟨sound_update G r result.2 hf.1 v _ hr, hr⟩

theorem run_correct {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    (∀ v b, (run G r u).2.memo v = some b → b = inMIS G r v) ∧
    (run G r u).1 = inMIS G r u := by
  exact call_correct G r _ none u _ initState (by intro v b h; cases h)

theorem call_correct_of_sound {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ)
    (caller : Option V) (v : V) (hn : rk r v < n) (st : RunState V)
    (hs : ∀ x b, st.memo x = some b → b = inMIS G r x) :
    (∀ x b, (callF G r n caller v hn st).2.memo x = some b → b = inMIS G r x) ∧
    (callF G r n caller v hn st).1 = inMIS G r v :=
  call_correct G r n caller v hn st hs
end ObservationCorrectness
open ObservationCorrectness

namespace ObservationCount
open RGMISFast
set_option autoImplicit false

private theorem fold_preserves {A S : Type*} (P : S → Prop) (f : S → A → S)
    (hf : ∀ s a, P s → P (f s a)) (l : List A) (s : S) (hs : P s) :
    P (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons a l ih => exact ih (f s a) (hf s a hs)

private def CountOK {V : Type*} (st : RunState V) : Prop :=
  st.count = (st.trace.filter (fun e => e.fresh)).length

private theorem count_call {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) st, CountOK st →
      CountOK (callF G r n caller v hn st).2 := by
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st hs
    simp only [callF]
    split
    · simpa [CountOK, List.filter_append] using hs
    · let s1 : RunState V := {st with count := st.count + 1, trace := st.trace ++ [⟨caller,v,true⟩]}
      have hs1 : CountOK s1 := by simpa [CountOK, s1, List.filter_append] using hs
      have hf := fold_preserves (fun acc : Bool × RunState V => CountOK acc.2)
        (fun acc (w : {w // w ∈ lowerNbrs G r v}) => if acc.1 then acc else
          callF G r n (some v) w.val
            (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) acc.2)
        (by intro acc w h; split; exact h; exact ih _ _ _ _ h)
        (lowerNbrs G r v).attach (false,s1) hs1
      exact hf

theorem count_eq_fresh_trace {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).length = Q G u r := by
  rw [List.length_map]
  exact (count_call G r _ none u _ initState rfl).symm
end ObservationCount
open ObservationCount

namespace ObservationTrace
open RGMISFast
set_option autoImplicit false

private def EdgeOK {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (e : CallEvent V) : Prop :=
  e.caller.isSome ∧ ∀ v, e.caller = some v → G.Adj v e.callee ∧ r e.callee < r v

private theorem fold_preserves {A S : Type*} (P : S → Prop) (f : S → A → S)
    (hf : ∀ s a, P s → P (f s a)) (l : List A) (s : S) (hs : P s) :
    P (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons a l ih => exact ih (f s a) (hf s a hs)

private theorem call_trace {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) st,
    ∃ xs, (callF G r n caller v hn st).2.trace =
      st.trace ++ ⟨caller,v,(st.memo v).isNone⟩ :: xs ∧
      ∀ e ∈ xs, EdgeOK G r e := by
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st
    simp only [callF]
    split
    next b hb => exact ⟨[], by simp [hb], by simp⟩
    next hb =>
      let base := st.trace ++ [⟨caller,v,true⟩]
      let P := fun acc : Bool × RunState V =>
        ∃ xs, acc.2.trace = base ++ xs ∧ ∀ e ∈ xs, EdgeOK G r e
      let s1 : RunState V := {st with count := st.count + 1, trace := base}
      have hf := fold_preserves P
        (fun acc (w : {w // w ∈ lowerNbrs G r v}) => if acc.1 then acc else
          callF G r n (some v) w.val
            (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) acc.2)
        (by
          intro acc w hp
          split
          · exact hp
          · obtain ⟨xs, hx, hxs⟩ := hp
            obtain ⟨ys, hy, hys⟩ := ih (some v) w.val
              (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) acc.2
            refine ⟨xs ++ ⟨some v,w.val,(acc.2.memo w.val).isNone⟩ :: ys, ?_, ?_⟩
            · rw [hy, hx, List.append_assoc]
            · intro e he
              rcases List.mem_append.mp he with he | he
              · exact hxs e he
              · rcases List.mem_cons.mp he with he | he
                · subst e
                  refine ⟨by simp, ?_⟩
                  intro p hp
                  have hv : v = p := Option.some.inj hp
                  subst p
                  exact (mem_lowerNbrs G r).mp w.property
                · exact hys e he)
        (lowerNbrs G r v).attach (false,s1)
        (by exact ⟨[], by simp [s1], by simp⟩)
      obtain ⟨xs, hx, hxs⟩ := hf
      refine ⟨xs, ?_, hxs⟩
      simpa [base, hb, List.append_assoc] using hx

theorem run_trace_structure {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    (run G r u).2.trace.head? = some ⟨none,u,true⟩ ∧
    (∀ e ∈ (run G r u).2.trace.tail, e.caller.isSome) ∧
    (∀ e ∈ (run G r u).2.trace, ∀ v, e.caller = some v →
      G.Adj v e.callee ∧ r e.callee < r v) := by
  obtain ⟨xs,hx,hs⟩ := call_trace G r _ none u (Nat.lt_succ_self _) initState
  change (run G r u).2.trace = _ at hx
  simp only [initState, List.nil_append, Option.isNone_none] at hx
  rw [hx]
  refine ⟨rfl, ?_, ?_⟩
  · intro e he
    exact (hs e he).1
  · intro e he v hv
    rcases List.mem_cons.mp he with he | he
    · subst e
      cases hv
    · exact (hs e he).2 v hv

theorem call_trace_prefix {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ)
    (caller : Option V) (v : V) (hn : rk r v < n) (st : RunState V) :
    st.trace <+: (callF G r n caller v hn st).2.trace := by
  obtain ⟨xs,hx,_⟩ := call_trace G r n caller v hn st
  rw [hx]
  exact List.prefix_append _ _
end ObservationTrace
open ObservationTrace

namespace ObservationUnique
open RGMISFast
set_option autoImplicit false

private def Fresh {V : Type*} (st : RunState V) : List V :=
  (st.trace.filter (fun e => e.fresh)).map (fun e => e.callee)

private def PendingInv {V : Type*} (S : Set V) (st : RunState V) : Prop :=
  (Fresh st).Nodup ∧ ∀ v ∈ Fresh st, st.memo v = none → v ∈ S

private theorem fold_preserves {A S : Type*} (P : S → Prop) (f : S → A → S)
    (hf : ∀ s a, P s → P (f s a)) (l : List A) (s : S) (hs : P s) :
    P (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons a l ih => exact ih (f s a) (hf s a hs)

private theorem call_unique {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) st (S : Set V),
      (∀ a ∈ S, r v < r a) → PendingInv S st → PendingInv S (callF G r n caller v hn st).2 := by
  classical
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st S hS hI
    simp only [callF]
    split
    next b hb =>
      simpa [PendingInv, Fresh, List.filter_append] using hI
    next hb =>
      have hv : v ∉ Fresh st := by
        intro hv
        exact (lt_irrefl (r v)) (hS v (hI.2 v hv hb))
      let s1 : RunState V := {st with count := st.count + 1, trace := st.trace ++ [⟨caller,v,true⟩]}
      have hs1 : PendingInv (insert v S) s1 := by
        have hf : Fresh s1 = Fresh st ++ [v] := by simp [Fresh, s1, List.filter_append]
        constructor
        · rw [hf]
          simpa using (List.nodup_append.mpr ⟨hI.1, by simp, by simpa using (show ∀ a ∈ Fresh st, a ≠ v from fun a ha he => hv (he ▸ ha))⟩)
        · intro x hx hm
          rw [hf] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact Set.mem_insert_of_mem _ (hI.2 x hx hm)
          · have he : x = v := by simpa using hx
            exact he ▸ Set.mem_insert _ _
      have hf := fold_preserves (fun acc : Bool × RunState V => PendingInv (insert v S) acc.2)
        (fun acc (w : {w // w ∈ lowerNbrs G r v}) => if acc.1 then acc else
          callF G r n (some v) w.val
            (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) acc.2)
        (by
          intro acc w hp
          split
          · exact hp
          · apply ih _ _ _ _ _ ?_ hp
            intro a ha
            have hw := ((mem_lowerNbrs G r).1 w.property).2
            rcases Set.mem_insert_iff.mp ha with rfl | ha
            · exact hw
            · exact hw.trans (hS a ha))
        (lowerNbrs G r v).attach (false,s1) hs1
      constructor
      · exact hf.1
      · intro x hx hm
        have hxv : x ≠ v := by
          intro he
          subst x
          simpa using hm
        simp only [RunState.memo, Function.update_of_ne hxv] at hm
        have hmem := hf.2 x hx hm
        exact (Set.mem_insert_iff.mp hmem).resolve_left hxv

theorem fresh_calls_nodup {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).Nodup := by
  exact (call_unique G r _ none u (Nat.lt_succ_self _) initState ∅
    (by simp) (by simp [PendingInv, Fresh, initState])).1
end ObservationUnique
open ObservationUnique

namespace ObservationSettling
open RGMISFast
set_option autoImplicit false

private theorem scan_sorted {V : Type*} [LinearOrder V] (r : V → ℝ) (s : Finset V) :
    (scanOrder r s).Pairwise (fun a b => r a ≤ r b) := by
  classical
  rcases s with ⟨m,hm⟩
  induction m using Quot.ind with
  | mk l =>
    change (((l.map (fun a => toLex (r a,a))).insertionSort (· ≤ ·)).map
      (fun p => (ofLex p).2)).Pairwise _
    rw [List.pairwise_map]
    apply (List.pairwise_insertionSort (fun a b : ℝ ×ₗ V => a ≤ b) _).imp_of_mem
    intro a b ha hb hab
    have ha' : (ofLex a).1 = r (ofLex a).2 := by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ((List.mem_insertionSort _).mp ha)
      rfl
    have hb' : (ofLex b).1 = r (ofLex b).2 := by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ((List.mem_insertionSort _).mp hb)
      rfl
    simpa only [ha',hb'] using (Prod.Lex.le_iff'.mp hab).1

private theorem fold_bounded {A S : Type*} (P : S → Prop) (f : A → S → Bool × S)
    (g : A → Bool) (rank : A → ℝ) (T : ℝ)
    (hf : ∀ a s, rank a ≤ T → P s → P (f a s).2 ∧ (f a s).1 = g a)
    (l : List A) (hl : l.Pairwise (fun a b => rank a ≤ rank b))
    (acc : Bool × S) (hp : P acc.2)
    (hb : acc.1 = true ∨ (∀ a ∈ l, rank a ≤ T) ∨ ∃ a ∈ l, g a = true ∧ rank a ≤ T) :
    P (l.foldl (fun acc a => if acc.1 then acc else f a acc.2) acc).2 := by
  induction l generalizing acc with
  | nil => exact hp
  | cons a l ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hl
    simp only [List.foldl_cons]
    by_cases hacc : acc.1 = true
    · simp only [hacc, ↓reduceIte]
      exact ih htail acc hp (Or.inl hacc)
    · simp only [hacc, ↓reduceIte]
      have hrest := hb.resolve_left hacc
      have ha : rank a ≤ T := by
        rcases hrest with hall | ⟨z,hz,hg,hr⟩
        · exact hall a (by simp)
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact hr
          · exact (hhead z hz).trans hr
      obtain ⟨hP,hg⟩ := hf a acc.2 ha hp
      apply ih htail (f a acc.2) hP
      by_cases hga : g a = true
      · exact Or.inl (hg.trans hga)
      · right
        rcases hrest with hall | ⟨z,hz,hgz,hr⟩
        · exact Or.inl (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        · refine Or.inr ⟨z, ?_, hgz, hr⟩
          rcases List.mem_cons.mp hz with rfl | hz
          · exact (hga hgz).elim
          · exact hz

private theorem scan_threshold {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (v : V) :
    (∀ w ∈ lowerNbrs G r v, r w ≤ tau G r v) ∨
    ∃ w ∈ lowerNbrs G r v, inMIS G r w = true ∧ r w ≤ tau G r v := by
  classical
  by_cases hv : r v ≤ tau G r v
  · exact Or.inl (fun w hw => ((mem_lowerNbrs G r).1 hw).2.le.trans hv)
  · have ht : tau G r v ∈
        (((insert v (G.neighborFinset v)).filter (fun x => inMIS G r x = true)).image r) :=
      Finset.min'_mem _ _
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp ht
    obtain ⟨hw,hyes⟩ := Finset.mem_filter.mp hw
    have hlt : r w < r v := by rw [he]; exact lt_of_not_ge hv
    have hne : w ≠ v := by intro h; subst w; exact (lt_irrefl _) hlt
    have hadj : G.Adj v w := by simpa [hne] using hw
    exact Or.inr ⟨w,(mem_lowerNbrs G r).2 ⟨hadj,hlt⟩,hyes,he.le⟩

private def GoodState {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (st : RunState V) : Prop :=
    (∀ x b, st.memo x = some b → b = inMIS G r x) ∧
    ∀ e ∈ st.trace, ∀ p, e.caller = some p → r e.callee ≤ tau G r p

private theorem call_settling {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) st, GoodState G r st →
      (∀ p, caller = some p → r v ≤ tau G r p) →
      GoodState G r (callF G r n caller v hn st).2 := by
  classical
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st hs hc
    have hcorrect := (call_correct_of_sound G r (n+1) caller v hn st hs.1).1
    refine ⟨hcorrect, ?_⟩
    simp only [callF]
    split
    next b hb =>
      intro e he p hp
      rcases List.mem_append.mp he with he | he
      · exact hs.2 e he p hp
      · have he' : e = ⟨caller,v,false⟩ := by simpa using he
        subst e
        exact hc p hp
    next hb =>
      let s1 : RunState V := {st with count := st.count+1, trace := st.trace ++ [⟨caller,v,true⟩]}
      have hs1 : GoodState G r s1 := by
        refine ⟨hs.1, ?_⟩
        intro e he p hp
        rcases List.mem_append.mp he with he | he
        · exact hs.2 e he p hp
        · have he' : e = ⟨caller,v,true⟩ := by simpa using he
          subst e
          exact hc p hp
      let exec := fun (w : {w // w ∈ lowerNbrs G r v}) (s : RunState V) =>
        callF G r n (some v) w.val
          (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) s
      have hsort : (lowerNbrs G r v).attach.Pairwise (fun a b => r a.val ≤ r b.val) := by
        rw [← List.pairwise_map]
        simpa [List.pairwise_map, lowerNbrs] using scan_sorted r ((G.neighborFinset v).filter (fun w => r w < r v))
      have hf := fold_bounded (GoodState G r) exec (fun w => inMIS G r w.val)
        (fun w => r w.val) (tau G r v)
        (by
          intro w s hw hp
          refine ⟨ih _ _ _ _ hp ?_, (call_correct_of_sound G r n _ _ _ s hp.1).2⟩
          intro p he
          have he' : v = p := Option.some.inj he
          subst p
          exact hw)
        (lowerNbrs G r v).attach hsort (false,s1) hs1
        (by
          right
          rcases scan_threshold G r v with hall | ⟨w,hw,hyes,hle⟩
          · exact Or.inl (fun w _ => hall w.val w.property)
          · exact Or.inr ⟨⟨w,hw⟩, by simp, hyes, hle⟩)
      exact hf.2

theorem run_settling_bound {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    ∀ e ∈ (run G r u).2.trace, ∀ p, e.caller = some p →
      r e.callee ≤ tau G r p := by
  exact (call_settling G r _ none u (Nat.lt_succ_self _) initState
    (by constructor <;> simp [initState]) (by simp)).2
end ObservationSettling
open ObservationSettling

namespace ObservationParents
open RGMISFast
set_option autoImplicit false

private def FreshNodes {V : Type*} (st : RunState V) : List V :=
  (st.trace.filter (fun e => e.fresh)).map (fun e => e.callee)

private theorem fresh_mono {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ)
    (caller : Option V) (v : V) (hn : rk r v < n) (st : RunState V) :
    ∀ x ∈ FreshNodes st, x ∈ FreshNodes (callF G r n caller v hn st).2 := by
  intro x hx
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
  obtain ⟨he,hf⟩ := List.mem_filter.mp he
  apply List.mem_map.mpr
  exact ⟨e,List.mem_filter.mpr ⟨(call_trace_prefix G r n caller v hn st).subset he,hf⟩,rfl⟩

private def ParentsOK {V : Type*} (st : RunState V) : Prop :=
  ∀ e ∈ st.trace, ∀ p, e.caller = some p → p ∈ FreshNodes st

private theorem fold_preserves {A S : Type*} (P : S → Prop) (f : S → A → S)
    (hf : ∀ s a, P s → P (f s a)) (l : List A) (s : S) (hs : P s) :
    P (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons a l ih => exact ih (f s a) (hf s a hs)

private theorem call_parents {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) st, ParentsOK st →
      (∀ p, caller = some p → p ∈ FreshNodes st) →
      ParentsOK (callF G r n caller v hn st).2 := by
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st hs hc
    simp only [callF]
    split
    next b hb =>
      intro e he p hp
      have hf : FreshNodes {st with trace := st.trace ++ [⟨caller,v,false⟩]} = FreshNodes st := by
        simp [FreshNodes,List.filter_append]
      rw [hf]
      rcases List.mem_append.mp he with he | he
      · exact hs e he p hp
      · have he' : e = ⟨caller,v,false⟩ := by simpa using he
        subst e
        exact hc p hp
    next hb =>
      let s1 : RunState V := {st with count := st.count+1, trace := st.trace ++ [⟨caller,v,true⟩]}
      have hfs : FreshNodes s1 = FreshNodes st ++ [v] := by simp [FreshNodes,s1,List.filter_append]
      have hs1 : ParentsOK s1 ∧ v ∈ FreshNodes s1 := by
        constructor
        · intro e he p hp
          rw [hfs]
          apply List.mem_append_left
          rcases List.mem_append.mp he with he | he
          · exact hs e he p hp
          · have he' : e = ⟨caller,v,true⟩ := by simpa using he
            subst e
            exact hc p hp
        · rw [hfs]; simp
      have hf := fold_preserves (fun acc : Bool × RunState V => ParentsOK acc.2 ∧ v ∈ FreshNodes acc.2)
        (fun acc (w : {w // w ∈ lowerNbrs G r v}) => if acc.1 then acc else
          callF G r n (some v) w.val
            (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) acc.2)
        (by
          intro acc w hp
          split
          · exact hp
          · refine ⟨ih _ _ _ _ hp.1 ?_, fresh_mono G r n _ _ _ acc.2 v hp.2⟩
            intro p he
            have he' : v = p := Option.some.inj he
            exact he' ▸ hp.2)
        (lowerNbrs G r v).attach (false,s1) hs1
      exact hf.1

theorem run_parents_fresh {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    ∀ e ∈ (run G r u).2.trace, ∀ p, e.caller = some p →
      p ∈ (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)) := by
  exact call_parents G r _ none u (Nat.lt_succ_self _) initState (by simp [ParentsOK,initState]) (by simp)
end ObservationParents
open ObservationParents

open RGMISFast
set_option autoImplicit false

theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (r : V → ℝ) (hinj : Function.Injective r)
    (hnn : ∀ v, 0 ≤ r v) :
    (∀ v b, (run G r u).2.memo v = some b → b = inMIS G r v) ∧
    (run G r u).1 = inMIS G r u ∧
    (run G r u).2.trace.head? = some ⟨none, u, true⟩ ∧
    (∀ e ∈ (run G r u).2.trace.tail, e.caller.isSome) ∧
    (∀ e ∈ (run G r u).2.trace, ∀ v, e.caller = some v → G.Adj v e.callee ∧ r e.callee < r v) ∧
    (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).Nodup ∧
    (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).length = Q G u r ∧
    ∃ T : AdmissibleTree G r u,
      T.nodes = (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).toFinset ∧
      ∀ e ∈ (run G r u).2.trace, e.fresh = true → ∀ v, e.caller = some v → T.par e.callee = v := by
  classical
  obtain ⟨hm,ha⟩ := run_correct G u r
  obtain ⟨hh,ht,he⟩ := run_trace_structure G u r
  have hd := fresh_calls_nodup G u r
  refine ⟨hm,ha,hh,ht,he,hd,count_eq_fresh_trace G u r,?_⟩
  let events := (run G r u).2.trace
  let fresh := events.filter (fun e => e.fresh)
  let nodes := (fresh.map (fun e => e.callee)).toFinset
  obtain ⟨tail,htail⟩ := List.head?_eq_some_iff.mp hh
  have hroot : u ∈ nodes := by
    simp [nodes,fresh,events,htail]
  have hex (w : V) (hw : w ∈ nodes) : ∃ e ∈ fresh, e.callee = w := by
    exact List.mem_map.mp (List.mem_toFinset.mp hw)
  let ev (w : V) : CallEvent V := if hw : w ∈ nodes then Classical.choose (hex w hw) else ⟨none,u,false⟩
  have hev (w : V) (hw : w ∈ nodes) : ev w ∈ fresh ∧ (ev w).callee = w := by
    simpa only [ev,dif_pos hw] using Classical.choose_spec (hex w hw)
  let par (w : V) := (ev w).caller.getD u
  have hp (w : V) (hw : w ∈ nodes) (hwu : w ≠ u) : (ev w).caller = some (par w) := by
    have hwmem := (List.mem_filter.mp (hev w hw).1).1
    dsimp [events] at hwmem
    have hwtail : ev w ∈ (run G r u).2.trace.tail := by
      rw [htail] at hwmem ⊢
      rcases List.mem_cons.mp hwmem with hwmem | hwmem
      · have : w = u := (hev w hw).2.symm.trans (congrArg CallEvent.callee hwmem)
        exact (hwu this).elim
      · exact hwmem
    have hs := ht (ev w) hwtail
    dsimp [par]
    cases hc : (ev w).caller with
    | none => simp [hc] at hs
    | some p => rfl
  let T : AdmissibleTree G r u := {
    nodes := nodes
    root_mem := hroot
    par := par
    depth := fun w => Fintype.card V - rk r w
    par_mem := by
      intro w hw hwu
      exact List.mem_toFinset.mpr (run_parents_fresh G u r (ev w)
        (List.mem_filter.mp (hev w hw).1).1 (par w) (hp w hw hwu))
    par_adj := by
      intro w hw hwu
      have h := (he (ev w) (List.mem_filter.mp (hev w hw).1).1 (par w) (hp w hw hwu)).1
      simpa only [(hev w hw).2] using h
    rank_le := by
      intro w hw hwu
      have h := run_settling_bound G u r (ev w) (List.mem_filter.mp (hev w hw).1).1 (par w) (hp w hw hwu)
      simpa only [(hev w hw).2] using h
    depth_lt := by
      intro w hw hwu
      have hl := (he (ev w) (List.mem_filter.mp (hev w hw).1).1 (par w) (hp w hw hwu)).2
      rw [(hev w hw).2] at hl
      have hi := rk_lt r hl
      have hb : rk r (par w) ≤ Fintype.card V := by
        unfold rk
        exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
      omega }
  refine ⟨T,rfl,?_⟩
  intro e hem hef v hcaller
  have ef : e ∈ fresh := List.mem_filter.mpr ⟨hem,hef⟩
  have hn : e.callee ∈ nodes := List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,ef,rfl⟩)
  have ee : ev e.callee = e := List.inj_on_of_nodup_map hd (hev _ hn).1 ef (hev _ hn).2
  change (ev e.callee).caller.getD u = v
  rw [ee,hcaller]
  rfl
