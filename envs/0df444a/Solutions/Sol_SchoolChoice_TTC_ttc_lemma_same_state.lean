-- Prove2me | solution 1 for SchoolChoice.TTC.ttc_lemma_same_state
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:45:52.552744+00:00
-- url     : https://prove2.me/submissions/a12a40f4-16fc-4737-b8cc-9290073f7bf8

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Model
import Definitions.Def_SchoolChoice_TTC_Algorithm
import Definitions.Def_SchoolChoice_TTC_SerialDictatorship



namespace SchoolChoice.TTC

variable {I S : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

lemma bestIn_some_iff {α : Type} {n : ℕ} (r : α ≃ Fin n) (T : Finset α) (x : α) :
    bestIn r T = some x ↔ x ∈ T ∧ ∀ y ∈ T, r x ≤ r y := by
  unfold bestIn
  split_ifs with h
  · constructor
    · intro hx
      simp only [Option.some.injEq] at hx
      subst hx
      obtain ⟨a, ha, hm⟩ := Finset.mem_image.1 (Finset.min'_mem (T.image r) (h.image r))
      refine ⟨?_, fun y hy => ?_⟩
      · rw [← hm]; simpa using ha
      · simp only [Equiv.apply_symm_apply]
        exact Finset.min'_le _ _ (Finset.mem_image_of_mem r hy)
    · rintro ⟨hx, hmin⟩
      have : (T.image r).min' (h.image r) = r x := by
        apply le_antisymm (Finset.min'_le _ _ (Finset.mem_image_of_mem r hx))
        apply Finset.le_min'
        intro y hy
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
        exact hmin b hb
      rw [this]; simp
  · simp only [reduceCtorEq, false_iff, not_and]
    intro hx; exact absurd ⟨x, hx⟩ h

lemma bestIn_none_iff {α : Type} {n : ℕ} (r : α ≃ Fin n) (T : Finset α) :
    bestIn r T = none ↔ T = ∅ := by
  unfold bestIn
  split_ifs with h
  · simp [h.ne_empty]
  · simp [Finset.not_nonempty_iff_eq_empty.1 h]

lemma bestIn_exists {α : Type} {n : ℕ} (r : α ≃ Fin n) {T : Finset α} (h : T.Nonempty) :
    ∃ x, bestIn r T = some x := by
  cases hb : bestIn r T with
  | none => rw [bestIn_none_iff] at hb; simp [hb] at h
  | some x => exact ⟨x, rfl⟩

lemma bestIn_mono {α : Type} {n : ℕ} (r : α ≃ Fin n) {T T' : Finset α} {x : α}
    (hT : T' ⊆ T) (hx : bestIn r T = some x) (hx' : x ∈ T') : bestIn r T' = some x := by
  rw [bestIn_some_iff] at *
  exact ⟨hx', fun y hy => hx.2 y (hT hy)⟩

section Graph
variable (P : I → Pref S) (pri : S → Priority I) (st : State I S)

lemma nextO_none : nextO P pri st none = none := rfl

lemma nextO_some_eq {j k : I} (h : nextO P pri st (some j) = some k) :
    ∃ s, pointS P st j = some s ∧ pointI pri st s = some k := by
  simpa [nextO, Option.bind_eq_some_iff] using h

lemma pointS_mem {j : I} {s : S} (h : pointS P st j = some s) : s ∈ remSchools st :=
  ((bestIn_some_iff _ _ _).1 h).1

lemma pointI_mem {s : S} {k : I} (h : pointI pri st s = some k) : k ∈ st.rem :=
  ((bestIn_some_iff _ _ _).1 h).1

lemma iterate_mem {x : Option I} {k : I} (n : ℕ)
    (h : (nextO P pri st)^[n+1] x = some k) : k ∈ st.rem := by
  rw [Function.iterate_succ_apply'] at h
  cases hx : (nextO P pri st)^[n] x with
  | none => rw [hx] at h; simp [nextO_none] at h
  | some j =>
    rw [hx] at h
    obtain ⟨s, _, hk⟩ := nextO_some_eq P pri st h
    exact pointI_mem pri st hk

lemma inCycle_iff (j : I) : InCycle P pri st j ↔ j ∈ st.rem ∧ ∃ p, 0 < p ∧
    p ≤ Fintype.card I ∧ (nextO P pri st)^[p] (some j) = some j := by
  unfold InCycle
  constructor
  · rintro ⟨h, n, hn, he⟩
    simp only [Finset.mem_range] at hn
    exact ⟨h, n+1, by omega, by omega, he⟩
  · rintro ⟨h, p, hp, hp', he⟩
    refine ⟨h, p-1, by simp; omega, ?_⟩
    rwa [Nat.sub_add_cancel hp]

lemma cycle_succ {j k : I} (hj : InCycle P pri st j) (h : nextO P pri st (some j) = some k) :
    InCycle P pri st k := by
  rw [inCycle_iff] at *
  obtain ⟨_, p, hp, hp', he⟩ := hj
  refine ⟨iterate_mem P pri st 0 (x := some j) (by simpa using h), p, hp, hp', ?_⟩
  rw [← h, ← Function.iterate_succ_apply, Function.iterate_succ_apply', he]

lemma cycle_inj {j j' : I} (hj : InCycle P pri st j) (hj' : InCycle P pri st j')
    (h : nextO P pri st (some j) = nextO P pri st (some j')) : j = j' := by
  rw [inCycle_iff] at hj hj'
  obtain ⟨_, p, hp, _, he⟩ := hj
  obtain ⟨_, p', hp2, _, he'⟩ := hj'
  have h1 : Function.IsPeriodicPt (nextO P pri st) (p*p') (some j) :=
    (show Function.IsPeriodicPt (nextO P pri st) p (some j) from he).mul_const p'
  have h2 : Function.IsPeriodicPt (nextO P pri st) (p*p') (some j') :=
    (show Function.IsPeriodicPt (nextO P pri st) p' (some j') from he').const_mul p
  have hpos : 0 < p * p' := Nat.mul_pos hp hp2
  have e1 := h1.eq
  have e2 := h2.eq
  rw [← Nat.sub_add_cancel hpos, Function.iterate_succ_apply] at e1 e2
  rw [h] at e1
  rw [e1] at e2
  exact Option.some_injective _ e2

lemma cycle_reach {x i : I} (hx : InCycle P pri st x) (m : ℕ)
    (hm : (nextO P pri st)^[m] (some x) = some i) : InCycle P pri st i := by
  rw [inCycle_iff] at *
  obtain ⟨hxr, p, hp, hp', he⟩ := hx
  refine ⟨?_, p, hp, hp', ?_⟩
  · rcases m with _ | m
    · simp at hm; rw [← hm]; exact hxr
    · exact iterate_mem P pri st m hm
  · rw [← hm, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, he]

lemma exists_cycle (hr : st.rem.Nonempty) (hs : (remSchools st).Nonempty) :
    ∃ j, InCycle P pri st j := by
  have hf : ∀ j ∈ st.rem, ∃ k ∈ st.rem, nextO P pri st (some j) = some k := by
    intro j _
    obtain ⟨s, hsj⟩ := bestIn_exists (P j) hs
    obtain ⟨k, hk⟩ := bestIn_exists (pri s) hr
    refine ⟨k, pointI_mem pri st (s := s) hk, ?_⟩
    simp only [nextO, Option.bind_some]
    change (pointS P st j).bind (pointI pri st) = _
    rw [show pointS P st j = some s from hsj]
    exact hk
  obtain ⟨j0, hj0⟩ := hr
  have hit : ∀ n, ∃ k ∈ st.rem, (nextO P pri st)^[n] (some j0) = some k := by
    intro n
    induction n with
    | zero => exact ⟨j0, hj0, rfl⟩
    | succ n ih =>
      obtain ⟨k, hk, he⟩ := ih
      obtain ⟨k', hk', he'⟩ := hf k hk
      exact ⟨k', hk', by rw [Function.iterate_succ_apply', he, he']⟩
  have key : ∀ a b, a < b → b ≤ Fintype.card I →
      (nextO P pri st)^[a] (some j0) = (nextO P pri st)^[b] (some j0) →
      ∃ j, InCycle P pri st j := by
    intro a b hab hb he
    obtain ⟨k, hk, hke⟩ := hit a
    refine ⟨k, (inCycle_iff P pri st k).2 ⟨hk, b - a, by omega, by omega, ?_⟩⟩
    rw [← hke, ← Function.iterate_add_apply, Nat.sub_add_cancel hab.le, ← he]
  have hc : (st.rem.image some).card < (Finset.range (Fintype.card I + 1)).card := by
    simp only [Finset.card_range]
    have := Finset.card_image_le (s := st.rem) (f := some)
    have := Finset.card_le_univ st.rem
    omega
  obtain ⟨a, ha, b, hb, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := fun n => (nextO P pri st)^[n] (some j0)) (by
      intro n _
      obtain ⟨k, hk, he⟩ := hit n
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨k, hk, he.symm⟩)
  simp only [Finset.mem_range] at ha hb
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h (by omega) he
  · exact key b a h (by omega) he.symm

end Graph

section Step
variable (P : I → Pref S) (pri : S → Priority I) (st : State I S)

lemma mem_cycleStudents {j : I} : j ∈ cycleStudents P pri st ↔ InCycle P pri st j := by
  unfold cycleStudents; simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma cycleStudents_sub : cycleStudents P pri st ⊆ st.rem := Finset.filter_subset _ _

lemma step_rem : (step P pri st).rem = st.rem \ cycleStudents P pri st := rfl
lemma step_cnt (s : S) : (step P pri st).cnt s = st.cnt s -
    ((cycleStudents P pri st).filter (fun i => pointS P st i = some s)).card := rfl
lemma step_asg (j : I) : (step P pri st).asg j =
    if j ∈ cycleStudents P pri st then pointS P st j else st.asg j := rfl

lemma nextO_some_def (j : I) :
    nextO P pri st (some j) = (pointS P st j).bind (pointI pri st) := rfl

lemma iterate_none (n : ℕ) : (nextO P pri st)^[n] none = none :=
  Function.iterate_fixed (nextO_none P pri st) n

lemma cycle_next {j : I} (h : InCycle P pri st j) :
    ∃ k, nextO P pri st (some j) = some k ∧ InCycle P pri st k := by
  cases hk : nextO P pri st (some j) with
  | none =>
    exfalso
    obtain ⟨_, p, hp, _, he⟩ := (inCycle_iff P pri st j).1 h
    rw [← Nat.sub_add_cancel hp, Function.iterate_succ_apply, hk, iterate_none] at he
    exact absurd he (by simp)
  | some k => exact ⟨k, rfl, cycle_succ P pri st h hk⟩

lemma cycle_pointS {j : I} (h : InCycle P pri st j) :
    ∃ s, pointS P st j = some s ∧ ∃ k, pointI pri st s = some k ∧ InCycle P pri st k := by
  obtain ⟨k, hk, hkc⟩ := cycle_next P pri st h
  obtain ⟨s, hs, hsk⟩ := nextO_some_eq P pri st hk
  exact ⟨s, hs, k, hsk, hkc⟩

lemma card_filter_le_one (s : S) :
    ((cycleStudents P pri st).filter (fun i => pointS P st i = some s)).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter, mem_cycleStudents] at ha hb
  apply cycle_inj P pri st ha.1 hb.1
  rw [nextO_some_def, nextO_some_def, ha.2, hb.2]

lemma filter_le_cnt (s : S) :
    ((cycleStudents P pri st).filter (fun i => pointS P st i = some s)).card ≤ st.cnt s := by
  have h1 := card_filter_le_one P pri st s
  rcases Nat.eq_zero_or_pos ((cycleStudents P pri st).filter
    (fun i => pointS P st i = some s)).card with h | h
  · omega
  · obtain ⟨a, ha⟩ := Finset.card_pos.1 h
    simp only [Finset.mem_filter] at ha
    have := pointS_mem P st ha.2
    simp only [remSchools, Finset.mem_filter] at this
    omega

lemma sum_filter_card :
    ∑ s, ((cycleStudents P pri st).filter (fun i => pointS P st i = some s)).card =
      (cycleStudents P pri st).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := pointS P st) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _), Fintype.sum_option]
  have : (cycleStudents P pri st).filter (fun i => pointS P st i = none) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro j hj
    obtain ⟨s, hs, _⟩ := cycle_pointS P pri st ((mem_cycleStudents P pri st).1 hj)
    simp [hs]
  rw [this]; simp

def Good (q : S → ℕ) (st : State I S) : Prop :=
  (∀ j, j ∈ st.rem ↔ st.asg j = none) ∧
  (∀ s, (Finset.univ.filter (fun j => st.asg j = some s)).card + st.cnt s = q s) ∧
  st.rem.card ≤ ∑ s, st.cnt s

lemma good_step (q : S → ℕ) (h : Good q st) : Good q (step P pri st) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [step_rem, step_asg, Finset.mem_sdiff]
    by_cases hC : j ∈ cycleStudents P pri st
    · obtain ⟨s, hs, _⟩ := cycle_pointS P pri st ((mem_cycleStudents P pri st).1 hC)
      simp [hC, hs]
    · simp [hC, h1]
  · intro s
    have hset : Finset.univ.filter (fun j => (step P pri st).asg j = some s) =
        Finset.univ.filter (fun j => st.asg j = some s) ∪
          (cycleStudents P pri st).filter (fun i => pointS P st i = some s) := by
      ext j
      rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, step_asg]
      simp only [Finset.mem_univ, true_and]
      by_cases hC : j ∈ cycleStudents P pri st
      · have : st.asg j = none := (h1 j).1 (cycleStudents_sub P pri st hC)
        simp [hC, this]
      · simp [hC]
    have hdisj : Disjoint (Finset.univ.filter (fun j => st.asg j = some s))
        ((cycleStudents P pri st).filter (fun i => pointS P st i = some s)) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
      have : st.asg j = none := (h1 j).1 (cycleStudents_sub P pri st hj'.1)
      rw [this] at hj; exact absurd hj (by simp)
    rw [hset, Finset.card_union_of_disjoint hdisj, step_cnt]
    have := filter_le_cnt P pri st s
    have := h2 s
    omega
  · rw [step_rem, Finset.card_sdiff_of_subset (cycleStudents_sub P pri st)]
    have hsum : ∑ s, (step P pri st).cnt s +
        ∑ s, ((cycleStudents P pri st).filter (fun i => pointS P st i = some s)).card =
          ∑ s, st.cnt s := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      rw [step_cnt]
      exact Nat.sub_add_cancel (filter_le_cnt P pri st s)
    rw [sum_filter_card] at hsum
    omega

lemma remSchools_nonempty (q : S → ℕ) (h : Good q st) (hr : st.rem.Nonempty) :
    (remSchools st).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty, remSchools, Finset.filter_eq_empty_iff] at hne
  have : ∑ s, st.cnt s = 0 := Finset.sum_eq_zero (fun s _ => by
    have := hne (Finset.mem_univ s); omega)
  have := h.2.2
  have := Finset.card_pos.2 hr
  omega

lemma step_card_lt (q : S → ℕ) (h : Good q st) (hr : st.rem.Nonempty) :
    (step P pri st).rem.card < st.rem.card := by
  obtain ⟨j, hj⟩ := exists_cycle P pri st hr (remSchools_nonempty st q h hr)
  rw [step_rem, Finset.card_sdiff_of_subset (cycleStudents_sub P pri st)]
  have : 0 < (cycleStudents P pri st).card :=
    Finset.card_pos.2 ⟨j, (mem_cycleStudents P pri st).2 hj⟩
  have := Finset.card_le_card (cycleStudents_sub P pri st)
  omega

end Step

section Run
variable (q : S → ℕ) (pri : S → Priority I) (P : I → Pref S)

lemma run_zero : run q pri P 0 = init q := rfl

lemma run_succ (t : ℕ) : run q pri P (t + 1) = step P pri (run q pri P t) :=
  Function.iterate_succ_apply' _ _ _

lemma good_run (hq : Fintype.card I ≤ ∑ s, q s) (t : ℕ) : Good q (run q pri P t) := by
  induction t with
  | zero =>
    refine ⟨fun j => by simp [run_zero, init], fun s => by simp [run_zero, init], ?_⟩
    simpa [run_zero, init] using hq
  | succ t ih => rw [run_succ]; exact good_step P pri _ q ih

lemma run_card (hq : Fintype.card I ≤ ∑ s, q s) (t : ℕ) :
    (run q pri P t).rem.card ≤ Fintype.card I - t := by
  induction t with
  | zero => simpa [run_zero, init] using Finset.card_le_univ _
  | succ t ih =>
    rw [run_succ]
    rcases (run q pri P t).rem.eq_empty_or_nonempty with h | h
    · rw [step_rem, h]; simp
    · have := step_card_lt P pri _ q (good_run q pri P hq t) h
      omega

lemma run_final (hq : Fintype.card I ≤ ∑ s, q s) :
    (run q pri P (Fintype.card I)).rem = ∅ := by
  have := run_card q pri P hq (Fintype.card I)
  simpa using this

lemma ttc_terminates_core (hq : Fintype.card I ≤ ∑ s, q s) :
    (run q pri P (Fintype.card I)).rem = ∅ ∧
      ∃ μ : I → S, (∀ i, ttc q pri P i = some (μ i)) ∧ IsMatching q μ := by
  refine ⟨run_final q pri P hq, ?_⟩
  have hg := good_run q pri P hq (Fintype.card I)
  have h : ∀ i, ∃ s, ttc q pri P i = some s := by
    intro i
    have : ttc q pri P i ≠ none := by
      intro hn
      have := (hg.1 i).2 hn
      rw [run_final q pri P hq] at this
      simp at this
    exact Option.ne_none_iff_exists'.1 this
  choose μ hμ using h
  refine ⟨μ, hμ, fun s => ?_⟩
  have := hg.2.1 s
  have he : Finset.univ.filter (fun i => μ i = s) =
      Finset.univ.filter (fun j => (run q pri P (Fintype.card I)).asg j = some s) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change _ ↔ ttc q pri P j = some s
    rw [hμ j]; simp
  rw [he]; omega

end Run

lemma iterate_agree {α : Type} (f g : α → α) (a : α) (hfg : ∀ x, x ≠ a → g x = f x)
    (x : α) (n : ℕ) (h : ∀ k < n, f^[k] x ≠ a) : g^[n] x = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun k hk => h k (by omega))]
    exact hfg _ (h n (by omega))

section Dev
variable (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S)

lemma pointS_update (st : State I S) {j : I} (hj : j ≠ i) :
    pointS (Function.update P i Qi) st j = pointS P st j := by
  simp [pointS, Function.update_of_ne hj]

lemma nextO_update (st : State I S) (o : Option I) (ho : o ≠ some i) :
    nextO (Function.update P i Qi) pri st o = nextO P pri st o := by
  cases o with
  | none => rfl
  | some j =>
    have hj : j ≠ i := fun h => ho (by rw [h])
    rw [nextO_some_def, nextO_some_def, pointS_update P i Qi st hj]

lemma inCycle_transfer (P₁ P₂ : I → Pref S) (st : State I S)
    (hag : ∀ o, o ≠ some i → nextO P₂ pri st o = nextO P₁ pri st o)
    (hi : ¬ InCycle P₁ pri st i) {j : I} (hj : InCycle P₁ pri st j) : InCycle P₂ pri st j := by
  have hj' := (inCycle_iff P₁ pri st j).1 hj
  obtain ⟨hr, p, hp, hp', he⟩ := hj'
  refine (inCycle_iff P₂ pri st j).2 ⟨hr, p, hp, hp', ?_⟩
  rw [iterate_agree (nextO P₁ pri st) (nextO P₂ pri st) (some i) hag (some j) p
    (fun k _ hk => hi (cycle_reach P₁ pri st hj k hk)), he]

lemma cycleStudents_eq (st : State I S)
    (h1 : ¬ InCycle P pri st i) (h2 : ¬ InCycle (Function.update P i Qi) pri st i) :
    cycleStudents P pri st = cycleStudents (Function.update P i Qi) pri st := by
  ext j
  rw [mem_cycleStudents, mem_cycleStudents]
  constructor
  · exact inCycle_transfer pri i P _ st (nextO_update pri P i Qi st) h1
  · exact inCycle_transfer pri i _ P st (fun o ho => (nextO_update pri P i Qi st o ho).symm) h2

lemma step_eq (st : State I S)
    (h1 : ¬ InCycle P pri st i) (h2 : ¬ InCycle (Function.update P i Qi) pri st i) :
    step P pri st = step (Function.update P i Qi) pri st := by
  have hC := cycleStudents_eq pri P i Qi st h1 h2
  have hne : ∀ j ∈ cycleStudents P pri st, j ≠ i := by
    intro j hj hji; subst hji; exact h1 ((mem_cycleStudents P pri st).1 hj)
  unfold step
  simp only
  rw [← hC]
  congr 1
  · funext s
    congr 2
    apply Finset.filter_congr
    intro j hj
    rw [pointS_update P i Qi st (hne j hj)]
  · funext j
    by_cases hj : j ∈ cycleStudents P pri st
    · simp [hj, pointS_update P i Qi st (hne j hj)]
    · simp [hj]

lemma not_cycle_of_mem_step (P : I → Pref S) (st : State I S) {j : I}
    (h : j ∈ (step P pri st).rem) : j ∈ st.rem ∧ ¬ InCycle P pri st j := by
  rw [step_rem, Finset.mem_sdiff, mem_cycleStudents] at h
  exact h

lemma run_eq (q : S → ℕ) (t : ℕ) (hi : i ∈ (run q pri P t).rem)
    (hi' : i ∈ (run q pri (Function.update P i Qi) t).rem) :
    run q pri P t = run q pri (Function.update P i Qi) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ] at hi hi' ⊢
    rw [run_succ]
    obtain ⟨a1, b1⟩ := not_cycle_of_mem_step pri P _ hi
    obtain ⟨a2, b2⟩ := not_cycle_of_mem_step pri _ _ hi'
    have e := ih a1 a2
    rw [← e] at b2 ⊢
    exact step_eq pri P i Qi _ b1 b2

lemma ttc_lemma_same_state_core (q : S → ℕ) (t : ℕ)
    (hi : i ∈ (run q pri P t).rem)
    (hi' : i ∈ (run q pri (Function.update P i Qi) t).rem) :
    (run q pri P t).rem = (run q pri (Function.update P i Qi) t).rem ∧
      remSchools (run q pri P t) = remSchools (run q pri (Function.update P i Qi) t) := by
  rw [run_eq pri P i Qi q t hi hi']
  exact ⟨rfl, rfl⟩

end Dev

end SchoolChoice.TTC

open SchoolChoice.TTC


theorem solution {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) (t : ℕ)
    (hi : i ∈ (run q pri P t).rem)
    (hi' : i ∈ (run q pri (Function.update P i Qi) t).rem) :
    (run q pri P t).rem = (run q pri (Function.update P i Qi) t).rem ∧
      remSchools (run q pri P t) = remSchools (run q pri (Function.update P i Qi) t) := by
  exact ttc_lemma_same_state_core pri P i Qi q t hi hi'
