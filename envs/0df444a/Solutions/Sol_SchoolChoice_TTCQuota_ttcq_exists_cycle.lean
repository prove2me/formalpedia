-- Prove2me | solution 1 for SchoolChoice.TTCQuota.ttcq_exists_cycle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:19:50.063359+00:00
-- url     : https://prove2.me/submissions/ad424f8c-67b9-4cef-a2fc-2dd2e4e54e00

import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm



namespace SchoolChoice.TTCQuota

variable {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype Ty] [DecidableEq Ty]

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
variable (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty)

lemma nextO_none : nextO P pri τ st none = none := rfl

lemma nextO_some_eq {j k : I} (h : nextO P pri τ st (some j) = some k) :
    ∃ s, pointS P τ st j = some s ∧ pointI pri st s = some k := by
  simpa [nextO, Option.bind_eq_some_iff] using h

lemma pointS_mem {j : I} {s : S} (h : pointS P τ st j = some s) : s ∈ roomFor st (τ j) :=
  ((bestIn_some_iff _ _ _).1 h).1

lemma pointI_mem {s : S} {k : I} (h : pointI pri st s = some k) : k ∈ st.rem :=
  ((bestIn_some_iff _ _ _).1 h).1

lemma iterate_mem {x : Option I} {k : I} (n : ℕ)
    (h : (nextO P pri τ st)^[n+1] x = some k) : k ∈ st.rem := by
  rw [Function.iterate_succ_apply'] at h
  cases hx : (nextO P pri τ st)^[n] x with
  | none => rw [hx] at h; simp [nextO_none] at h
  | some j =>
    rw [hx] at h
    obtain ⟨s, _, hk⟩ := nextO_some_eq P pri τ st h
    exact pointI_mem pri st hk

lemma inCycle_iff (j : I) : InCycle P pri τ st j ↔ j ∈ st.rem ∧ ∃ p, 0 < p ∧
    p ≤ Fintype.card I ∧ (nextO P pri τ st)^[p] (some j) = some j := by
  unfold InCycle
  constructor
  · rintro ⟨h, n, hn, he⟩
    simp only [Finset.mem_range] at hn
    exact ⟨h, n+1, by omega, by omega, he⟩
  · rintro ⟨h, p, hp, hp', he⟩
    refine ⟨h, p-1, by simp; omega, ?_⟩
    rwa [Nat.sub_add_cancel hp]

lemma cycle_succ {j k : I} (hj : InCycle P pri τ st j) (h : nextO P pri τ st (some j) = some k) :
    InCycle P pri τ st k := by
  rw [inCycle_iff] at *
  obtain ⟨_, p, hp, hp', he⟩ := hj
  refine ⟨iterate_mem P pri τ st 0 (x := some j) (by simpa using h), p, hp, hp', ?_⟩
  rw [← h, ← Function.iterate_succ_apply, Function.iterate_succ_apply', he]

lemma cycle_inj {j j' : I} (hj : InCycle P pri τ st j) (hj' : InCycle P pri τ st j')
    (h : nextO P pri τ st (some j) = nextO P pri τ st (some j')) : j = j' := by
  rw [inCycle_iff] at hj hj'
  obtain ⟨_, p, hp, _, he⟩ := hj
  obtain ⟨_, p', hp2, _, he'⟩ := hj'
  have h1 : Function.IsPeriodicPt (nextO P pri τ st) (p*p') (some j) :=
    (show Function.IsPeriodicPt (nextO P pri τ st) p (some j) from he).mul_const p'
  have h2 : Function.IsPeriodicPt (nextO P pri τ st) (p*p') (some j') :=
    (show Function.IsPeriodicPt (nextO P pri τ st) p' (some j') from he').const_mul p
  have hpos : 0 < p * p' := Nat.mul_pos hp hp2
  have e1 := h1.eq
  have e2 := h2.eq
  rw [← Nat.sub_add_cancel hpos, Function.iterate_succ_apply] at e1 e2
  rw [h] at e1
  rw [e1] at e2
  exact Option.some_injective _ e2

lemma cycle_reach {x i : I} (hx : InCycle P pri τ st x) (m : ℕ)
    (hm : (nextO P pri τ st)^[m] (some x) = some i) : InCycle P pri τ st i := by
  rw [inCycle_iff] at *
  obtain ⟨hxr, p, hp, hp', he⟩ := hx
  refine ⟨?_, p, hp, hp', ?_⟩
  · rcases m with _ | m
    · simp at hm; rw [← hm]; exact hxr
    · exact iterate_mem P pri τ st m hm
  · rw [← hm, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, he]


lemma exists_cycle (hr : st.rem.Nonempty) (hroom : ∀ j ∈ st.rem, (roomFor st (τ j)).Nonempty) :
    ∃ j, InCycle P pri τ st j := by
  have hf : ∀ j ∈ st.rem, ∃ k ∈ st.rem, nextO P pri τ st (some j) = some k := by
    intro j hj
    obtain ⟨s, hsj⟩ := bestIn_exists (P j) (hroom j hj)
    obtain ⟨k, hk⟩ := bestIn_exists (pri s) hr
    refine ⟨k, pointI_mem pri st (s := s) hk, ?_⟩
    simp only [nextO, Option.bind_some]
    change (pointS P τ st j).bind (pointI pri st) = _
    rw [show pointS P τ st j = some s from hsj]
    exact hk
  obtain ⟨j0, hj0⟩ := hr
  have hit : ∀ n, ∃ k ∈ st.rem, (nextO P pri τ st)^[n] (some j0) = some k := by
    intro n
    induction n with
    | zero => exact ⟨j0, hj0, rfl⟩
    | succ n ih =>
      obtain ⟨k, hk, he⟩ := ih
      obtain ⟨k', hk', he'⟩ := hf k hk
      exact ⟨k', hk', by rw [Function.iterate_succ_apply', he, he']⟩
  have key : ∀ a b, a < b → b ≤ Fintype.card I →
      (nextO P pri τ st)^[a] (some j0) = (nextO P pri τ st)^[b] (some j0) →
      ∃ j, InCycle P pri τ st j := by
    intro a b hab hb he
    obtain ⟨k, hk, hke⟩ := hit a
    refine ⟨k, (inCycle_iff P pri τ st k).2 ⟨hk, b - a, by omega, by omega, ?_⟩⟩
    rw [← hke, ← Function.iterate_add_apply, Nat.sub_add_cancel hab.le, ← he]
  have hc : (st.rem.image some).card < (Finset.range (Fintype.card I + 1)).card := by
    simp only [Finset.card_range]
    have := Finset.card_image_le (s := st.rem) (f := some)
    have := Finset.card_le_univ st.rem
    omega
  obtain ⟨a, ha, b, hb, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := fun n => (nextO P pri τ st)^[n] (some j0)) (by
      intro n _
      obtain ⟨k, hk, he⟩ := hit n
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨k, hk, he.symm⟩)
  simp only [Finset.mem_range] at ha hb
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h (by omega) he
  · exact key b a h (by omega) he.symm

lemma mem_cycleStudents {j : I} : j ∈ cycleStudents P pri τ st ↔ InCycle P pri τ st j := by
  unfold cycleStudents; simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma cycleStudents_sub : cycleStudents P pri τ st ⊆ st.rem := Finset.filter_subset _ _

lemma nextO_some_def (j : I) :
    nextO P pri τ st (some j) = (pointS P τ st j).bind (pointI pri st) := rfl

lemma iterate_none (n : ℕ) : (nextO P pri τ st)^[n] none = none :=
  Function.iterate_fixed (nextO_none P pri τ st) n

lemma cycle_next {j : I} (h : InCycle P pri τ st j) :
    ∃ k, nextO P pri τ st (some j) = some k ∧ InCycle P pri τ st k := by
  cases hk : nextO P pri τ st (some j) with
  | none =>
    exfalso
    obtain ⟨_, p, hp, _, he⟩ := (inCycle_iff P pri τ st j).1 h
    rw [← Nat.sub_add_cancel hp, Function.iterate_succ_apply, hk, iterate_none] at he
    exact absurd he (by simp)
  | some k => exact ⟨k, rfl, cycle_succ P pri τ st h hk⟩

lemma cycle_pointS {j : I} (h : InCycle P pri τ st j) :
    ∃ s, pointS P τ st j = some s ∧ ∃ k, pointI pri st s = some k ∧ InCycle P pri τ st k := by
  obtain ⟨k, hk, hkc⟩ := cycle_next P pri τ st h
  obtain ⟨s, hs, hsk⟩ := nextO_some_eq P pri τ st hk
  exact ⟨s, hs, k, hsk, hkc⟩

lemma card_filter_le_one (s : S) :
    ((cycleStudents P pri τ st).filter (fun i => pointS P τ st i = some s)).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter, mem_cycleStudents] at ha hb
  apply cycle_inj P pri τ st ha.1 hb.1
  rw [nextO_some_def, nextO_some_def, ha.2, hb.2]

lemma filter_le_cnt (s : S) :
    ((cycleStudents P pri τ st).filter (fun i => pointS P τ st i = some s)).card ≤ st.cnt s := by
  have h1 := card_filter_le_one P pri τ st s
  rcases Nat.eq_zero_or_pos ((cycleStudents P pri τ st).filter
    (fun i => pointS P τ st i = some s)).card with h | h
  · omega
  · obtain ⟨a, ha⟩ := Finset.card_pos.1 h
    simp only [Finset.mem_filter] at ha
    have := pointS_mem P τ st ha.2
    simp only [roomFor, Finset.mem_filter] at this
    omega

lemma filter_le_tcnt (s : S) (t : Ty) :
    ((cycleStudents P pri τ st).filter (fun i => pointS P τ st i = some s ∧ τ i = t)).card
      ≤ st.tcnt s t := by
  have h1 := card_filter_le_one P pri τ st s
  have h2 : ((cycleStudents P pri τ st).filter (fun i => pointS P τ st i = some s ∧ τ i = t)).card
      ≤ ((cycleStudents P pri τ st).filter (fun i => pointS P τ st i = some s)).card :=
    Finset.card_le_card (fun a ha => by
      simp only [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1⟩)
  rcases Nat.eq_zero_or_pos ((cycleStudents P pri τ st).filter
    (fun i => pointS P τ st i = some s ∧ τ i = t)).card with h | h
  · omega
  · obtain ⟨a, ha⟩ := Finset.card_pos.1 h
    simp only [Finset.mem_filter] at ha
    have := pointS_mem P τ st ha.2.1
    simp only [roomFor, Finset.mem_filter] at this
    rw [ha.2.2] at this
    omega

lemma sum_filter_card :
    ∑ s, ((cycleStudents P pri τ st).filter (fun i => pointS P τ st i = some s)).card =
      (cycleStudents P pri τ st).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := pointS P τ st) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _), Fintype.sum_option]
  have : (cycleStudents P pri τ st).filter (fun i => pointS P τ st i = none) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro j hj
    obtain ⟨s, hs, _⟩ := cycle_pointS P pri τ st ((mem_cycleStudents P pri τ st).1 hj)
    simp [hs]
  rw [this]; simp

end Graph

section Step
variable (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty)

lemma roomFor_prune (t : Ty) : roomFor (prune τ st) t = roomFor st t := rfl

lemma prune_rem_sub : (prune τ st).rem ⊆ st.rem := Finset.filter_subset _ _

lemma mem_prune {j : I} : j ∈ (prune τ st).rem ↔ j ∈ st.rem ∧ (roomFor st (τ j)).Nonempty := by
  simp [prune]

lemma step_rem : (step P pri τ st).rem =
    (prune τ st).rem \ cycleStudents P pri τ (prune τ st) := rfl
lemma step_cnt (s : S) : (step P pri τ st).cnt s = st.cnt s -
    ((cycleStudents P pri τ (prune τ st)).filter
      (fun i => pointS P τ (prune τ st) i = some s)).card := rfl
lemma step_tcnt (s : S) (t : Ty) : (step P pri τ st).tcnt s t = st.tcnt s t -
    ((cycleStudents P pri τ (prune τ st)).filter
      (fun i => pointS P τ (prune τ st) i = some s ∧ τ i = t)).card := rfl
lemma step_asg (j : I) : (step P pri τ st).asg j =
    if j ∈ cycleStudents P pri τ (prune τ st) then pointS P τ (prune τ st) j else st.asg j := rfl

def GoodQ (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (st : State I S Ty) : Prop :=
  (∀ j ∈ st.rem, st.asg j = none) ∧
  (∀ s, (Finset.univ.filter (fun j => st.asg j = some s)).card + st.cnt s = q s) ∧
  (∀ s t, (Finset.univ.filter (fun j => st.asg j = some s ∧ τ j = t)).card + st.tcnt s t
    = qt s t)

lemma good_step (q : S → ℕ) (qt : S → Ty → ℕ) (h : GoodQ q qt τ st) :
    GoodQ q qt τ (step P pri τ st) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hCn : ∀ j ∈ cycleStudents P pri τ (prune τ st), st.asg j = none := fun j hj =>
    h1 j (prune_rem_sub τ st (cycleStudents_sub P pri τ _ hj))
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [step_rem, Finset.mem_sdiff] at hj
    rw [step_asg, if_neg hj.2]
    exact h1 j (prune_rem_sub τ st hj.1)
  · intro s
    have hset : Finset.univ.filter (fun j => (step P pri τ st).asg j = some s) =
        Finset.univ.filter (fun j => st.asg j = some s) ∪
          (cycleStudents P pri τ (prune τ st)).filter
            (fun i => pointS P τ (prune τ st) i = some s) := by
      ext j
      rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, step_asg]
      simp only [Finset.mem_univ, true_and]
      by_cases hC : j ∈ cycleStudents P pri τ (prune τ st)
      · simp [hC, hCn j hC]
      · simp [hC]
    have hdisj : Disjoint (Finset.univ.filter (fun j => st.asg j = some s))
        ((cycleStudents P pri τ (prune τ st)).filter
          (fun i => pointS P τ (prune τ st) i = some s)) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
      rw [hCn j hj'.1] at hj; exact absurd hj (by simp)
    rw [hset, Finset.card_union_of_disjoint hdisj, step_cnt]
    have := filter_le_cnt P pri τ (prune τ st) s
    have := h2 s
    change _ ≤ st.cnt s at *
    omega
  · intro s t
    have hset : Finset.univ.filter (fun j => (step P pri τ st).asg j = some s ∧ τ j = t) =
        Finset.univ.filter (fun j => st.asg j = some s ∧ τ j = t) ∪
          (cycleStudents P pri τ (prune τ st)).filter
            (fun i => pointS P τ (prune τ st) i = some s ∧ τ i = t) := by
      ext j
      rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, step_asg]
      simp only [Finset.mem_univ, true_and]
      by_cases hC : j ∈ cycleStudents P pri τ (prune τ st)
      · simp [hC, hCn j hC]
      · simp [hC]
    have hdisj : Disjoint (Finset.univ.filter (fun j => st.asg j = some s ∧ τ j = t))
        ((cycleStudents P pri τ (prune τ st)).filter
          (fun i => pointS P τ (prune τ st) i = some s ∧ τ i = t)) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
      rw [hCn j hj'.1] at hj; exact absurd hj.1 (by simp)
    rw [hset, Finset.card_union_of_disjoint hdisj, step_tcnt]
    have := filter_le_tcnt P pri τ (prune τ st) s t
    have := h3 s t
    change _ ≤ st.tcnt s t at *
    omega

lemma step_card_lt (hr : st.rem.Nonempty) :
    (step P pri τ st).rem.card < st.rem.card := by
  rcases (prune τ st).rem.eq_empty_or_nonempty with h | h
  · rw [step_rem, h]; simpa using Finset.card_pos.2 hr
  · have hroom : ∀ j ∈ (prune τ st).rem, (roomFor (prune τ st) (τ j)).Nonempty := by
      intro j hj; exact ((mem_prune τ st).1 hj).2
    obtain ⟨j, hj⟩ := exists_cycle P pri τ (prune τ st) h hroom
    rw [step_rem, Finset.card_sdiff_of_subset (cycleStudents_sub P pri τ _)]
    have : 0 < (cycleStudents P pri τ (prune τ st)).card :=
      Finset.card_pos.2 ⟨j, (mem_cycleStudents P pri τ _).2 hj⟩
    have := Finset.card_le_card (cycleStudents_sub P pri τ (prune τ st))
    have := Finset.card_le_card (prune_rem_sub τ st)
    omega

end Step

section Run
variable (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (pri : S → Priority I) (P : I → Pref S)

lemma run_zero : run q qt τ pri P 0 = init q qt := rfl

lemma run_succ (t : ℕ) : run q qt τ pri P (t + 1) = step P pri τ (run q qt τ pri P t) :=
  Function.iterate_succ_apply' _ _ _

lemma good_run (t : ℕ) : GoodQ q qt τ (run q qt τ pri P t) := by
  induction t with
  | zero =>
    refine ⟨fun j _ => by simp [run_zero, init], fun s => by simp [run_zero, init],
      fun s t => by simp [run_zero, init]⟩
  | succ t ih => rw [run_succ]; exact good_step P pri τ _ q qt ih

lemma run_card (t : ℕ) :
    (run q qt τ pri P t).rem.card ≤ Fintype.card I - t := by
  induction t with
  | zero => simpa [run_zero, init] using Finset.card_le_univ _
  | succ t ih =>
    rw [run_succ]
    rcases (run q qt τ pri P t).rem.eq_empty_or_nonempty with h | h
    · have := Finset.card_le_card (show (step P pri τ (run q qt τ pri P t)).rem ⊆ ∅ by
        rw [← h, step_rem]; exact Finset.sdiff_subset.trans (prune_rem_sub τ _))
      simp at this; rw [this]; simp
    · have := step_card_lt P pri τ _ h
      omega

lemma run_final : (run q qt τ pri P (Fintype.card I)).rem = ∅ := by
  have := run_card q qt τ pri P (Fintype.card I)
  simpa using this

lemma exists_cycle_core (t : ℕ) (hrem : (prune τ (run q qt τ pri P t)).rem.Nonempty) :
    ∃ i ∈ (prune τ (run q qt τ pri P t)).rem,
      InCycle P pri τ (prune τ (run q qt τ pri P t)) i := by
  obtain ⟨j, hj⟩ := exists_cycle P pri τ _ hrem (fun j hj => ((mem_prune τ _).1 hj).2)
  exact ⟨j, hj.1, hj⟩

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
variable (pri : S → Priority I) (τ : I → Ty) (P : I → Pref S) (i : I) (Qi : Pref S)

lemma pointS_update (st : State I S Ty) {j : I} (hj : j ≠ i) :
    pointS (Function.update P i Qi) τ st j = pointS P τ st j := by
  simp [pointS, Function.update_of_ne hj]

lemma nextO_update (st : State I S Ty) (o : Option I) (ho : o ≠ some i) :
    nextO (Function.update P i Qi) pri τ st o = nextO P pri τ st o := by
  cases o with
  | none => rfl
  | some j =>
    have hj : j ≠ i := fun h => ho (by rw [h])
    rw [nextO_some_def, nextO_some_def, pointS_update τ P i Qi st hj]

lemma inCycle_transfer (P₁ P₂ : I → Pref S) (st : State I S Ty)
    (hag : ∀ o, o ≠ some i → nextO P₂ pri τ st o = nextO P₁ pri τ st o)
    (hi : ¬ InCycle P₁ pri τ st i) {j : I} (hj : InCycle P₁ pri τ st j) :
    InCycle P₂ pri τ st j := by
  have hj' := (inCycle_iff P₁ pri τ st j).1 hj
  obtain ⟨hr, p, hp, hp', he⟩ := hj'
  refine (inCycle_iff P₂ pri τ st j).2 ⟨hr, p, hp, hp', ?_⟩
  rw [iterate_agree (nextO P₁ pri τ st) (nextO P₂ pri τ st) (some i) hag (some j) p
    (fun k _ hk => hi (cycle_reach P₁ pri τ st hj k hk)), he]

lemma cycleStudents_eq (st : State I S Ty)
    (h1 : ¬ InCycle P pri τ st i) (h2 : ¬ InCycle (Function.update P i Qi) pri τ st i) :
    cycleStudents P pri τ st = cycleStudents (Function.update P i Qi) pri τ st := by
  ext j
  rw [mem_cycleStudents, mem_cycleStudents]
  constructor
  · exact inCycle_transfer pri τ i P _ st (nextO_update pri τ P i Qi st) h1
  · exact inCycle_transfer pri τ i _ P st
      (fun o ho => (nextO_update pri τ P i Qi st o ho).symm) h2

lemma step_eq (st : State I S Ty)
    (h1 : ¬ InCycle P pri τ (prune τ st) i)
    (h2 : ¬ InCycle (Function.update P i Qi) pri τ (prune τ st) i) :
    step P pri τ st = step (Function.update P i Qi) pri τ st := by
  have hC := cycleStudents_eq pri τ P i Qi (prune τ st) h1 h2
  have hne : ∀ j ∈ cycleStudents P pri τ (prune τ st), j ≠ i := by
    intro j hj hji; subst hji; exact h1 ((mem_cycleStudents P pri τ _).1 hj)
  unfold step
  simp only
  rw [← hC]
  congr 1
  · funext s
    congr 2
    apply Finset.filter_congr
    intro j hj
    rw [pointS_update τ P i Qi _ (hne j hj)]
  · funext s t
    congr 2
    apply Finset.filter_congr
    intro j hj
    rw [pointS_update τ P i Qi _ (hne j hj)]
  · funext j
    by_cases hj : j ∈ cycleStudents P pri τ (prune τ st)
    · simp [hj, pointS_update τ P i Qi _ (hne j hj)]
    · simp [hj]

lemma not_cycle_of_mem_step (P : I → Pref S) (st : State I S Ty) {j : I}
    (h : j ∈ (step P pri τ st).rem) :
    j ∈ (prune τ st).rem ∧ ¬ InCycle P pri τ (prune τ st) j := by
  rw [step_rem, Finset.mem_sdiff, mem_cycleStudents] at h
  exact h

lemma run_eq (q : S → ℕ) (qt : S → Ty → ℕ) (t : ℕ) (hi : i ∈ (run q qt τ pri P t).rem)
    (hi' : i ∈ (run q qt τ pri (Function.update P i Qi) t).rem) :
    run q qt τ pri P t = run q qt τ pri (Function.update P i Qi) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ] at hi hi' ⊢
    rw [run_succ]
    obtain ⟨a1, b1⟩ := not_cycle_of_mem_step pri τ P _ hi
    obtain ⟨a2, b2⟩ := not_cycle_of_mem_step pri τ _ _ hi'
    have e := ih (prune_rem_sub τ _ a1) (prune_rem_sub τ _ a2)
    rw [← e] at b2 ⊢
    exact step_eq pri τ P i Qi _ b1 b2

lemma same_state_core (q : S → ℕ) (qt : S → Ty → ℕ) (t : ℕ)
    (hi : i ∈ (run q qt τ pri P t).rem)
    (hi' : i ∈ (run q qt τ pri (Function.update P i Qi) t).rem) :
    (run q qt τ pri P t).rem = (run q qt τ pri (Function.update P i Qi) t).rem ∧
      (run q qt τ pri P t).cnt = (run q qt τ pri (Function.update P i Qi) t).cnt ∧
      (run q qt τ pri P t).tcnt = (run q qt τ pri (Function.update P i Qi) t).tcnt := by
  rw [run_eq pri τ P i Qi q qt t hi hi']
  exact ⟨rfl, rfl, rfl⟩

end Dev

end SchoolChoice.TTCQuota

open SchoolChoice.TTCQuota


theorem solution {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (t : ℕ)
    (hrem : (prune τ (run q qt τ pri P t)).rem.Nonempty) :
    ∃ i ∈ (prune τ (run q qt τ pri P t)).rem,
      InCycle P pri τ (prune τ (run q qt τ pri P t)) i := by
  exact exists_cycle_core q qt τ pri P t hrem
