-- Prove2me | solution 1 for StochKnapSL.CapacityGap.gamma_achievable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:06:44.644255+00:00
-- url     : https://prove2.me/submissions/6b4e163a-8c23-4e08-a605-80ce87364c5e

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory
open StochKnapSL.CapacityGap

namespace SKRun

variable {N : ℕ}

/-- one step of the run of `P` on `x` -/
noncomputable def F (P : AdaptivePolicy N) (x : Fin N → ℝ) (s : RunState N) : RunState N :=
  step (P.next s.chosen x) x s

def init (Q : ℝ) : RunState N := ⟨[], [], Q, false⟩

lemma run_eq (P : AdaptivePolicy N) (Q : ℝ) (x : Fin N → ℝ) :
    run P Q x = (F P x)^[N] (init Q) := rfl

lemma step_chosen_mono (c : Option (Fin N)) (x : Fin N → ℝ) (s : RunState N) (a : Fin N)
    (h : a ∈ s.chosen) : a ∈ (step c x s).chosen := by
  unfold step
  split_ifs with h1
  · exact h
  · rcases c with _ | c
    · exact h
    · simp only
      split_ifs <;> simp [h]

lemma step_full_mono (c : Option (Fin N)) (x : Fin N → ℝ) (s : RunState N) (a : Fin N)
    (h : a ∈ s.full) : a ∈ (step c x s).full := by
  unfold step
  split_ifs with h1
  · exact h
  · rcases c with _ | c
    · exact h
    · simp only
      split_ifs <;> simp [h]

lemma iter_full_mono (P : AdaptivePolicy N) (x : Fin N → ℝ) (s : RunState N) (a : Fin N)
    (m : ℕ) (h : a ∈ s.full) : a ∈ ((F P x)^[m] s).full := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact step_full_mono _ _ _ _ ih

lemma step_congr (c : Option (Fin N)) (x x' : Fin N → ℝ) (s : RunState N) (k : Fin N)
    (hk : k ∉ (step c x s).chosen) (hx : ∀ j, j ≠ k → x j = x' j) :
    step c x s = step c x' s := by
  unfold step at hk ⊢
  split_ifs at hk ⊢ with h1
  · rfl
  · rcases c with _ | c
    · rfl
    · simp only at hk ⊢
      by_cases hc : c ∈ s.chosen
      · simp [hc]
      · have hck : c ≠ k := by
          rintro rfl
          apply hk
          split_ifs <;> simp
        rw [hx c hck]

lemma iter_congr (P : AdaptivePolicy N) (Q : ℝ) (x x' : Fin N → ℝ) (k : Fin N)
    (hx : ∀ j, j ≠ k → x j = x' j) (n : ℕ)
    (hk : k ∉ ((F P x)^[n] (init Q)).chosen) :
    (F P x)^[n] (init Q) = (F P x')^[n] (init Q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hk
    have hk' : k ∉ ((F P x)^[n] (init Q)).chosen := fun h => hk (step_chosen_mono _ _ _ _ h)
    have e := ih hk'
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← e]
    set s := (F P x)^[n] (init Q)
    have hnext : P.next s.chosen x = P.next s.chosen x' := by
      apply P.nonanticipative
      intro j hj
      exact hx j (fun h => hk' (h ▸ hj))
    show step (P.next s.chosen x) x s = step (P.next s.chosen x') x' s
    rw [← hnext]
    exact step_congr _ _ _ _ k hk hx

lemma reached_congr (P : AdaptivePolicy N) (Q : ℝ) (x x' : Fin N → ℝ) (k : Fin N)
    (hx : ∀ j, j ≠ k → x j = x' j) : reached P Q x k ↔ reached P Q x' k := by
  have key : ∀ y y' : Fin N → ℝ, (∀ j, j ≠ k → y j = y' j) →
      ¬ reached P Q y k → ¬ reached P Q y' k := by
    intro y y' hy h
    unfold reached at h ⊢
    rw [run_eq] at h ⊢
    rw [← iter_congr P Q y y' k hy N h]
    exact h
  constructor
  · intro h; by_contra h'; exact key x' x (fun j hj => (hx j hj).symm) h' h
  · intro h; by_contra h'; exact key x x' hx h' h

/-- invariant of a run -/
def Inv (Q : ℝ) (x : Fin N → ℝ) (s : RunState N) : Prop :=
  s.chosen.Nodup ∧ (s.full.map x).sum ≤ Q ∧
    ((s.chosen = s.full ∧ s.rem = Q - (s.full.map x).sum) ∨
      (∃ a, s.chosen = s.full ++ [a] ∧ s.stopped = true))

lemma inv_step (Q : ℝ) (x : Fin N → ℝ) (c : Option (Fin N)) (s : RunState N)
    (h : Inv Q x s) : Inv Q x (step c x s) := by
  obtain ⟨hnd, hsum, hcase⟩ := h
  unfold step
  split_ifs with h1
  · exact ⟨hnd, hsum, hcase⟩
  · rcases c with _ | c
    · refine ⟨hnd, hsum, ?_⟩
      rcases hcase with h | ⟨a, ha, _⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, rfl⟩
    · simp only
      have hc' : s.chosen = s.full ∧ s.rem = Q - (s.full.map x).sum := by
        rcases hcase with h | ⟨a, _, hs⟩
        · exact h
        · simp_all
      split_ifs with h2 h3
      · refine ⟨hnd, hsum, ?_⟩
        rcases hcase with h | ⟨a, ha, _⟩
        · exact Or.inl h
        · exact Or.inr ⟨a, ha, rfl⟩
      · refine ⟨?_, ?_, ?_⟩
        · exact List.nodup_append.2 ⟨hnd, List.nodup_singleton _, by
            intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; exact fun e => h2 (e ▸ ha)⟩
        · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
            List.sum_cons, List.sum_nil]
          linarith [hc'.2]
        · left
          refine ⟨by rw [hc'.1], ?_⟩
          simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
            List.sum_cons, List.sum_nil]
          rw [hc'.2]; ring
      · refine ⟨List.nodup_append.2 ⟨hnd, List.nodup_singleton _, by
            intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; exact fun e => h2 (e ▸ ha)⟩,
          hsum, Or.inr ⟨c, by rw [hc'.1], rfl⟩⟩

lemma inv_iter (P : AdaptivePolicy N) (Q : ℝ) (hQ : 0 ≤ Q) (x : Fin N → ℝ) (n : ℕ) :
    Inv Q x ((F P x)^[n] (init Q)) := by
  induction n with
  | zero => exact ⟨List.nodup_nil, by simpa [init] using hQ, Or.inl ⟨rfl, by simp [init]⟩⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step _ _ _ _ ih

lemma full_sub_chosen (P : AdaptivePolicy N) (Q : ℝ) (hQ : 0 ≤ Q) (x : Fin N → ℝ) (i : Fin N)
    (h : fullyServed P Q x i) : reached P Q x i := by
  unfold fullyServed at h; unfold reached
  obtain ⟨_, _, hc⟩ := inv_iter P Q hQ x N
  rw [run_eq] at h ⊢
  rcases hc with ⟨e, _⟩ | ⟨a, e, _⟩
  · rw [e]; exact h
  · rw [e]; exact List.mem_append_left _ h

lemma chosen_sum_le (P : AdaptivePolicy N) (Q : ℝ) (hQ : 0 ≤ Q) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (x : Fin N → ℝ) (hxΔ : ∀ j, x j ≤ Δ) :
    ((run P Q x).chosen.map x).sum ≤ Q + Δ := by
  obtain ⟨_, hs, hc⟩ := inv_iter P Q hQ x N
  rw [run_eq]
  rcases hc with ⟨e, _⟩ | ⟨a, e, _⟩
  · rw [e]; linarith
  · rw [e]; simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    linarith [hxΔ a]

lemma chosen_nodup (P : AdaptivePolicy N) (Q : ℝ) (hQ : 0 ≤ Q) (x : Fin N → ℝ) :
    (run P Q x).chosen.Nodup := (inv_iter P Q hQ x N).1

/-- pointwise bound for the rounded policy -/
lemma reached_sum_le (P : AdaptivePolicy N) (Q : ℝ) (hQ : 0 ≤ Q) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (x : Fin N → ℝ) (hx0 : ∀ j, 0 ≤ x j) (hxΔ : ∀ j, x j ≤ Δ) (U : Finset (Fin N)) :
    ∑ k ∈ U, x k * (if reached P Q x k then (1 : ℝ) else 0) ≤ Q + Δ := by
  set L := (run P Q x).chosen
  have hnd : L.Nodup := chosen_nodup P Q hQ x
  have e1 : ∑ k ∈ U, x k * (if reached P Q x k then (1 : ℝ) else 0) =
      ∑ k ∈ U.filter (fun k => k ∈ L), x k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : reached P Q x k
    · rw [if_pos h, if_pos (show k ∈ L from h)]; ring
    · rw [if_neg h, if_neg (show k ∉ L from h)]; ring
  rw [e1]
  have e2 : ∑ k ∈ L.toFinset, x k = (L.map x).sum := by
    rw [List.sum_toFinset _ hnd]
  calc ∑ k ∈ U.filter (fun k => k ∈ L), x k ≤ ∑ k ∈ L.toFinset, x k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk; simp only [Finset.mem_filter] at hk; simpa using hk.2
        · intro k _ _; exact hx0 k
    _ = (L.map x).sum := e2
    _ ≤ Q + Δ := chosen_sum_le P Q hQ Δ hΔ x hxΔ

/-! ### priority policies -/

lemma find_not_mem_take {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup) (n : ℕ)
    (hn : n < L.length) : L.find? (fun c => decide (c ∉ L.take n)) = some L[n] := by
  have e0 : L.find? (fun c => decide (c ∉ L.take n)) =
      (L.take n ++ L.drop n).find? (fun c => decide (c ∉ L.take n)) := by
    rw [List.take_append_drop]
  rw [e0, List.find?_append]
  have h1 : (L.take n).find? (fun c => decide (c ∉ L.take n)) = none := by
    rw [List.find?_eq_none]; intro a ha; simp [ha]
  rw [h1, Option.none_or, List.drop_eq_getElem_cons hn]
  have h2 : L[n] ∉ L.take n := by
    intro hm
    have hd := List.disjoint_take_drop (l := L) hL (le_refl n)
    exact hd hm (by rw [List.drop_eq_getElem_cons hn]; exact List.mem_cons_self)
  simp [List.find?_cons, h2]

def pre (σ : Equiv.Perm (Fin N)) (n : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => (σ.symm j).val < n)

lemma pre_succ (σ : Equiv.Perm (Fin N)) (n : ℕ) (hn : n < N) (x : Fin N → ℝ) :
    ∑ j ∈ pre σ (n+1), x j = ∑ j ∈ pre σ n, x j + x (σ ⟨n, hn⟩) := by
  have hnot : σ ⟨n, hn⟩ ∉ pre σ n := by simp [pre]
  have e : pre σ (n+1) = insert (σ ⟨n, hn⟩) (pre σ n) := by
    ext j
    simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · left
        have e : σ.symm j = ⟨n, hn⟩ := Fin.ext h
        rw [← e]; simp
    · rintro (rfl | h)
      · simp
      · omega
  rw [e, Finset.sum_insert hnot, add_comm]

lemma prio_iter (σ : Equiv.Perm (Fin N)) (Q' : ℝ) (x : Fin N → ℝ) (n : ℕ) (hn : n ≤ N)
    (hpre : ∀ m < n, ∑ j ∈ pre σ (m+1), x j ≤ Q') :
    (F (priority σ) x)^[n] (init Q') =
      ⟨(List.ofFn σ).take n, (List.ofFn σ).take n, Q' - ∑ j ∈ pre σ n, x j, false⟩ := by
  induction n with
  | zero => simp [init, pre]
  | succ n ih =>
    have hnN : n < N := by omega
    rw [Function.iterate_succ_apply', ih (by omega) (fun m hm => hpre m (by omega))]
    set L := List.ofFn σ
    have hlen : n < L.length := by simp [L]; omega
    have hnd : L.Nodup := List.nodup_ofFn.2 σ.injective
    have hLn : L[n] = σ ⟨n, hnN⟩ := by simp [L]
    have hfind : L.find? (fun c => decide (c ∉ L.take n)) = some (σ ⟨n, hnN⟩) := by
      rw [find_not_mem_take L hnd n hlen, hLn]
    have hnotin : σ ⟨n, hnN⟩ ∉ L.take n := by
      intro hm
      have hd := List.disjoint_take_drop (l := L) hnd (le_refl n)
      exact hd hm (by rw [List.drop_eq_getElem_cons hlen, hLn]; exact List.mem_cons_self)
    have hcap : x (σ ⟨n, hnN⟩) ≤ Q' - ∑ j ∈ pre σ n, x j := by
      have := hpre n (by omega); rw [pre_succ σ n hnN] at this; linarith
    have htake : L.take n ++ [σ ⟨n, hnN⟩] = L.take (n+1) := by
      rw [← hLn]; exact List.take_append_getElem hlen
    show step ((List.ofFn σ).find? (fun c => decide (c ∉ L.take n))) x _ = _
    rw [hfind]
    unfold step
    dsimp only
    rw [if_neg (by decide), if_neg hnotin, if_pos hcap, htake, pre_succ σ n hnN]
    congr 1; ring

lemma prio_full (σ : Equiv.Perm (Fin N)) (Q' : ℝ) (x : Fin N → ℝ) (hx : ∀ j, 0 ≤ x j)
    (i : Fin N) (h : ∑ j ∈ ahead σ i, x j + x i ≤ Q') :
    fullyServed (priority σ) Q' x i := by
  obtain ⟨p, hp⟩ : ∃ p, p = (σ.symm i).val := ⟨_, rfl⟩
  have hpN : p < N := hp ▸ (σ.symm i).isLt
  have hσp : σ ⟨p, hpN⟩ = i := by
    have e : (⟨p, hpN⟩ : Fin N) = σ.symm i := Fin.ext hp
    rw [e]; simp
  have hahead : ahead σ i = pre σ p := by
    ext j; simp only [ahead, pre, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, hp]
  have hsum : ∑ j ∈ pre σ (p+1), x j ≤ Q' := by
    rw [pre_succ σ p hpN, hσp, ← hahead]; exact h
  have hst := prio_iter σ Q' x (p+1) (by omega) (by
    intro m hm
    refine le_trans ?_ hsum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj; simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; omega
    · intro j _ _; exact hx j)
  unfold fullyServed
  rw [run_eq]
  have hsplit : (F (priority σ) x)^[N] (init Q') =
      (F (priority σ) x)^[N - (p+1)] ((F (priority σ) x)^[p+1] (init Q')) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
  rw [hsplit, hst]
  apply iter_full_mono
  show i ∈ (List.ofFn σ).take (p+1)
  have hlen : p < (List.ofFn σ).length := by simp; omega
  rw [← List.take_append_getElem hlen]
  apply List.mem_append_right
  simp [hσp]

/-! ### measurability of the run -/

scoped instance instMSList : MeasurableSpace (List (Fin N)) := ⊤
scoped instance instMSCList : MeasurableSingletonClass (List (Fin N)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
scoped instance instMSOpt : MeasurableSpace (Option (Fin N)) := ⊤
scoped instance instMSCOpt : MeasurableSingletonClass (Option (Fin N)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def toPair (s : RunState N) : (List (Fin N) × List (Fin N) × Bool) × ℝ :=
  ((s.chosen, s.full, s.stopped), s.rem)

def ofPair (k : List (Fin N) × List (Fin N) × Bool) (r : ℝ) : RunState N :=
  ⟨k.1, k.2.1, r, k.2.2⟩

lemma step_pair_meas (k : List (Fin N) × List (Fin N) × Bool) (c : Option (Fin N)) :
    Measurable (fun p : (Fin N → ℝ) × ℝ => toPair (step c p.1 (ofPair k p.2))) := by
  obtain ⟨l, f, b⟩ := k
  cases b
  · rcases c with _ | c
    · simp only [step, ofPair, toPair, Bool.false_eq_true, if_false]
      exact measurable_const.prodMk measurable_snd
    · by_cases hc : c ∈ l
      · simp only [step, ofPair, toPair, Bool.false_eq_true, if_false, hc, if_true]
        exact measurable_const.prodMk measurable_snd
      · have hs : MeasurableSet {p : (Fin N → ℝ) × ℝ | p.1 c ≤ p.2} :=
          measurableSet_le ((measurable_pi_apply c).comp measurable_fst) measurable_snd
        have e : (fun p : (Fin N → ℝ) × ℝ => toPair (step (some c) p.1 (ofPair (l, f, false) p.2))) =
            fun p => if p.1 c ≤ p.2 then ((l ++ [c], f ++ [c], false), p.2 - p.1 c)
              else ((l ++ [c], f, true), (0:ℝ)) := by
          funext p
          simp only [step, ofPair, toPair, Bool.false_eq_true, if_false, hc]
          by_cases hp : p.1 c ≤ p.2
          · simp [hp]
          · simp [hp]
        rw [e]
        refine Measurable.ite hs ?_ ?_
        · exact measurable_const.prodMk
            (measurable_snd.sub ((measurable_pi_apply c).comp measurable_fst))
        · exact measurable_const
  · simp only [step, ofPair, toPair, if_true]
    exact measurable_const.prodMk measurable_snd

lemma next_meas (P : AdaptivePolicy N) (l : List (Fin N)) :
    Measurable (fun x : Fin N → ℝ => P.next l x) := by
  apply measurable_to_countable'
  intro c
  exact P.measurable_next l c

lemma F_pair_meas (P : AdaptivePolicy N) :
    Measurable (fun q : ((List (Fin N) × List (Fin N) × Bool) × ((Fin N → ℝ) × ℝ)) =>
      toPair (F P q.2.1 (ofPair q.1 q.2.2))) := by
  apply measurable_from_prod_countable_right
  intro k
  have h1 : Measurable (fun q : Option (Fin N) × ((Fin N → ℝ) × ℝ) =>
      toPair (step q.1 q.2.1 (ofPair k q.2.2))) := by
    apply measurable_from_prod_countable_right
    intro c
    exact step_pair_meas k c
  have h2 : Measurable (fun p : (Fin N → ℝ) × ℝ => (P.next k.1 p.1, p)) :=
    ((next_meas P k.1).comp measurable_fst).prodMk measurable_id
  exact h1.comp h2

lemma iter_pair_meas (P : AdaptivePolicy N) (Q : ℝ) (n : ℕ) :
    Measurable (fun x : Fin N → ℝ => toPair ((F P x)^[n] (init Q))) := by
  induction n with
  | zero => show Measurable (fun _ => toPair (init Q)); exact measurable_const
  | succ n ih =>
    have e : (fun x : Fin N → ℝ => toPair ((F P x)^[n+1] (init Q))) =
        (fun q : ((List (Fin N) × List (Fin N) × Bool) × ((Fin N → ℝ) × ℝ)) =>
          toPair (F P q.2.1 (ofPair q.1 q.2.2))) ∘
        (fun x => ((toPair ((F P x)^[n] (init Q))).1, (x, (toPair ((F P x)^[n] (init Q))).2))) := by
      funext x
      simp only [Function.comp_apply, Function.iterate_succ_apply']
      rfl
    rw [e]
    exact (F_pair_meas P).comp ((measurable_fst.comp ih).prodMk
      (measurable_id.prodMk (measurable_snd.comp ih)))

lemma reached_meas (P : AdaptivePolicy N) (Q : ℝ) (k : Fin N) :
    MeasurableSet {x : Fin N → ℝ | reached P Q x k} := by
  have h := iter_pair_meas P Q N
  have : {x : Fin N → ℝ | reached P Q x k} =
      (fun x => toPair ((F P x)^[N] (init Q))) ⁻¹' {q | k ∈ q.1.1} := by
    ext x; rfl
  rw [this]
  exact h (measurable_fst (measurable_fst MeasurableSpace.measurableSet_top))

end SKRun

open SKRun

open scoped Pointwise

namespace SKGamma

lemma fill_eq_diff {N : ℕ} (σ : Equiv.Perm (Fin N)) (Q : ℝ) (hQ : 0 ≤ Q) (x : Fin N → ℝ)
    (hx : ∀ j, 0 ≤ x j) (i : Fin N) :
    fill σ Q x i = min Q (∑ j ∈ ahead σ i, x j + x i) - min Q (∑ j ∈ ahead σ i, x j) := by
  unfold fill
  have hS : 0 ≤ ∑ j ∈ ahead σ i, x j := Finset.sum_nonneg (fun j _ => hx j)
  set S := ∑ j ∈ ahead σ i, x j
  have hxi := hx i
  rcases le_total Q S with h | h
  · rw [max_eq_left (by linarith), min_eq_right hxi, min_eq_left (by linarith), min_eq_left h]
    try ring
  · rw [max_eq_right (by linarith), min_eq_right h]
    rcases le_total (x i) (Q - S) with h2 | h2
    · rw [min_eq_left h2, min_eq_right (by linarith)]; try ring
    · rw [min_eq_right h2, min_eq_left (by linarith)]; try ring

lemma ahead_sigma {N : ℕ} (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m < N) :
    ahead σ (σ ⟨m, hm⟩) = pre σ m := by
  ext j; simp [ahead, pre, Fin.lt_def]

lemma pre_zero {N : ℕ} (σ : Equiv.Perm (Fin N)) : pre σ 0 = ∅ := by
  ext j; simp [pre]

lemma abel_aux (a D : ℕ → ℝ) (n : ℕ) (hD0 : D 0 = 0) (hD : ∀ m ≤ n, 0 ≤ D m)
    (hanti : ∀ m, m + 1 < n → a (m+1) ≤ a m) :
    ∀ k, 1 ≤ k → k ≤ n → a (k-1) * D k ≤ ∑ m ∈ Finset.range k, a m * (D (m+1) - D m) := by
  intro k hk1 hkn
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hD0]
    · have ih' := ih hk (by omega)
      rw [Finset.sum_range_succ]
      have h1 : a k ≤ a (k-1) := by
        have := hanti (k-1) (by omega); rwa [Nat.sub_add_cancel hk] at this
      have h2 := hD k (by omega)
      simp only [Nat.add_sub_cancel]
      nlinarith

lemma abel_nonneg (a D : ℕ → ℝ) (n : ℕ) (hD0 : D 0 = 0) (hD : ∀ m ≤ n, 0 ≤ D m)
    (ha : ∀ m < n, 0 ≤ a m) (hanti : ∀ m, m + 1 < n → a (m+1) ≤ a m) :
    0 ≤ ∑ m ∈ Finset.range n, a m * (D (m+1) - D m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := abel_aux a D n hD0 hD hanti n hn le_rfl
    have h1 := ha (n-1) (by omega)
    have h2 := hD n le_rfl
    nlinarith

/-- coefficient sequence along `σ` -/
noncomputable def seq {N : ℕ} (σ : Equiv.Perm (Fin N)) (c : Fin N → ℝ) (m : ℕ) : ℝ :=
  if h : m < N then c (σ ⟨m, h⟩) else 0

lemma sum_eq_abel {N : ℕ} (σ : Equiv.Perm (Fin N)) (c w : Fin N → ℝ) :
    ∑ i, c i * w i = ∑ m ∈ Finset.range N,
      seq σ c m * (∑ j ∈ pre σ (m+1), w j - ∑ j ∈ pre σ m, w j) := by
  rw [← Equiv.sum_comp σ (fun i => c i * w i)]
  rw [← Fin.sum_univ_eq_sum_range (fun m => seq σ c m *
      (∑ j ∈ pre σ (m+1), w j - ∑ j ∈ pre σ m, w j)) N]
  apply Finset.sum_congr rfl
  intro m _
  rw [pre_succ σ m.val m.isLt]
  simp [seq, m.isLt]

lemma greedy_ineq {N : ℕ} (σ : Equiv.Perm (Fin N)) (c y z : Fin N → ℝ) (hc0 : ∀ i, 0 ≤ c i)
    (hanti : ∀ m (h : m + 1 < N), c (σ ⟨m+1, h⟩) ≤ c (σ ⟨m, by omega⟩))
    (hYZ : ∀ k ≤ N, ∑ j ∈ pre σ k, y j ≤ ∑ j ∈ pre σ k, z j) :
    ∑ i, c i * y i ≤ ∑ i, c i * z i := by
  rw [sum_eq_abel σ c y, sum_eq_abel σ c z, ← sub_nonneg, ← Finset.sum_sub_distrib]
  have := abel_nonneg (seq σ c) (fun k => ∑ j ∈ pre σ k, z j - ∑ j ∈ pre σ k, y j) N
    (by simp [pre_zero]) (fun m hm => by linarith [hYZ m hm])
    (fun m hm => by simp only [seq, hm, dif_pos]; exact hc0 _)
    (fun m hm => by
      simp only [seq, hm, dif_pos, show m < N by omega]
      exact hanti m hm)
  refine le_of_le_of_eq this ?_
  apply Finset.sum_congr rfl; intro m _; ring

end SKGamma

open SKGamma

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (α : Fin N → ℝ) (Q : ℝ)
    (hmeas : ∀ i, Measurable (d i)) (hint : ∀ i, Integrable (d i) μ)
    (hnn : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ d i ω) (hα : ∀ i, 0 ≤ α i) (hQ : 0 ≤ Q)
    (hΓ : InGamma μ d α Q) :
    ∃ π : Mixture (Equiv.Perm (Fin N)), ∀ i,
      α i * ∫ ω, d i ω ∂μ ≤ ∑ k, π.w k * ∫ ω, fill (π.pol k) Q (fun j => d j ω) i ∂μ := by
  have hall : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ d j ω := ae_all_iff.2 hnn
  -- the set function
  set FU : Finset (Fin N) → ℝ := fun U => ∫ ω, min Q (∑ i ∈ U, d i ω) ∂μ with hFU
  have hmin_int : ∀ U : Finset (Fin N), Integrable (fun ω => min Q (∑ i ∈ U, d i ω)) μ := by
    intro U
    refine Integrable.mono' (integrable_finsetSum U (fun i _ => hint i))
      ((measurable_const.min (Finset.measurable_sum _ (fun i _ => hmeas i))).aestronglyMeasurable) ?_
    filter_upwards [hall] with ω h
    have h0 : 0 ≤ ∑ i ∈ U, d i ω := Finset.sum_nonneg (fun i _ => h i)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hQ h0)]
    exact min_le_right _ _
  -- vertices
  set v : Equiv.Perm (Fin N) → Fin N → ℝ := fun σ i => ∫ ω, fill σ Q (fun j => d j ω) i ∂μ with hv
  have hvstep : ∀ σ : Equiv.Perm (Fin N), ∀ m (hm : m < N),
      v σ (σ ⟨m, hm⟩) = FU (pre σ (m+1)) - FU (pre σ m) := by
    intro σ m hm
    simp only [hv, hFU]
    rw [← integral_sub (hmin_int _) (hmin_int _)]
    apply integral_congr_ae
    filter_upwards [hall] with ω h
    rw [fill_eq_diff σ Q hQ _ h, ahead_sigma σ m hm, pre_succ σ m hm]
  have hvpre : ∀ σ : Equiv.Perm (Fin N), ∀ k, k ≤ N → ∑ j ∈ pre σ k, v σ j = FU (pre σ k) := by
    intro σ k hk
    induction k with
    | zero => simp [pre_zero, hFU, min_eq_right hQ]
    | succ k ih =>
      rw [pre_succ σ k (by omega), ih (by omega), hvstep σ k (by omega)]; ring
  -- target vector
  set t : Fin N → ℝ := fun i => α i * ∫ ω, d i ω ∂μ with ht
  -- the dominated hull
  set L : (Equiv.Perm (Fin N) → ℝ) → (Fin N → ℝ) := fun W => ∑ σ, W σ • v σ with hL
  set K : Set (Fin N → ℝ) := L '' stdSimplex ℝ (Equiv.Perm (Fin N)) with hK
  set D : Set (Fin N → ℝ) := K + Set.Iic (0 : Fin N → ℝ) with hD
  have hLlin : IsLinearMap ℝ L := by
    constructor
    · intro W W'; simp only [hL, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · intro r W; simp only [hL, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hLcont : Continuous L := by
    simp only [hL]
    exact continuous_finsetSum _ (fun σ _ => (continuous_apply σ).smul continuous_const)
  have hKc : IsCompact K := (isCompact_stdSimplex ℝ (Equiv.Perm (Fin N))).image hLcont
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ _).is_linear_image hLlin
  have hDconv : Convex ℝ D := hKconv.add (convex_Iic 0)
  have hDclosed : IsClosed D := isClosed_Iic.add_left_of_isCompact hKc
  have hmemD : ∀ z, z ∈ D ↔ ∃ k ∈ K, z ≤ k := by
    intro z
    constructor
    · rintro ⟨k, hk, n, hn, rfl⟩
      exact ⟨k, hk, by have : n ≤ 0 := hn; intro i; have := this i; simp at this ⊢; linarith⟩
    · rintro ⟨k, hk, hz⟩
      exact ⟨k, hk, z - k, by intro i; simp; linarith [hz i], by abel⟩
  have hvK : ∀ σ, v σ ∈ K := by
    intro σ
    refine ⟨fun τ => if τ = σ then 1 else 0, ⟨fun τ => by dsimp only; split_ifs <;> norm_num, by simp⟩, ?_⟩
    simp [hL]
  have htD : t ∈ D := by
    by_contra hnot
    obtain ⟨f, u, hfD, hut⟩ := geometric_hahn_banach_closed_point hDconv hDclosed hnot
    set c : Fin N → ℝ := fun i => f (Pi.single i 1) with hc
    have hf : ∀ z, f z = ∑ i, c i * z i := by
      intro z
      conv_lhs => rw [← Finset.univ_sum_single z]
      rw [map_sum]
      apply Finset.sum_congr rfl; intro i _
      have : Pi.single i (z i) = z i • (Pi.single i (1:ℝ) : Fin N → ℝ) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]
      rw [this, map_smul, smul_eq_mul, hc]; ring
    -- c ≥ 0
    have hc0 : ∀ i, 0 ≤ c i := by
      intro i
      by_contra hneg; push_neg at hneg
      obtain ⟨σ0⟩ : Nonempty (Equiv.Perm (Fin N)) := ⟨1⟩
      set a := v σ0
      set s : ℝ := (u - f a) / (-c i) + 1
      have hmem : a - s • (Pi.single i (1:ℝ) : Fin N → ℝ) ∈ D := by
        rw [hmemD]
        refine ⟨a, hvK σ0, ?_⟩
        have hs : 0 ≤ s := by
          have : f a < u := hfD a ((hmemD a).2 ⟨a, hvK σ0, le_rfl⟩)
          have : 0 < (u - f a) / (-c i) := div_pos (by linarith) (by linarith)
          simp only [s]; linarith
        intro j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hj : j = i
        · subst hj; simp; linarith
        · simp [hj]
      have h1 := hfD _ hmem
      rw [map_sub, map_smul, smul_eq_mul] at h1
      have h2 : f (Pi.single i 1) = c i := rfl
      rw [h2] at h1
      have : s * (-c i) = (u - f a) + (-c i) := by
        simp only [s]; rw [add_mul, div_mul_cancel₀ _ (by linarith : (-c i) ≠ 0)]; ring
      linarith
    -- sort by decreasing c
    set σ := Tuple.sort (fun i => -c i) with hσ
    have hmono := Tuple.monotone_sort (fun i => -c i)
    have hanti : ∀ m (h : m + 1 < N), c (σ ⟨m+1, h⟩) ≤ c (σ ⟨m, by omega⟩) := by
      intro m h
      have := hmono (show (⟨m, by omega⟩ : Fin N) ≤ ⟨m+1, h⟩ from by
        rw [Fin.mk_le_mk]; omega)
      simp only [Function.comp_apply] at this
      linarith
    have hYZ : ∀ k ≤ N, ∑ j ∈ pre σ k, t j ≤ ∑ j ∈ pre σ k, v σ j := by
      intro k hk
      rw [hvpre σ k hk]
      have := hΓ (pre σ k)
      simpa [ht, hFU] using this
    have hg := greedy_ineq σ c t (v σ) hc0 hanti hYZ
    have hvD : v σ ∈ D := (hmemD _).2 ⟨v σ, hvK σ, le_rfl⟩
    have h1 := hfD _ hvD
    have e1 := hf t
    have e2 := hf (v σ)
    linarith
  -- extract the mixture
  obtain ⟨k, ⟨W, hW, rfl⟩, htk⟩ := (hmemD t).1 htD
  set e := Fintype.equivFin (Equiv.Perm (Fin N))
  refine ⟨⟨Fintype.card (Equiv.Perm (Fin N)), fun j => W (e.symm j), fun j => e.symm j,
    fun j => hW.1 _, ?_⟩, ?_⟩
  · rw [Equiv.sum_comp e.symm W]; exact hW.2
  · intro i
    have := htk i
    simp only [hL, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    refine le_trans this (le_of_eq ?_)
    rw [← Equiv.sum_comp e.symm (fun σ => W σ * v σ i)]
