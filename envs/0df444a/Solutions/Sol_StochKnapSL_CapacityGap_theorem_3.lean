-- Prove2me | solution 1 for StochKnapSL.CapacityGap.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:00:32.724173+00:00
-- url     : https://prove2.me/submissions/3b428082-da43-4db0-91c5-1f0ffb326687

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
import Theorems.Thm_StochKnapSL_CapacityGap_gamma_achievable
import Theorems.Thm_StochKnapSL_CapacityGap_fill_ratio_le_prob
import Theorems.Thm_StochKnapSL_CapacityGap_greedy_fill_structure
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

namespace SKRun

lemma real_eq_one_of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Set Ω} (h : ∀ᵐ ω ∂μ, ω ∈ s) : μ.real s = 1 := by
  have h0 : μ sᶜ = 0 := ae_iff.1 h
  have : μ s = μ Set.univ := measure_congr (ae_eq_univ.2 h0)
  simp [Measure.real, this]

lemma good_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ} {d : Fin N → Ω → ℝ}
    {Δ : ℝ} {α : Fin N → ℝ} (hS : Standing μ d Δ α) :
    ∀ᵐ ω ∂μ, ∀ j, 0 < d j ω ∧ d j ω ≤ Δ := by
  rw [ae_all_iff]; intro j
  filter_upwards [hS.pos j, hS.bdd j] with ω h1 h2 using ⟨h1, h2⟩

/-- the single-policy mixture -/
def single {P : Type*} (p : P) : Mixture P where
  m := 1
  w := fun _ => 1
  pol := fun _ => p
  w_nonneg := fun _ => zero_le_one
  w_sum := by simp

lemma serviceProb_single {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (d : Fin N → Ω → ℝ) (p : AdaptivePolicy N) (Q : ℝ) (i : Fin N) :
    serviceProb μ d (single p) Q i = μ.real {ω | fullyServed p Q (fun j => d j ω) i} := by
  unfold serviceProb
  show ∑ _k : Fin 1, (1:ℝ) * μ.real {ω | fullyServed p Q (fun j => d j ω) i} = _
  simp

/-- the priority policy serves everybody with capacity `N Δ` -/
lemma prio_all {N : ℕ} (σ : Equiv.Perm (Fin N)) (Δ : ℝ) (x : Fin N → ℝ)
    (hx : ∀ j, 0 < x j ∧ x j ≤ Δ) (i : Fin N) : fullyServed (priority σ) (N * Δ) x i := by
  apply prio_full σ _ x (fun j => (hx j).1.le)
  have hni : i ∉ ahead σ i := by simp [ahead]
  calc ∑ j ∈ ahead σ i, x j + x i = ∑ j ∈ insert i (ahead σ i), x j := by
        rw [Finset.sum_insert hni, add_comm]
    _ ≤ ∑ j, x j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => (hx j).1.le)
    _ ≤ ∑ _j : Fin N, Δ := Finset.sum_le_sum (fun j _ => (hx j).2)
    _ = N * Δ := by simp

lemma prio_all_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ) (hS : Standing μ d Δ α)
    (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    μ.real {ω | fullyServed (priority σ) (N * Δ) (fun j => d j ω) i} = 1 := by
  apply real_eq_one_of_ae
  filter_upwards [good_ae hS] with ω h
  exact prio_all σ Δ _ h i

lemma adapFeasible_NΔ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ) (hS : Standing μ d Δ α) :
    AdapFeasible μ d α (N * Δ) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hS.Δ_pos.le, single (priority (Equiv.refl _)), ?_⟩
  intro i
  rw [serviceProb_single, prio_all_prob μ d Δ α hS]
  exact (hS.α_mem i).2

end SKRun

namespace SKRun

lemma int_d {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    {d : Fin N → Ω → ℝ} {Δ : ℝ} {α : Fin N → ℝ} (hS : Standing μ d Δ α) (k : Fin N) :
    Integrable (d k) μ := by
  refine Integrable.of_bound (C := Δ) (hS.meas k).aestronglyMeasurable ?_
  filter_upwards [hS.pos k, hS.bdd k] with ω h1 h2
  rw [Real.norm_eq_abs, abs_of_pos h1]; exact h2

lemma Ed_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    {d : Fin N → Ω → ℝ} {Δ : ℝ} {α : Fin N → ℝ} (hS : Standing μ d Δ α) (k : Fin N) :
    0 < ∫ ω, d k ω ∂μ := by
  have hnn : 0 ≤ᵐ[μ] d k := by filter_upwards [hS.pos k] with ω h; exact h.le
  rcases (integral_nonneg_of_ae hnn).eq_or_lt with h | h
  · exfalso
    have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn (int_d hS k)).1 h.symm
    have hf : ∀ᵐ ω ∂μ, False := by
      filter_upwards [h0, hS.pos k] with ω h1 h2
      simp only [Pi.zero_apply] at h1; linarith
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hf
    exact IsProbabilityMeasure.ne_zero μ hf
  · exact h

lemma inGamma_NΔ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ) (hS : Standing μ d Δ α) :
    InGamma μ d α (N * Δ) := by
  intro U
  have hae : (fun ω => min ((N : ℝ) * Δ) (∑ i ∈ U, d i ω)) =ᵐ[μ] (fun ω => ∑ i ∈ U, d i ω) := by
    filter_upwards [good_ae hS] with ω h
    apply min_eq_right
    calc ∑ i ∈ U, d i ω ≤ ∑ i, d i ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => (h j).1.le)
      _ ≤ ∑ _i : Fin N, Δ := Finset.sum_le_sum (fun j _ => (h j).2)
      _ = N * Δ := by simp
  rw [integral_congr_ae hae, integral_finsetSum _ (fun i _ => int_d hS i)]
  apply Finset.sum_le_sum
  intro i _
  have h1 := (hS.α_mem i).2
  have h2 := (Ed_pos hS i).le
  nlinarith

end SKRun

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ)
    (hS : Standing μ d Δ α) :
    QAnti μ d α ≤ QII μ d α + Δ := by
  have hne : ({Q | 0 ≤ Q ∧ InGamma μ d α Q} : Set ℝ).Nonempty :=
    ⟨_, mul_nonneg (Nat.cast_nonneg _) hS.Δ_pos.le, inGamma_NΔ μ d Δ α hS⟩
  have hbdd : BddBelow ({Q | AntiFeasible μ d α Q} : Set ℝ) := ⟨0, fun q hq => hq.1⟩
  suffices h : QAnti μ d α - Δ ≤ QII μ d α by linarith
  unfold QII
  apply le_csInf hne
  rintro Q ⟨hQ0, hΓ⟩
  suffices hF : AntiFeasible μ d α (Q + Δ) by
    have := csInf_le hbdd hF
    unfold QAnti; linarith
  obtain ⟨π, hπ⟩ := gamma_achievable μ d α Q hS.meas (fun i => int_d hS i)
    (fun i => by filter_upwards [hS.pos i] with ω h; exact h.le) (fun i => (hS.α_mem i).1) hQ0 hΓ
  refine ⟨by linarith [hS.Δ_pos], π, ?_⟩
  intro i
  have hE := Ed_pos hS i
  -- α_i ≤ Σ w_k E[fill_k]/E[d_i]
  have h1 : α i ≤ ∑ k, π.w k * ((∫ ω, fill (π.pol k) Q (fun j => d j ω) i ∂μ) /
      (∫ ω, d i ω ∂μ)) := by
    have := hπ i
    rw [← le_div_iff₀ hE] at this
    refine le_trans this (le_of_eq ?_)
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro k _; ring
  refine le_trans h1 ?_
  show _ ≤ ∑ k, π.w k * μ.real {ω | fullyServed (priority (π.pol k)) (Q + Δ) (fun j => d j ω) i}
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (π.w_nonneg k)
  refine le_trans (fill_ratio_le_prob μ d Δ α hS (π.pol k) Q hQ0 i) ?_
  -- {fill > 0} ⊆ {fully served} a.e.
  have H : {ω | 0 < fill (π.pol k) Q (fun j => d j ω) i} ≤ᵐ[μ]
      {ω | fullyServed (priority (π.pol k)) (Q + Δ) (fun j => d j ω) i} := by
    filter_upwards [good_ae hS] with ω h hω
    have hpos := ((greedy_fill_structure (π.pol k) Q (fun j => d j ω) (fun j => (h j).1.le)
      hQ0).2 i (h i).1).1 hω
    apply prio_full _ _ _ (fun j => (h j).1.le)
    linarith [(h i).2]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae H)
