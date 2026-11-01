-- Prove2me | solution 1 for StochasticRewardMatching.Decomposable.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-01T02:04:13.565625+00:00
-- url     : https://prove2.me/submissions/b33478d9-8684-462c-bdcd-ad1106792ff2

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Dual

open scoped BigOperators
open MeasureTheory
open Filter
open StochasticRewardMatching.Decomposable

noncomputable section

namespace Lemma3

variable {n m : ℕ}

/-! ## Part 0: elementary facts about `g`, the reward bound and the seed cube -/

lemma continuous_g : Continuous g := by
  unfold g
  fun_prop

lemma measurable_g_eval {n : ℕ} (i : Fin n) : Measurable (fun Y : Seeds n => g (Y i)) :=
  (continuous_g.comp (continuous_apply i)).measurable

lemma g_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : g x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · unfold g
    exact le_of_lt (Real.exp_pos _)
  · unfold g
    calc Real.exp (x - 1) ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith [hx.2])
      _ = 1 := Real.exp_zero

/-! ## Part 1: the pointwise combinatorial identity (per `Y`, per `ω`) -/

/-- Contribution of a single history entry `z` to `lambdaPath · t`. -/
def lamEntry {n m : ℕ} (D : Instance n m) (Y : Seeds n) (t : Fin m) (z : Action n m × Bool) : ℝ :=
  if z.1.1 = t ∧ z.2 = true then
    (match z.1.2 with | none => 0 | some i => D.reward i * (1 - g (Y i)))
  else 0

/-- Contribution of a single history entry `z` to `thetaPath · i`. -/
def thetaEntry {n m : ℕ} (D : Instance n m) (Y : Seeds n) (i : Fin n) (z : Action n m × Bool) : ℝ :=
  if z.1.2 = some i ∧ z.2 = true then D.reward i * g (Y i) else 0

/-- Contribution of a single history entry `z` to `algorithmReward`. -/
def rewardEntry {n m : ℕ} (D : Instance n m) (z : Action n m × Bool) : ℝ :=
  if z.2 then actionReward D z.1 else 0

/-- Per-entry identity: the two path contributions of one history entry sum to its reward. -/
lemma entry_identity {n m : ℕ} (D : Instance n m) (Y : Seeds n) (z : Action n m × Bool) :
    (∑ t : Fin m, lamEntry D Y t z) + (∑ i : Fin n, thetaEntry D Y i z) =
      rewardEntry D z := by
  obtain ⟨⟨tm, res⟩, b⟩ := z
  unfold lamEntry thetaEntry rewardEntry
  cases b with
  | false => simp
  | true =>
    cases res with
    | none => simp [actionReward]
    | some j =>
      simp only [actionReward, and_true, Option.some.injEq]
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
      simp
      ring

/-- The pointwise identity for an arbitrary list of history entries. -/
lemma list_identity {n m : ℕ} (D : Instance n m) (Y : Seeds n) (h : History n m) :
    (∑ t : Fin m, (h.map (lamEntry D Y t)).sum) +
      (∑ i : Fin n, (h.map (thetaEntry D Y i)).sum) =
        (h.map (rewardEntry D)).sum := by
  induction h with
  | nil => simp
  | cons z h ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hz := entry_identity D Y z
    linear_combination ih + hz

/-- Pointwise identity in terms of the platform definitions. -/
theorem pointwise_identity {n m : ℕ} (D : Instance n m) (ω : Outcome D) (Y : Seeds n) :
    (∑ t : Fin m, lambdaPath D ω Y t) + (∑ i : Fin n, thetaPath D ω Y i) =
      algorithmReward D Y ω := by
  unfold lambdaPath thetaPath algorithmReward
  exact list_identity D Y (algorithmHistory D Y ω)

/-! ## Part 2: measurability -/

lemma continuous_score {n m : ℕ} (D : Instance n m) (t : Fin m) (i : Fin n) :
    Continuous (fun Y : Seeds n => score D Y t i) := by
  unfold score
  have hg : Continuous (fun Y : Seeds n => g (Y i)) :=
    continuous_g.comp (continuous_apply i)
  exact (continuous_const.mul continuous_const).mul (continuous_const.sub hg)

/-- Splitting an `ite` whose value is compared to a constant. -/
lemma ite_some_eq_iff {α : Type*} {p : Prop} [Decidable p] {x y z : Option α} :
    (if p then x else y) = z ↔ (p ∧ x = z) ∨ (¬p ∧ y = z) := by
  by_cases hp : p <;> simp [hp]

lemma measurable_lamEntry {n m : ℕ} (D : Instance n m) (t : Fin m)
    (z : Action n m × Bool) :
    Measurable (fun Y : Seeds n => lamEntry D Y t z) := by
  obtain ⟨⟨tm, res⟩, b⟩ := z
  unfold lamEntry
  show Measurable (fun Y : Seeds n =>
    if tm = t ∧ b = true then
      (match res with | none => (0 : ℝ) | some i => D.reward i * (1 - g (Y i)))
    else 0)
  split_ifs with h
  · cases res with
    | none => exact measurable_const
    | some i => exact measurable_const.mul (measurable_const.sub (measurable_g_eval i))
  · exact measurable_const

lemma measurable_thetaEntry {n m : ℕ} (D : Instance n m) (i : Fin n)
    (z : Action n m × Bool) :
    Measurable (fun Y : Seeds n => thetaEntry D Y i z) := by
  obtain ⟨⟨tm, res⟩, b⟩ := z
  unfold thetaEntry
  show Measurable (fun Y : Seeds n =>
    if res = some i ∧ b = true then D.reward i * g (Y i) else 0)
  split_ifs with h
  · exact measurable_const.mul (measurable_g_eval i)
  · exact measurable_const

lemma measurable_rewardEntry {n m : ℕ} (D : Instance n m) (z : Action n m × Bool) :
    Measurable (fun _ : Seeds n => rewardEntry D z) := by
  obtain ⟨⟨tm, res⟩, b⟩ := z
  unfold rewardEntry
  show Measurable (fun _ : Seeds n => if b then actionReward D (tm, res) else 0)
  exact measurable_const

/-- Fibres of `bestOf` applied to a list of continuously scored candidates. -/
lemma measurableSet_bestOf {n m : ℕ} (D : Instance n m) (t : Fin m) :
    ∀ (L : List (Fin n)) (c : Option (Fin n)),
      MeasurableSet {Y : Seeds n | bestOf (score D Y t) L = c} := by
  intro L
  induction L with
  | nil =>
    intro c
    cases c with
    | none => simp [bestOf]
    | some j =>
      have h : {Y : Seeds n | bestOf (score D Y t) [] = some j} = ∅ := by
        ext Y
        simp [bestOf]
      rw [h]
      exact MeasurableSet.empty
  | cons a rest ih =>
    intro c
    cases c with
    | none =>
      have h : {Y : Seeds n | bestOf (score D Y t) (a :: rest) = none} = ∅ := by
        ext Y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        cases hb : bestOf (score D Y t) rest with
        | none => simp [bestOf, hb]
        | some b =>
          rw [show bestOf (score D Y t) (a :: rest) =
              (if score D Y t b ≤ score D Y t a then some a else some b) by
            simp only [bestOf, hb]]
          split_ifs <;> simp
      rw [h]
      exact MeasurableSet.empty
    | some j =>
      have hset : {Y : Seeds n | bestOf (score D Y t) (a :: rest) = some j} =
          ({Y : Seeds n | bestOf (score D Y t) rest = none} ∩
            {Y : Seeds n | some a = some j}) ∪
          ⋃ b : Fin n, ({Y : Seeds n | bestOf (score D Y t) rest = some b} ∩
            (({Y : Seeds n | score D Y t b ≤ score D Y t a} ∩
                {Y : Seeds n | some a = some j}) ∪
             ({Y : Seeds n | ¬ score D Y t b ≤ score D Y t a} ∩
                {Y : Seeds n | some b = some j}))) := by
        ext Y
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
        cases hb : bestOf (score D Y t) rest with
        | none => simp [bestOf, hb]
        | some b =>
          rw [show bestOf (score D Y t) (a :: rest) =
              (if score D Y t b ≤ score D Y t a then some a else some b) by
            simp only [bestOf, hb]]
          rw [ite_some_eq_iff]
          simp
      rw [hset]
      refine MeasurableSet.union ?_ ?_
      · refine (ih none).inter ?_
        by_cases hc : some a = some j
        · simp [hc]
        · simp [hc]
      · refine MeasurableSet.iUnion fun b => (ih (some b)).inter ?_
        refine MeasurableSet.union ?_ ?_
        · refine MeasurableSet.inter ?_ ?_
          · exact measurableSet_le (continuous_score D t b).measurable
              (continuous_score D t a).measurable
          · by_cases hc : some a = some j
            · simp [hc]
            · simp [hc]
        · refine MeasurableSet.inter ?_ ?_
          · have hlt : MeasurableSet {Y : Seeds n | ¬ score D Y t b ≤ score D Y t a} := by
              have h := measurableSet_lt (continuous_score D t a).measurable
                (continuous_score D t b).measurable
              simpa [not_le] using h
            exact hlt
          · by_cases hc : some b = some j
            · simp [hc]
            · simp [hc]

/-- Measurability of the fibre of `algorithmChoice`. -/
lemma measurableSet_algorithmChoice {n m : ℕ} (D : Instance n m) (S : Finset (Fin n)) (t : Fin m)
    (j : Option (Fin n)) :
    MeasurableSet {Y : Seeds n | algorithmChoice D Y S t = j} := by
  unfold algorithmChoice
  exact measurableSet_bestOf D t ((neighbors D S t).sort (· ≤ ·)) j

/-- State of the algorithm run: remaining resources together with the history so far. -/
abbrev RunState (n m : ℕ) := Finset (Fin n) × History n m

/-- One step of history extension, with the resource choice supplied externally. -/
def nextState {n m : ℕ} (D : Instance n m) (ω : Outcome D) (k : ℕ) (hk : k < m)
    (st : RunState n m) (j : Option (Fin n)) : RunState n m :=
  let a : Action n m := (⟨k, hk⟩, j)
  let b := actionBit D ω a
  (if b then afterSuccess st.1 a else st.1, st.2 ++ [(a, b)])

/-- One unfolding step of `algorithmRun`. -/
theorem algorithmRun_succ {n m : ℕ} (D : Instance n m) (ω : Outcome D)
    (init : Finset (Fin n)) (Y : Seeds n) (k : ℕ) :
    algorithmRun D Y ω init (k + 1) =
      if hk : k < m then
        nextState D ω k hk (algorithmRun D Y ω init k)
          (algorithmChoice D Y (algorithmRun D Y ω init k).1 ⟨k, hk⟩)
      else algorithmRun D Y ω init k := rfl

/-- Fibres of the algorithm run are measurable. -/
theorem measurableSet_algorithmRun {n m : ℕ} (D : Instance n m) (ω : Outcome D)
    (init : Finset (Fin n)) :
    ∀ (k : ℕ) (st : RunState n m),
      MeasurableSet {Y : Seeds n | algorithmRun D Y ω init k = st} := by
  intro k
  induction k with
  | zero =>
    intro st
    by_cases h : ((init, ([] : History n m)) : RunState n m) = st
    · subst h
      have hz : {Y : Seeds n | algorithmRun D Y ω init 0 = (init, [])} = Set.univ := by
        ext Y
        simp [algorithmRun]
      rw [hz]
      exact MeasurableSet.univ
    · have hz : {Y : Seeds n | algorithmRun D Y ω init 0 = st} = ∅ := by
        ext Y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hY
        exact h (by simpa [algorithmRun] using hY)
      rw [hz]
      exact MeasurableSet.empty
  | succ k ih =>
    intro st
    by_cases hk : k < m
    · have hset : {Y : Seeds n | algorithmRun D Y ω init (k + 1) = st} =
          ⋃ p : RunState n m × Option (Fin n),
            ({Y : Seeds n | algorithmRun D Y ω init k = p.1} ∩
             ({Y : Seeds n | algorithmChoice D Y p.1.1 ⟨k, hk⟩ = p.2} ∩
              {Y : Seeds n | nextState D ω k hk p.1 p.2 = st})) := by
        ext Y
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hY
          refine ⟨(algorithmRun D Y ω init k,
            algorithmChoice D Y (algorithmRun D Y ω init k).1 ⟨k, hk⟩), rfl, rfl, ?_⟩
          rw [algorithmRun_succ] at hY
          rw [dif_pos hk] at hY
          exact hY
        · rintro ⟨p, hrun, hchoice, hnext⟩
          rw [algorithmRun_succ]
          rw [dif_pos hk]
          rw [hrun, hchoice]
          exact hnext
      rw [hset]
      refine MeasurableSet.iUnion fun p => ?_
      refine (ih p.1).inter ((measurableSet_algorithmChoice D p.1.1 ⟨k, hk⟩ p.2).inter ?_)
      by_cases hst : nextState D ω k hk p.1 p.2 = st
      · have hz : {Y : Seeds n | nextState D ω k hk p.1 p.2 = st} = Set.univ := by
          ext Y
          simp [hst]
        rw [hz]
        exact MeasurableSet.univ
      · have hz : {Y : Seeds n | nextState D ω k hk p.1 p.2 = st} = ∅ := by
          ext Y
          simp [hst]
        rw [hz]
        exact MeasurableSet.empty
    · have hset : {Y : Seeds n | algorithmRun D Y ω init (k + 1) = st} =
          {Y : Seeds n | algorithmRun D Y ω init k = st} := by
        ext Y
        simp only [Set.mem_ofPred_eq]
        rw [algorithmRun_succ]
        rw [dif_neg hk]
      rw [hset]
      exact ih st

/-- Fibres of the full algorithm history are measurable. -/
theorem measurableSet_algorithmHistory {n m : ℕ} (D : Instance n m) (ω : Outcome D)
    (h : History n m) :
    MeasurableSet {Y : Seeds n | algorithmHistory D Y ω = h} := by
  unfold algorithmHistory
  have hset : {Y : Seeds n | (algorithmRun D Y ω Finset.univ m).2 = h} =
      ⋃ st : RunState n m,
        ({Y : Seeds n | algorithmRun D Y ω Finset.univ m = st} ∩
         {Y : Seeds n | st.2 = h}) := by
    ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hY
      exact ⟨algorithmRun D Y ω Finset.univ m, rfl, hY⟩
    · rintro ⟨st, hrun, hst⟩
      rw [hrun]
      exact hst
  rw [hset]
  refine MeasurableSet.iUnion fun st => (measurableSet_algorithmRun D ω Finset.univ m st).inter ?_
  by_cases hst : st.2 = h
  · have hz : {Y : Seeds n | st.2 = h} = Set.univ := by
      ext Y
      simp [hst]
    rw [hz]
    exact MeasurableSet.univ
  · have hz : {Y : Seeds n | st.2 = h} = ∅ := by
      ext Y
      simp [hst]
    rw [hz]
    exact MeasurableSet.empty

/-- A function of a countably-valued measurable "path" is measurable. -/
lemma measurable_fiber_apply {β γ : Type*} [MeasurableSpace γ] [Countable β]
    {f : Seeds n → β} (hf : ∀ b, MeasurableSet (f ⁻¹' {b})) {G : β → Seeds n → γ}
    (hG : ∀ b, Measurable (G b)) :
    Measurable (fun Y => G (f Y) Y) := by
  intro s hs
  have hset : (fun Y => G (f Y) Y) ⁻¹' s = ⋃ b, (f ⁻¹' {b} ∩ (G b) ⁻¹' s) := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro hY
      exact ⟨f Y, rfl, hY⟩
    · rintro ⟨b, hb, hY⟩
      rwa [hb]
  rw [hset]
  exact MeasurableSet.iUnion fun b => (hf b).inter (hG b hs)

/-- A finite sum of a fixed list of measurable functions is measurable. -/
lemma measurable_listSum {α : Type*} {n : ℕ} (h : List α) (F : α → Seeds n → ℝ)
    (hF : ∀ z, Measurable (F z)) :
    Measurable (fun Y : Seeds n => (h.map (fun z => F z Y)).sum) := by
  induction h with
  | nil => simp
  | cons z rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF z).add ih

lemma measurable_lambdaPath {n m : ℕ} (D : Instance n m) (ω : Outcome D) (t : Fin m) :
    Measurable (fun Y : Seeds n => lambdaPath D ω Y t) := by
  have key := measurable_fiber_apply
    (f := fun Y : Seeds n => algorithmHistory D Y ω)
    (hf := fun h => measurableSet_algorithmHistory D ω h)
    (G := fun h Y => (h.map (fun z => lamEntry D Y t z)).sum)
    (hG := fun h => measurable_listSum h (fun z Y => lamEntry D Y t z)
      (fun z => measurable_lamEntry D t z))
  have hfun : (fun Y : Seeds n => lambdaPath D ω Y t) =
      fun Y => ((algorithmHistory D Y ω).map (fun z => lamEntry D Y t z)).sum := by
    funext Y
    rfl
  rw [hfun]
  exact key

lemma measurable_thetaPath {n m : ℕ} (D : Instance n m) (ω : Outcome D) (i : Fin n) :
    Measurable (fun Y : Seeds n => thetaPath D ω Y i) := by
  have key := measurable_fiber_apply
    (f := fun Y : Seeds n => algorithmHistory D Y ω)
    (hf := fun h => measurableSet_algorithmHistory D ω h)
    (G := fun h Y => (h.map (fun z => thetaEntry D Y i z)).sum)
    (hG := fun h => measurable_listSum h (fun z Y => thetaEntry D Y i z)
      (fun z => measurable_thetaEntry D i z))
  have hfun : (fun Y : Seeds n => thetaPath D ω Y i) =
      fun Y => ((algorithmHistory D Y ω).map (fun z => thetaEntry D Y i z)).sum := by
    funext Y
    rfl
  rw [hfun]
  exact key

lemma measurable_algorithmReward {n m : ℕ} (D : Instance n m) (ω : Outcome D) :
    Measurable (fun Y : Seeds n => algorithmReward D Y ω) := by
  have key := measurable_fiber_apply
    (f := fun Y : Seeds n => algorithmHistory D Y ω)
    (hf := fun h => measurableSet_algorithmHistory D ω h)
    (G := fun h Y => (h.map (fun z => rewardEntry D z)).sum)
    (hG := fun h => measurable_listSum h (fun z _ => rewardEntry D z)
      (fun z => measurable_rewardEntry D z))
  have hfun : (fun Y : Seeds n => algorithmReward D Y ω) =
      fun Y => ((algorithmHistory D Y ω).map (fun z => rewardEntry D z)).sum := by
    funext Y
    rfl
  rw [hfun]
  exact key

/-! ## Part 3: lengths, bounds and integrability -/

/-- The history produced after `k` steps has length `min k m`. -/
theorem algorithmRun_length {n m : ℕ} (D : Instance n m) (ω : Outcome D) (Y : Seeds n)
    (init : Finset (Fin n)) (k : ℕ) :
    (algorithmRun D Y ω init k).2.length = min k m := by
  induction k with
  | zero => simp [algorithmRun]
  | succ k ih =>
    rw [algorithmRun_succ]
    by_cases hk : k < m
    · rw [dif_pos hk]
      simp only [nextState, List.length_append, List.length_cons, List.length_nil]
      rw [ih]
      have h1 : min k m = k := Nat.min_eq_left (le_of_lt hk)
      have h2 : min (k + 1) m = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hk)
      rw [h1, h2]
    · rw [dif_neg hk]
      rw [ih]
      have hle : m ≤ k := by omega
      have h1 : min k m = m := Nat.min_eq_right hle
      have h2 : min (k + 1) m = m := Nat.min_eq_right (le_trans hle (Nat.le_succ k))
      rw [h1, h2]

/-- The algorithm history has length exactly `m`. -/
theorem algorithmHistory_length {n m : ℕ} (D : Instance n m) (ω : Outcome D) (Y : Seeds n) :
    (algorithmHistory D Y ω).length = m := by
  unfold algorithmHistory
  rw [algorithmRun_length]
  simp

lemma ae_mem_cube (n : ℕ) :
    ∀ᵐ Y ∂seedLaw n, ∀ i : Fin n, Y i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [eventually_all]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Icc)

lemma list_sum_nonneg {α : Type*} (l : List α) (F : α → ℝ) (hF : ∀ z, 0 ≤ F z) :
    0 ≤ (l.map F).sum := by
  induction l with
  | nil => simp
  | cons z rest ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [hF z]

lemma list_sum_le_length_mul {α : Type*} (l : List α) (F : α → ℝ) (R : ℝ)
    (hF : ∀ z, F z ≤ R) : (l.map F).sum ≤ (l.length : ℝ) * R := by
  induction l with
  | nil => simp
  | cons z rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [hF z]

/-- A bound on the total reward. -/
def rewardBound {n m : ℕ} (D : Instance n m) : ℝ := ∑ i : Fin n, D.reward i

lemma rewardBound_nonneg {n m : ℕ} (D : Instance n m) : 0 ≤ rewardBound D :=
  Finset.sum_nonneg fun i _ => D.reward_nonneg i

lemma reward_le_rewardBound {n m : ℕ} (D : Instance n m) (i : Fin n) :
    D.reward i ≤ rewardBound D :=
  Finset.single_le_sum (f := D.reward) (fun j _ => D.reward_nonneg j) (Finset.mem_univ i)

lemma lamEntry_bounds {n m : ℕ} (D : Instance n m) (Y : Seeds n)
    (hY : ∀ i, Y i ∈ Set.Icc (0 : ℝ) 1) (t : Fin m) (z : Action n m × Bool) :
    0 ≤ lamEntry D Y t z ∧ lamEntry D Y t z ≤ rewardBound D := by
  unfold lamEntry
  split_ifs with h
  · cases hres : z.1.2 with
    | none => exact ⟨le_rfl, rewardBound_nonneg D⟩
    | some i =>
      have hg := g_mem (hY i)
      constructor
      · exact mul_nonneg (D.reward_nonneg i) (sub_nonneg.2 hg.2)
      · refine le_trans ?_ (reward_le_rewardBound D i)
        exact mul_le_of_le_one_right (D.reward_nonneg i) (by linarith [hg.1])
  · exact ⟨le_rfl, rewardBound_nonneg D⟩

lemma thetaEntry_bounds {n m : ℕ} (D : Instance n m) (Y : Seeds n)
    (hY : ∀ i, Y i ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) (z : Action n m × Bool) :
    0 ≤ thetaEntry D Y i z ∧ thetaEntry D Y i z ≤ rewardBound D := by
  unfold thetaEntry
  split_ifs with h
  · have hg := g_mem (hY i)
    constructor
    · exact mul_nonneg (D.reward_nonneg i) hg.1
    · refine le_trans ?_ (reward_le_rewardBound D i)
      exact mul_le_of_le_one_right (D.reward_nonneg i) hg.2
  · exact ⟨le_rfl, rewardBound_nonneg D⟩

lemma rewardEntry_bounds {n m : ℕ} (D : Instance n m) (z : Action n m × Bool) :
    0 ≤ rewardEntry D z ∧ rewardEntry D z ≤ rewardBound D := by
  obtain ⟨⟨tm, res⟩, b⟩ := z
  unfold rewardEntry
  cases b with
  | false => exact ⟨le_rfl, rewardBound_nonneg D⟩
  | true =>
    cases res with
    | none => exact ⟨le_rfl, rewardBound_nonneg D⟩
    | some i =>
      simp only [actionReward]
      exact ⟨D.reward_nonneg i, reward_le_rewardBound D i⟩

lemma lambdaPath_bounds {n m : ℕ} (D : Instance n m) (ω : Outcome D) (Y : Seeds n)
    (hY : ∀ i, Y i ∈ Set.Icc (0 : ℝ) 1) (t : Fin m) :
    0 ≤ lambdaPath D ω Y t ∧ lambdaPath D ω Y t ≤ (m : ℝ) * rewardBound D := by
  unfold lambdaPath
  have hlen : (algorithmHistory D Y ω).length = m := algorithmHistory_length D ω Y
  constructor
  · exact list_sum_nonneg _ _ (fun z => (lamEntry_bounds D Y hY t z).1)
  · have h := list_sum_le_length_mul (algorithmHistory D Y ω)
      (fun z => if z.1.1 = t ∧ z.2 = true then
        (match z.1.2 with | none => (0 : ℝ) | some i => D.reward i * (1 - g (Y i))) else 0)
      (rewardBound D) (fun z => (lamEntry_bounds D Y hY t z).2)
    rw [hlen] at h
    exact h

lemma thetaPath_bounds {n m : ℕ} (D : Instance n m) (ω : Outcome D) (Y : Seeds n)
    (hY : ∀ i, Y i ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    0 ≤ thetaPath D ω Y i ∧ thetaPath D ω Y i ≤ (m : ℝ) * rewardBound D := by
  unfold thetaPath
  have hlen : (algorithmHistory D Y ω).length = m := algorithmHistory_length D ω Y
  constructor
  · exact list_sum_nonneg _ _ (fun z => (thetaEntry_bounds D Y hY i z).1)
  · have h := list_sum_le_length_mul (algorithmHistory D Y ω)
      (fun z => if z.1.2 = some i ∧ z.2 = true then D.reward i * g (Y i) else 0)
      (rewardBound D) (fun z => (thetaEntry_bounds D Y hY i z).2)
    rw [hlen] at h
    exact h

lemma algorithmReward_bounds {n m : ℕ} (D : Instance n m) (ω : Outcome D) (Y : Seeds n)
    (_hY : ∀ i, Y i ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ algorithmReward D Y ω ∧ algorithmReward D Y ω ≤ (m : ℝ) * rewardBound D := by
  unfold algorithmReward
  have hlen : (algorithmHistory D Y ω).length = m := algorithmHistory_length D ω Y
  constructor
  · exact list_sum_nonneg _ _ (fun z => (rewardEntry_bounds D z).1)
  · have h := list_sum_le_length_mul (algorithmHistory D Y ω)
      (fun z => if z.2 then actionReward D z.1 else 0)
      (rewardBound D) (fun z => (rewardEntry_bounds D z).2)
    rw [hlen] at h
    exact h

instance seedLaw_instIsFiniteMeasure (n : ℕ) : IsFiniteMeasure (seedLaw n) := by
  unfold seedLaw
  infer_instance

lemma integrable_lambdaPath {n m : ℕ} (D : Instance n m) (ω : Outcome D) (t : Fin m) :
    Integrable (fun Y : Seeds n => lambdaPath D ω Y t) (seedLaw n) := by
  refine Integrable.of_bound (measurable_lambdaPath D ω t).aestronglyMeasurable
    ((m : ℝ) * rewardBound D) ?_
  filter_upwards [ae_mem_cube n] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg (lambdaPath_bounds D ω Y hY t).1]
  exact (lambdaPath_bounds D ω Y hY t).2

lemma integrable_thetaPath {n m : ℕ} (D : Instance n m) (ω : Outcome D) (i : Fin n) :
    Integrable (fun Y : Seeds n => thetaPath D ω Y i) (seedLaw n) := by
  refine Integrable.of_bound (measurable_thetaPath D ω i).aestronglyMeasurable
    ((m : ℝ) * rewardBound D) ?_
  filter_upwards [ae_mem_cube n] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaPath_bounds D ω Y hY i).1]
  exact (thetaPath_bounds D ω Y hY i).2

lemma integrable_algorithmReward {n m : ℕ} (D : Instance n m) (ω : Outcome D) :
    Integrable (fun Y : Seeds n => algorithmReward D Y ω) (seedLaw n) := by
  refine Integrable.of_bound (measurable_algorithmReward D ω).aestronglyMeasurable
    ((m : ℝ) * rewardBound D) ?_
  filter_upwards [ae_mem_cube n] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg (algorithmReward_bounds D ω Y hY).1]
  exact (algorithmReward_bounds D ω Y hY).2

/-! ## Part 4: assembly -/

theorem lemma3_main {n m : ℕ} (D : Instance n m) :
    dualTotal D (lambda D) (theta D) = algorithmValue D := by
  have hgroup : ∀ ω : Outcome D,
      (∑ t : Fin m, lambda D ω t) + (∑ i : Fin n, theta D ω i) =
        seedAverage (fun Y => algorithmReward D Y ω) := by
    intro ω
    unfold lambda theta seedAverage
    have hLam : ∫ Y, (∑ t : Fin m, lambdaPath D ω Y t) ∂seedLaw n
        = ∑ t : Fin m, ∫ Y, lambdaPath D ω Y t ∂seedLaw n := by
      rw [integral_finsetSum]
      intro t _
      exact integrable_lambdaPath D ω t
    have hTheta : ∫ Y, (∑ i : Fin n, thetaPath D ω Y i) ∂seedLaw n
        = ∑ i : Fin n, ∫ Y, thetaPath D ω Y i ∂seedLaw n := by
      rw [integral_finsetSum]
      intro i _
      exact integrable_thetaPath D ω i
    have hLamInt : Integrable (fun Y : Seeds n => ∑ t : Fin m, lambdaPath D ω Y t)
        (seedLaw n) :=
      integrable_finsetSum (Finset.univ : Finset (Fin m))
        (fun t _ => integrable_lambdaPath D ω t)
    have hThetaInt : Integrable (fun Y : Seeds n => ∑ i : Fin n, thetaPath D ω Y i)
        (seedLaw n) :=
      integrable_finsetSum (Finset.univ : Finset (Fin n))
        (fun i _ => integrable_thetaPath D ω i)
    have hcongr : (fun Y : Seeds n =>
          (∑ t : Fin m, lambdaPath D ω Y t) + (∑ i : Fin n, thetaPath D ω Y i))
        =ᵐ[seedLaw n] fun Y => algorithmReward D Y ω :=
      Filter.Eventually.of_forall fun Y => pointwise_identity D ω Y
    calc (∑ t : Fin m, ∫ Y, lambdaPath D ω Y t ∂seedLaw n)
          + (∑ i : Fin n, ∫ Y, thetaPath D ω Y i ∂seedLaw n)
        = (∫ Y, (∑ t : Fin m, lambdaPath D ω Y t) ∂seedLaw n)
          + (∫ Y, (∑ i : Fin n, thetaPath D ω Y i) ∂seedLaw n) := by rw [hLam, hTheta]
      _ = ∫ Y, ((∑ t : Fin m, lambdaPath D ω Y t) + (∑ i : Fin n, thetaPath D ω Y i))
            ∂seedLaw n := (integral_add hLamInt hThetaInt).symm
      _ = ∫ Y, algorithmReward D Y ω ∂seedLaw n := integral_congr_ae hcongr
  unfold dualTotal algorithmValue edgeAverage
  dsimp only
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [hgroup ω]

end Lemma3

theorem solution {n m : ℕ} (D : Instance n m) :
    dualTotal D (lambda D) (theta D) = algorithmValue D :=
  Lemma3.lemma3_main D
