-- Prove2me | solution 1 for SepCostShare.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:11:58.61652+00:00
-- url     : https://prove2.me/submissions/9edb443e-6f9b-4470-812f-99c284d909f7

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Protocol
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm
import Theorems.Thm_SepCostShare_stopped_enforceable
import Theorems.Thm_SepCostShare_line8_well_defined
import Theorems.Thm_SepCostShare_exchange_pi_decrease
import Theorems.Thm_SepCostShare_exchange_count
import Theorems.Thm_SepCostShare_type1_cost_decrease
import Theorems.Thm_SepCostShare_inner_loop_cost_decrease

namespace SepCostShareProof

open SepCostShare

open Classical in
lemma exists_argmin {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (B : N → Finset E) (hB : G.IsProfile B) (i : N) (e : E)
    (hi : i ∈ G.users e B) : ∃ f : E, G.IsArgmin B i e f := by
  have he : e ∈ B i := (Finset.mem_filter.mp hi).2
  have he_alt : e ∈ G.alts B i e := by
    unfold MatroidGame.alts
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ e, ?_⟩
    rw [Finset.insert_erase he]
    exact hB i
  obtain ⟨f, hf_mem, hf_min⟩ :=
    Finset.exists_min_image (G.alts B i e) (fun f => G.pi i f) ⟨e, he_alt⟩
  exact ⟨f, hf_mem, hf_min⟩

lemma algStep_exchange {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive)
    (x y : (N → Finset E) × Option E) (hx : G.IsProfile x.1) (hstep : G.AlgStep x y) :
    G.IsProfile y.1 ∧
      ∃ (i : N) (e f : E), e ∈ x.1 i ∧ f ∉ x.1 i ∧ G.pi i f < G.pi i e ∧
        y.1 = G.swap x.1 i e f := by
  rcases x with ⟨Bx, mx⟩
  rcases y with ⟨By, my⟩
  have finish : ∀ (i : N) (e f : E), i ∈ G.users e Bx →
      (G.deltaBar Bx i e < G.d i e ∨ G.deltaBar Bx i e < G.pi i e) →
      G.IsArgmin Bx i e f → By = G.swap Bx i e f →
      G.IsProfile By ∧
        ∃ (i' : N) (e' f' : E), e' ∈ Bx i' ∧ f' ∉ Bx i' ∧ G.pi i' f' < G.pi i' e' ∧
          By = G.swap Bx i' e' f' := by
    intro i e f hi hsel hf hBy
    obtain ⟨hpi, hf_not_mem, hprof⟩ := exchange_pi_decrease G hG Bx hx i e f hi hsel hf
    have he : e ∈ Bx i := (Finset.mem_filter.mp hi).2
    exact ⟨hBy ▸ hprof, i, e, f, he, hf_not_mem, hpi, hBy⟩
  cases mx with
  | none =>
    rcases hstep with ⟨⟨e, i, hi, hd, f, hf, hBy⟩, _⟩ | ⟨e, _, ⟨_, i, hi, hp, f, hf, hBy⟩, _⟩
    · exact finish i e f hi (Or.inl hd) hf hBy
    · exact finish i e f hi (Or.inr hp) hf hBy
  | some e =>
    rcases hstep with ⟨⟨_, i, hi, hp, f, hf, hBy⟩, _⟩
    exact finish i e f hi (Or.inr hp) hf hBy

lemma isRun_profile {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E) (hB : G.IsProfile B)
    (s : ℕ → (N → Finset E) × Option E) (k : ℕ) (hrun : G.IsRun B s k) :
    ∀ t ≤ k, G.IsProfile (s t).1 := by
  intro t ht
  induction t with
  | zero =>
    rw [hrun.1]
    exact hB
  | succ t ih =>
    have ht_lt : t < k := Nat.lt_of_succ_le ht
    have hprof_t : G.IsProfile (s t).1 := ih (Nat.le_of_lt ht_lt)
    exact (algStep_exchange G hG (s t) (s (t + 1)) hprof_t (hrun.2 t ht_lt)).1

lemma algStep_some_cond2 {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (x : (N → Finset E) × Option E) (B' : N → Finset E) (e : E)
    (hstep : G.AlgStep x (B', some e)) : G.cond2 B' e := by
  rcases x with ⟨Bx, mx⟩
  cases mx with
  | none =>
    rcases hstep with ⟨_, hnone⟩ | ⟨e', _, _, hsome, hnone⟩
    · cases hnone
    · by_cases hc2 : G.cond2 B' e'
      · have heq : some e = some e' := hsome hc2
        injection heq with heq'
        exact heq' ▸ hc2
      · cases hnone hc2
  | some e' =>
    rcases hstep with ⟨_, hsome, hnone⟩
    by_cases hc2 : G.cond2 B' e'
    · have heq : some e = some e' := hsome hc2
      injection heq with heq'
      exact heq' ▸ hc2
    · cases hnone hc2

def RunCostInv {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (B : N → Finset E) (x : (N → Finset E) × Option E) : Prop :=
  match x.2 with
  | none => G.cost x.1 ≤ G.cost B
  | some e =>
      ∃ B₀, G.IsProfile B₀ ∧ G.cost B₀ ≤ G.cost B ∧ Relation.TransGen (G.InnerStep e) B₀ x.1

lemma algStep_cost_inv {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (x y : (N → Finset E) × Option E) (hx : G.IsProfile x.1)
    (hinv : RunCostInv G B x) (hstep : G.AlgStep x y) :
    RunCostInv G B y := by
  rcases x with ⟨Bx, mx⟩
  rcases y with ⟨By, my⟩
  cases mx with
  | none =>
    change G.cost Bx ≤ G.cost B at hinv
    rcases hstep with ⟨⟨e, i, hi, hd, f, hf, rfl⟩, rfl⟩ | ⟨e, _, hinner, hsome, hnone⟩
    · change G.cost (G.swap Bx i e f) ≤ G.cost B
      have hdec := type1_cost_decrease G hG Bx hx i e f hi hd hf
      linarith [hdec.1, hdec.2]
    · have htr : Relation.TransGen (G.InnerStep e) Bx By := Relation.TransGen.single hinner
      by_cases hc2 : G.cond2 By e
      · rw [hsome hc2]
        exact ⟨Bx, hx, hinv, htr⟩
      · rw [hnone hc2]
        change G.cost By ≤ G.cost B
        have hdec := inner_loop_cost_decrease G hG Bx By hx e htr hc2
        linarith
  | some e =>
    change ∃ B₀, G.IsProfile B₀ ∧ G.cost B₀ ≤ G.cost B ∧
      Relation.TransGen (G.InnerStep e) B₀ Bx at hinv
    rcases hinv with ⟨B₀, hB₀, hcost₀, htr⟩
    rcases hstep with ⟨hinner, hsome, hnone⟩
    have htr' : Relation.TransGen (G.InnerStep e) B₀ By := Relation.TransGen.tail htr hinner
    by_cases hc2 : G.cond2 By e
    · rw [hsome hc2]
      exact ⟨B₀, hB₀, hcost₀, htr'⟩
    · rw [hnone hc2]
      change G.cost By ≤ G.cost B
      have hdec := inner_loop_cost_decrease G hG B₀ By hB₀ e htr' hc2
      linarith

lemma isRun_cost_inv {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E) (hB : G.IsProfile B)
    (s : ℕ → (N → Finset E) × Option E) (k : ℕ) (hrun : G.IsRun B s k) :
    ∀ t ≤ k, RunCostInv G B (s t) := by
  intro t ht
  induction t with
  | zero =>
    rw [hrun.1]
    exact le_rfl
  | succ t ih =>
    have ht_lt : t < k := Nat.lt_of_succ_le ht
    have hprof_t := isRun_profile G hG B hB s k hrun t (Nat.le_of_lt ht_lt)
    exact algStep_cost_inv G hG B (s t) (s (t + 1)) hprof_t
      (ih (Nat.le_of_lt ht_lt)) (hrun.2 t ht_lt)

lemma exists_innerStep {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E) (hB : G.IsProfile B)
    (e : E) (h2 : G.cond2 B e) :
    ∃ (B' : N → Finset E) (m : Option E),
      G.InnerStep e B B' ∧ (G.cond2 B' e → m = some e) ∧ (¬ G.cond2 B' e → m = none) := by
  obtain ⟨i, hi, hpi⟩ := line8_well_defined G hG B hB e h2
  obtain ⟨f, hf⟩ := exists_argmin G B hB i e hi
  refine ⟨G.swap B i e f, ?_⟩
  have hinner : G.InnerStep e B (G.swap B i e f) := ⟨h2, i, hi, hpi, f, hf, rfl⟩
  by_cases hc2 : G.cond2 (G.swap B i e f) e
  · exact ⟨some e, hinner, fun _ => rfl, fun h => absurd hc2 h⟩
  · exact ⟨none, hinner, fun h => absurd h hc2, fun _ => rfl⟩

open Classical in
noncomputable def nextState {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (x : (N → Finset E) × Option E) : (N → Finset E) × Option E :=
  if h : ∃ y, G.AlgStep x y then Classical.choose h else x

noncomputable def greedyRun {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (B : N → Finset E) : ℕ → (N → Finset E) × Option E
  | 0 => (B, none)
  | t + 1 => nextState G (greedyRun G B t)

end SepCostShareProof

open SepCostShare
open SepCostShareProof

theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E) (hB : G.IsProfile B) :
    (∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
        G.outerIters s k ≤ Fintype.card N * Fintype.card E * G.rkMax ∧
          k ≤ Fintype.card N * Fintype.card E * G.rkMax) ∧
      (∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
        (s k).2 = none → G.Stopped (s k).1 →
          G.Enforceable (s k).1 ∧ G.cost (s k).1 ≤ G.cost B) ∧
      (∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
        ((s k).2 = none ∧ G.Stopped (s k).1) ∨ ∃ y, G.AlgStep (s k) y) ∧
      (∃ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k ∧ (s k).2 = none ∧
        G.Stopped (s k).1 ∧ k ≤ Fintype.card N * Fintype.card E * G.rkMax ∧
        G.Enforceable (s k).1 ∧ G.cost (s k).1 ≤ G.cost B) := by
  have hc1 : ∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
      G.outerIters s k ≤ Fintype.card N * Fintype.card E * G.rkMax ∧
        k ≤ Fintype.card N * Fintype.card E * G.rkMax := by
    intro s k hrun
    let s' : ℕ → (N → Finset E) := fun t => (s t).1
    have hs0 : G.IsProfile (s' 0) := by
      dsimp [s']
      rw [hrun.1]
      exact hB
    have hstep : ∀ t < k, G.IsProfile (s' (t + 1)) ∧
        ∃ (i : N) (e f : E), e ∈ s' t i ∧ f ∉ s' t i ∧ G.pi i f < G.pi i e ∧
          s' (t + 1) = G.swap (s' t) i e f := by
      intro t ht
      have hprof_t : G.IsProfile (s t).1 := isRun_profile G hG B hB s k hrun t (Nat.le_of_lt ht)
      exact algStep_exchange G hG (s t) (s (t + 1)) hprof_t (hrun.2 t ht)
    obtain ⟨hk1, hk2⟩ := exchange_count G hG s' k hs0 hstep
    have hk : k ≤ Fintype.card N * Fintype.card E * G.rkMax := le_trans hk1 hk2
    have houter : G.outerIters s k ≤ k := by
      unfold MatroidGame.outerIters
      exact (Finset.card_filter_le (Finset.range k) _).trans_eq (Finset.card_range k)
    exact ⟨le_trans houter hk, hk⟩
  have hc2 : ∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
      (s k).2 = none → G.Stopped (s k).1 →
        G.Enforceable (s k).1 ∧ G.cost (s k).1 ≤ G.cost B := by
    intro s k hrun hnone hstop
    have hprof_k : G.IsProfile (s k).1 := isRun_profile G hG B hB s k hrun k le_rfl
    have henf : G.Enforceable (s k).1 := (stopped_enforceable G hG (s k).1 hprof_k).2 hstop
    have hinv := isRun_cost_inv G hG B hB s k hrun k le_rfl
    unfold RunCostInv at hinv
    rw [hnone] at hinv
    exact ⟨henf, hinv⟩
  have hc3 : ∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
      ((s k).2 = none ∧ G.Stopped (s k).1) ∨ ∃ y, G.AlgStep (s k) y := by
    intro s k hrun
    have hprof : G.IsProfile (s k).1 := isRun_profile G hG B hB s k hrun k le_rfl
    rcases hsk : s k with ⟨Bk, mk⟩
    rw [hsk] at hprof
    cases mk with
    | none =>
      by_cases hstop : G.Stopped Bk
      · exact Or.inl ⟨rfl, hstop⟩
      · right
        obtain ⟨e, he⟩ := Classical.not_forall.mp hstop
        by_cases hc1_e : G.cond1 Bk e
        · rcases hc1_e with ⟨i, hi, hd⟩
          obtain ⟨f, hf⟩ := exists_argmin G Bk hprof i e hi
          exact ⟨(G.swap Bk i e f, none), Or.inl ⟨⟨e, i, hi, hd, f, hf, rfl⟩, rfl⟩⟩
        · have hc2_e : G.cond2 Bk e := by
            by_contra hnc2
            exact he ⟨hc1_e, hnc2⟩
          obtain ⟨B', m, hinner, hsome, hnone⟩ := exists_innerStep G hG Bk hprof e hc2_e
          exact ⟨(B', m), Or.inr ⟨e, hc1_e, hinner, hsome, hnone⟩⟩
    | some e =>
      right
      cases k with
      | zero =>
        rw [hrun.1] at hsk
        cases hsk
      | succ t =>
        have hstep_prev : G.AlgStep (s t) (Bk, some e) := by
          rw [← hsk]
          exact hrun.2 t (Nat.lt_succ_self t)
        have hc2_e : G.cond2 Bk e := algStep_some_cond2 G (s t) Bk e hstep_prev
        obtain ⟨B', m, hinner, hsome, hnone⟩ := exists_innerStep G hG Bk hprof e hc2_e
        exact ⟨(B', m), hinner, hsome, hnone⟩
  refine ⟨hc1, hc2, hc3, ?_⟩
  classical
  let s := greedyRun G B
  let M := Fintype.card N * Fintype.card E * G.rkMax
  have hex : ∃ k, ¬ ∃ y, G.AlgStep (s k) y := by
    by_contra hall
    have hall' : ∀ t, ∃ y, G.AlgStep (s t) y := fun t => by
      by_contra hno
      exact hall ⟨t, hno⟩
    have hrunM : G.IsRun B s (M + 1) := by
      refine ⟨rfl, fun t _ => ?_⟩
      change G.AlgStep (s t) (nextState G (s t))
      unfold nextState
      rw [dif_pos (hall' t)]
      exact Classical.choose_spec (hall' t)
    have hle := (hc1 s (M + 1) hrunM).2
    omega
  let k := Nat.find hex
  have hk_no_step : ¬ ∃ y, G.AlgStep (s k) y := Nat.find_spec hex
  have hrun_k : G.IsRun B s k := by
    refine ⟨rfl, fun t ht => ?_⟩
    have hstep_t : ∃ y, G.AlgStep (s t) y := by
      by_contra hno
      exact Nat.find_min hex ht hno
    change G.AlgStep (s t) (nextState G (s t))
    unfold nextState
    rw [dif_pos hstep_t]
    exact Classical.choose_spec hstep_t
  have hk_le : k ≤ M := (hc1 s k hrun_k).2
  rcases hc3 s k hrun_k with ⟨hnone, hstop⟩ | hstep_k
  · obtain ⟨henf, hcost⟩ := hc2 s k hrun_k hnone hstop
    exact ⟨s, k, hrun_k, hnone, hstop, hk_le, henf, hcost⟩
  · exact absurd hstep_k hk_no_step
