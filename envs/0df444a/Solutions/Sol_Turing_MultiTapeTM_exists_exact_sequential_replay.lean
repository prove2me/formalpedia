-- Prove2me | solution 1 for Turing.MultiTapeTM.exists_exact_sequential_replay
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T20:23:34.105265+00:00
-- url     : https://prove2.me/submissions/cb32268f-3034-4ecf-bde7-2669d46b5e5d

import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NativeReplay

open Turing Turing.MultiTapeTM

variable {k : ℕ} {Symbol State Summary : Type*}

structure Observer (Symbol Summary : Type*) where
  initial : Summary
  read : Summary → Symbol → Summary
  mismatch : Symbol

def Observer.report (ob : Observer Symbol Summary) (output : List Symbol) : Summary :=
  output.foldl ob.read ob.initial

def Observer.push (ob : Observer Symbol Summary) (report : Summary)
    (symbol : Option Symbol) : Summary :=
  symbol.elim report (ob.read report)

@[simp] theorem report_append (ob : Observer Symbol Summary) (out : List Symbol)
    (symbol : Option Symbol) :
    ob.report (out ++ symbol.toList) = ob.push (ob.report out) symbol := by
  cases symbol <;> simp [Observer.report, Observer.push, List.foldl_append]

inductive Control (State Summary : Type*)
  | first (worker : State) (report : Summary)
  | rewind (worker : RewindState) (saved : Summary)
  | second (worker : State) (saved report : Summary)

private abbrev idle : Option (Option Symbol) × SignType := (none, .zero)

private def firstMode (report : Summary) : Option State → Control State Summary
  | some q => .first q report
  | none => .rewind .start report

private def rewindMode (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (saved : Summary) : Option RewindState → Control State Summary
  | some q => .rewind q saved
  | none => .second tm.q₀ saved ob.initial

private def secondMode (saved report : Summary) : Option State → Option (Control State Summary)
  | some q => some (.second q saved report)
  | none => none

variable [DecidableEq Summary]

private def compare (ob : Observer Symbol Summary) (saved report : Summary)
    (q : Option State) : Option Symbol :=
  if q.isNone ∧ saved ≠ report then some ob.mismatch else none

private noncomputable def action (tm : MultiTapeTM k Symbol State)
    (ob : Observer Symbol Summary) (ctl : Control State Summary) (input : Option Symbol)
    (seen : Fin (k + k) → Option Symbol) : Action (k + k) Symbol (Control State Summary) :=
  match ctl with
  | .first q summary =>
    let a := tm.tr q input (fun j => seen (Fin.castAdd k j))
    ⟨a.inputTape, Fin.append a.workTapes (fun _ => idle), none,
      some (firstMode (ob.push summary a.output) a.state)⟩
  | .rewind q saved =>
    let a := (rewindInput Symbol).tr q input (fun j => j.elim0)
    ⟨a.inputTape, fun _ => idle, none, some (rewindMode tm ob saved a.state)⟩
  | .second q saved summary =>
    let a := tm.tr q input (fun j => seen (Fin.natAdd k j))
    let report := ob.push summary a.output
    ⟨a.inputTape, Fin.append (fun _ => idle) a.workTapes, compare ob saved report a.state,
      secondMode saved report a.state⟩

/-- Run the original machine on the left bank, rewind the real read-only input head,
then rerun on a right bank kept blank throughout. Worker output is folded into finite
control. The wrapper emits its mismatch symbol only if the two summaries differ. -/
noncomputable def machine (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary) :
    MultiTapeTM (k + k) Symbol (Control State Summary) :=
  ofTr (.first tm.q₀ ob.initial) (action tm ob)

variable {input : List Symbol}

def firstView (ob : Observer Symbol Summary) (c : Cfg k Symbol State input) :
    Cfg (k + k) Symbol (Control State Summary) input :=
  ⟨some (firstMode (ob.report c.output) c.state), c.inputPos,
    Fin.append c.workTapes (fun _ _ => none), Fin.append c.workTapePos (fun _ => 0), []⟩

def rewindStart (c : Cfg k Symbol State input) : Cfg 0 Symbol RewindState input :=
  ⟨some .start, c.inputPos, fun j => j.elim0, fun j => j.elim0, []⟩

def rewindView (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (left : Cfg k Symbol State input) (c : Cfg 0 Symbol RewindState input) :
    Cfg (k + k) Symbol (Control State Summary) input :=
  ⟨some (rewindMode tm ob (ob.report left.output) c.state), c.inputPos,
    Fin.append left.workTapes (fun _ _ => none), Fin.append left.workTapePos (fun _ => 0), []⟩

def secondView (ob : Observer Symbol Summary) (left right : Cfg k Symbol State input) :
    Cfg (k + k) Symbol (Control State Summary) input :=
  ⟨secondMode (ob.report left.output) (ob.report right.output) right.state, right.inputPos,
    Fin.append left.workTapes right.workTapes, Fin.append left.workTapePos right.workTapePos,
    (compare ob (ob.report left.output) (ob.report right.output) right.state).toList⟩

@[simp] theorem initialView (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (input : List Symbol) : (machine tm ob).initCfg input = firstView ob (tm.initCfg input) := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [firstView, -Fin.natAdd_eq_addNat]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [firstView, -Fin.natAdd_eq_addNat]
  · rfl

omit [DecidableEq Summary] in
private theorem first_input (ob : Observer Symbol Summary) (c : Cfg k Symbol State input) :
    (firstView ob c).inputSymbol = c.inputSymbol := by
  rfl

omit [DecidableEq Summary] in
private theorem first_work (ob : Observer Symbol Summary) (c : Cfg k Symbol State input) :
    (fun j => (firstView ob c).workTapeSymbols (Fin.castAdd k j)) = c.workTapeSymbols := by
  funext j
  simp [Cfg.workTapeSymbols, firstView]

theorem first_step (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (c : Cfg k Symbol State input) {q : State} (hq : c.state = some q) :
    (machine tm ob).step (firstView ob c) = firstView ob (tm.step c) := by
  have hf : (firstView ob c).state = some (.first q (ob.report c.output)) := by
    simp [firstView, hq, firstMode]
  rw [step_of_state hf, step_of_state hq]
  simp only [machine, tr_ofTr, action, first_input, first_work]
  apply Cfg.ext
  · simp [firstView, Action.apply]
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Action.apply, firstView, idle, -Fin.natAdd_eq_addNat]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [Action.apply, firstView, idle, SignType.cast, -Fin.natAdd_eq_addNat]
  · rfl

omit [DecidableEq Summary] in
private theorem rewind_input (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (left : Cfg k Symbol State input) (c : Cfg 0 Symbol RewindState input) :
    (rewindView tm ob left c).inputSymbol = c.inputSymbol := by
  rfl

theorem rewind_step (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (left : Cfg k Symbol State input) (c : Cfg 0 Symbol RewindState input)
    {q : RewindState} (hq : c.state = some q) :
    (machine tm ob).step (rewindView tm ob left c) =
      rewindView tm ob left ((rewindInput Symbol).step c) := by
  have hf : (rewindView tm ob left c).state = some (.rewind q (ob.report left.output)) := by
    simp [rewindView, hq, rewindMode]
  rw [step_of_state hf, step_of_state hq]
  simp only [machine, tr_ofTr, action, rewind_input]
  have w : (fun j : Fin 0 => j.elim0 : Fin 0 → Option Symbol) = c.workTapeSymbols :=
    Subsingleton.elim _ _
  rw [w]
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext i
    simp [Action.apply, rewindView, SignType.cast]
  · rfl

private theorem second_input (ob : Observer Symbol Summary) (left c : Cfg k Symbol State input) :
    (secondView ob left c).inputSymbol = c.inputSymbol := by
  rfl

private theorem second_work (ob : Observer Symbol Summary) (left c : Cfg k Symbol State input) :
    (fun j => (secondView ob left c).workTapeSymbols (Fin.natAdd k j)) = c.workTapeSymbols := by
  funext j
  simp [Cfg.workTapeSymbols, secondView, -Fin.natAdd_eq_addNat]

theorem second_step (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (left c : Cfg k Symbol State input) :
    (machine tm ob).step (secondView ob left c) = secondView ob left (tm.step c) := by
  cases hq : c.state with
  | none =>
    rw [step_of_halt hq, step_of_halt]
    simp [secondView, secondMode, hq]
  | some q =>
    have hf : (secondView ob left c).state =
        some (.second q (ob.report left.output) (ob.report c.output)) := by
      simp [secondView, secondMode, hq]
    rw [step_of_state hf, step_of_state hq]
    simp only [machine, tr_ofTr, action, second_input, second_work]
    apply Cfg.ext
    · simp [secondView, Action.apply]
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Action.apply, secondView, idle, -Fin.natAdd_eq_addNat]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [Action.apply, secondView, idle, SignType.cast, -Fin.natAdd_eq_addNat]
    · simp [Action.apply, secondView, compare, hq]


private theorem run_map_before_halt {m n : ℕ} {Q R : Type*}
    (source : MultiTapeTM m Symbol Q) (target : MultiTapeTM n Symbol R)
    (embed : Cfg m Symbol Q input → Cfg n Symbol R input)
    (one : ∀ (c : Cfg m Symbol Q input) (q : Q), c.state = some q →
      target.step (embed c) = embed (source.step c))
    (start : Cfg m Symbol Q input) (time : ℕ)
    (live : ∀ j < time, ¬ (source.runFrom start j).Halted) :
    target.runFrom (embed start) time = embed (source.runFrom start time) := by
  induction time with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ, runFrom_succ, ih (fun j hj => live j (Nat.lt_succ_of_lt hj))]
    cases h : (source.runFrom start t).state with
    | none => exact False.elim (live t (Nat.lt_succ_self t) h)
    | some q => exact one _ q h

/-- The left bank simulates every step through the first worker halt. -/
theorem first_run (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (time : ℕ) (live : ∀ j < time, ¬ (tm.runFrom (tm.initCfg input) j).Halted) :
    (machine tm ob).runFrom ((machine tm ob).initCfg input) time =
      firstView ob (tm.runFrom (tm.initCfg input) time) := by
  rw [initialView]
  exact run_map_before_halt tm (machine tm ob) (firstView ob)
    (fun c _ h => first_step tm ob c h) _ time live

/-- The right bank, with the entire first final bank held fixed, is an exact
simulation of any second worker run, including the absorbing halting state. -/
theorem second_run (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (left c : Cfg k Symbol State input) (time : ℕ) :
    (machine tm ob).runFrom (secondView ob left c) time =
      secondView ob left (tm.runFrom c time) := by
  have sim : Function.Semiconj (secondView ob left) tm.step (machine tm ob).step :=
    fun c => (second_step tm ob left c).symm
  exact (sim.iterate_right time c).symm

omit [DecidableEq Summary] in
theorem enters_rewind (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (left : Cfg k Symbol State input) (hlt : left.Halted) :
    firstView ob left = rewindView tm ob left (rewindStart left) := by
  simp [firstView, rewindView, rewindStart, firstMode, rewindMode, hlt]

private theorem rewind_end (left : Cfg k Symbol State input) :
    (rewindInput Symbol).runFrom (rewindStart left) (left.inputPos.val - 1 + 2) =
      ⟨none, 1, fun j => j.elim0, fun j => j.elim0, []⟩ :=
  runFrom_rewindInput left.inputPos _ _ []

theorem rewind_plan (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    (left : Cfg k Symbol State input) :
    ∃ u ≤ input.length + 2,
      (∀ t ≤ u,
        (machine tm ob).runFrom (rewindView tm ob left (rewindStart left)) t =
          rewindView tm ob left ((rewindInput Symbol).runFrom (rewindStart left) t)) ∧
      (machine tm ob).runFrom (rewindView tm ob left (rewindStart left)) u =
        secondView ob left (tm.initCfg input) := by
  obtain ⟨u, hbound, hhalt⟩ := exists_haltsAt
    (show ((rewindInput Symbol).runFrom (rewindStart left) (left.inputPos.val - 1 + 2)).Halted by
      rw [rewind_end left])
  have htime : u ≤ input.length + 2 := by
    have pos := left.inputPos.isLt
    omega
  have hs : ∀ t ≤ u,
      (machine tm ob).runFrom (rewindView tm ob left (rewindStart left)) t =
        rewindView tm ob left ((rewindInput Symbol).runFrom (rewindStart left) t) := by
    intro t ht
    exact run_map_before_halt (rewindInput Symbol) (machine tm ob) (rewindView tm ob left)
      (fun c _ q => rewind_step tm ob left c q) _ t (fun j hj => hhalt.not_halted (hj.trans_le ht))
  have atHalt : (rewindInput Symbol).runFrom (rewindStart left) u =
      ⟨none, 1, fun j => j.elim0, fun j => j.elim0, []⟩ :=
    (hhalt.runFrom_eq hbound).symm.trans (rewind_end left)
  refine ⟨u, htime, hs, ?_⟩
  rw [hs u le_rfl, atHalt]
  rfl

/-- If the original machine halts after τ steps, the wrapper restarts on
the original input with completely blank right work tapes after a bounded
physical rewind. The full old left bank remains frozen. -/
theorem replay_exact (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    {τ : ℕ} (ht : tm.HaltsAt (tm.initCfg input) τ) :
    ∃ u ≤ input.length + 2, ∀ j,
      (machine tm ob).runFrom ((machine tm ob).initCfg input) (τ + u + j) =
        secondView ob (tm.runFrom (tm.initCfg input) τ) (tm.runFrom (tm.initCfg input) j) := by
  let left := tm.runFrom (tm.initCfg input) τ
  obtain ⟨u, hu, _, after⟩ := rewind_plan tm ob left
  refine ⟨u, hu, fun j => ?_⟩
  rw [runFrom_add, runFrom_add, first_run tm ob τ (fun s hs => ht.not_halted hs),
    enters_rewind tm ob left ht.halted, after, second_run]

private theorem second_empty (tm : MultiTapeTM k Symbol State)
    (ob : Observer Symbol Summary) {τ : ℕ} (ht : tm.HaltsAt (tm.initCfg input) τ)
    (t : ℕ) :
    (secondView ob (tm.runFrom (tm.initCfg input) τ) (tm.runFrom (tm.initCfg input) t)).output = [] := by
  by_cases hl : (tm.runFrom (tm.initCfg input) t).Halted
  · rw [ht.runFrom_eq (ht.le_of_halted hl)]
    simp [secondView, compare]
  · cases hs : (tm.runFrom (tm.initCfg input) t).state with
    | none => exact False.elim (hl hs)
    | some q =>
        change (compare ob _ _ (tm.runFrom (tm.initCfg input) t).state).toList = []
        unfold compare
        rw [hs]
        simp

/-- At every physical cutoff, the native wrapper has produced no mismatch.
Its observation is computed by the finite controller, so neither proof
nor implementation retains an output transcript. The worker need not halt. -/
theorem output_empty (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary) (T : ℕ) :
    ((machine tm ob).runFrom ((machine tm ob).initCfg input) T).output = [] := by
  by_cases halt : (tm.runFrom (tm.initCfg input) T).Halted
  · obtain ⟨τ, hτT, hτ⟩ := exists_haltsAt halt
    let left := tm.runFrom (tm.initCfg input) τ
    let lrew := rewindView tm ob left (rewindStart left)
    have first : (machine tm ob).runFrom ((machine tm ob).initCfg input) τ = lrew := by
      rw [first_run tm ob τ (fun j hj => hτ.not_halted hj), enters_rewind tm ob left hτ.halted]
    obtain ⟨u, _, during, after⟩ := rewind_plan tm ob left
    have rest : T = τ + (T-τ) := by omega
    rw [rest, runFrom_add, first]
    by_cases before : T - τ ≤ u
    · rw [during _ before]
      rfl
    · have tRest : T-τ = u + (T-τ-u) := by omega
      rw [tRest, runFrom_add]
      change ((machine tm ob).runFrom
        ((machine tm ob).runFrom (rewindView tm ob left (rewindStart left)) u)
          (T-τ-u)).output = []
      rw [after, second_run]
      exact second_empty tm ob hτ (T-τ-u)
  · rw [first_run tm ob T]
    · rfl
    · intro j hj early
      exact halt ((congrArg Cfg.state (tm.runFrom_eq_of_halt (tm.initCfg input) hj.le early)).trans early)


/-- Exact halt timing with a cold second bank. The duration of the rewind
can depend on the input position at the first halt. -/
theorem replay_haltsAt (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    {τ : ℕ} (ht : tm.HaltsAt (tm.initCfg input) τ) :
    ∃ u ≤ input.length + 2,
      (machine tm ob).HaltsAt ((machine tm ob).initCfg input) (τ + u + τ) := by
  let w := machine tm ob
  let c := tm.initCfg input
  let left := tm.runFrom c τ
  let lrew := rewindView tm ob left (rewindStart left)
  have first : w.runFrom (w.initCfg input) τ = lrew := by
    rw [first_run tm ob τ (fun j hj => ht.not_halted hj), enters_rewind tm ob left ht.halted]
  obtain ⟨u, uBound, during, after⟩ := rewind_plan tm ob left
  have second (j : ℕ) : w.runFrom (w.initCfg input) (τ + u + j) =
      secondView ob left (tm.runFrom c j) := by
    rw [runFrom_add, runFrom_add, first]
    change w.runFrom (w.runFrom (rewindView tm ob left (rewindStart left)) u) j = _
    rw [after, second_run]
  refine ⟨u, uBound, ?_, ?_⟩
  · change (w.runFrom (w.initCfg input) (τ+u+τ)).state = none
    rw [second τ]
    change secondMode _ _ (tm.runFrom c τ).state = none
    rw [ht.halted]
    rfl
  · intro t earlier
    change (w.runFrom (w.initCfg input) t).state ≠ none
    by_cases early : t ≤ τ
    · rw [first_run tm ob t (fun j hj => ht.not_halted (hj.trans_le early))]
      exact Option.some_ne_none _
    · by_cases mid : t ≤ τ+u
      · have time : t = τ + (t-τ) := by omega
        rw [time, runFrom_add, first]
        change (w.runFrom (rewindView tm ob left (rewindStart left)) (t-τ)).state ≠ none
        rw [during _ (by omega)]
        exact Option.some_ne_none _
      · have hbefore : t-(τ+u) < τ := by omega
        have live : (tm.runFrom c (t-(τ+u))).state ≠ none := ht.not_halted hbefore
        have time : t = τ+u+(t-(τ+u)) := by omega
        rw [time, second]
        change secondMode _ _ (tm.runFrom c (t-(τ+u))).state ≠ none
        cases h : (tm.runFrom c (t-(τ+u))).state with
        | none => exact (live h).elim
        | some _ => exact Option.some_ne_none _

theorem replay_halting_iff (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary) :
    (∃ t, ((machine tm ob).runFrom ((machine tm ob).initCfg input) t).Halted) ↔
      ∃ t, (tm.runFrom (tm.initCfg input) t).Halted := by
  constructor
  · rintro ⟨t, stops⟩
    by_contra allLive
    have live (j : ℕ) : ¬(tm.runFrom (tm.initCfg input) j).Halted := fun h => allLive ⟨j,h⟩
    have step := first_run tm ob t (fun j _ => live j)
    rw [step] at stops
    exact (Option.some_ne_none _ stops).elim
  · rintro ⟨t, stops⟩
    obtain ⟨τ, _, early⟩ := exists_haltsAt stops
    obtain ⟨u, _, honest⟩ := replay_haltsAt tm ob early
    exact ⟨τ+u+τ, honest.halted⟩

end NativeReplay

namespace NativeReplay

open Turing Turing.MultiTapeTM

variable {Symbol State Summary : Type*} {k : ℕ} {input : List Symbol}

private def walk (p : Fin (input.length + 2)) : Cfg 0 Symbol RewindState input :=
  ⟨some .walk,p,fun j => j.elim0,fun j => j.elim0,[]⟩

private theorem walk_step (p : Fin (input.length + 2)) (positive : 0 < p.val)
    (hbound : p.val ≤ input.length) :
    (rewindInput Symbol).step (walk (input := input) p) =
      walk (input := input) ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  have read : (walk (input := input) p).inputSymbol = some (input[p.val - 1]'(by omega)) :=
    inputSymbolInner (p.val-1) (by dsimp [walk]; omega) (by omega)
  rw [step_of_state (show (walk (input := input) p).state = some .walk from rfl)]
  rw [read]
  simp only [rewindInput, tr_ofTr]
  refine Cfg.ext ?_ ?_ (Subsingleton.elim _ _) (Subsingleton.elim _ _) ?_
  · rfl
  · change moveInputPos p .neg = _
    exact moveInputPos_neg_of_ne_left p (fun h => by
      have hval : p.val = 0 := congrArg Fin.val h
      omega)
  · rfl

private theorem walk_run (p : Fin (input.length + 2)) (inside : p.val ≤ input.length)
    (t : ℕ) (before : t ≤ p.val) :
    (rewindInput Symbol).runFrom (walk (input := input) p) t =
      walk (input := input) ⟨p.val - t, by have := p.isLt; omega⟩ := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [runFrom_succ, ih (by omega), walk_step _ (by dsimp; omega) (by dsimp; omega)]
    congr 1

private theorem start_step (left : Cfg k Symbol State input) :
    (rewindInput Symbol).step (rewindStart left) =
      walk (input := input) ⟨left.inputPos.val - 1, by have := left.inputPos.isLt; omega⟩ := by
  rw [step_of_state (show (rewindStart left).state = some .start from rfl)]
  simp only [rewindInput, tr_ofTr]
  refine Cfg.ext ?_ ?_ (Subsingleton.elim _ _) (Subsingleton.elim _ _) ?_
  · rfl
  · change moveInputPos left.inputPos .neg = _
    by_cases hp : left.inputPos = 0
    · apply Fin.ext
      change (moveInputPos left.inputPos .neg).val = left.inputPos.val - 1
      simp [hp, moveInputPos]
    · exact moveInputPos_neg_of_ne_left left.inputPos hp
  · rfl

/-- Rewind first halts at the exact address determined by the original
head position. Equality of the final configuration at that address
alone would not establish this stricter first-halt fact. -/
theorem rewind_first_halt (left : Cfg k Symbol State input) :
    (rewindInput Symbol).HaltsAt (rewindStart left) (left.inputPos.val - 1 + 2) := by
  refine ⟨?_, ?_⟩
  · have h := runFrom_rewindInput left.inputPos (fun i => i.elim0) (fun i => i.elim0) []
    change ((rewindInput Symbol).runFrom (rewindStart left) (left.inputPos.val - 1 + 2)).state = none
    rw [show (rewindInput Symbol).runFrom (rewindStart left) (left.inputPos.val - 1 + 2) = _ from h]
  · intro t before
    cases t with
    | zero => exact Option.some_ne_none _
    | succ t =>
      have pos := left.inputPos.isLt
      rw [show t+1 = 1+t by omega, runFrom_add, runFrom_one, start_step,
        walk_run _ (by dsimp; omega) _ (by dsimp; omega)]
      exact Option.some_ne_none _


/-- The required rewind is bounded both by the input length and by
the number of prior worker steps. -/
theorem rewind_cost_le (tm : MultiTapeTM k Symbol State) (x : List Symbol) (τ : ℕ) :
    (tm.runFrom (tm.initCfg x) τ).inputPos.val - 1 + 2 ≤
      min (x.length+2) (τ+2) := by
  let c := tm.runFrom (tm.initCfg x) τ
  have pos := c.inputPos.isLt
  have initPos : (tm.initCfg x).inputPos.val = 1 := by
    change (1 : Fin (x.length+2)).val = 1
    simp
  have advance : c.inputPos.val ≤ 1 + τ := by
    have bound := tm.inputPos_runFrom_le (tm.initCfg x) τ
    rw [initPos] at bound
    exact bound
  change c.inputPos.val - 1 + 2 ≤ _
  exact le_min (by omega) (by omega)

variable [DecidableEq Summary]

/-- The physical rewind has an integer checkpoint derivable directly from
the head position at the original halt. -/
theorem replay_exact_at_head_clock (tm : MultiTapeTM k Symbol State)
    (ob : Observer Symbol Summary) {τ : ℕ} (ht : tm.HaltsAt (tm.initCfg input) τ)
    (j : ℕ) :
    let left := tm.runFrom (tm.initCfg input) τ
    let u := left.inputPos.val - 1 + 2
    (machine tm ob).runFrom ((machine tm ob).initCfg input) (τ+u+j) =
      secondView ob left (tm.runFrom (tm.initCfg input) j) := by
  let left := tm.runFrom (tm.initCfg input) τ
  let u := left.inputPos.val - 1 + 2
  change (machine tm ob).runFrom ((machine tm ob).initCfg input) (τ+u+j) = _
  have hhalt : (rewindInput Symbol).HaltsAt (rewindStart left) u := rewind_first_halt left
  have before (t : ℕ) (le : t ≤ u) :
      (machine tm ob).runFrom (rewindView tm ob left (rewindStart left)) t =
        rewindView tm ob left ((rewindInput Symbol).runFrom (rewindStart left) t) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [runFrom_succ, runFrom_succ, ih (by omega)]
      cases h : ((rewindInput Symbol).runFrom (rewindStart left) t).state with
      | none => exact (hhalt.not_halted (by omega : t < u) h).elim
      | some q => exact rewind_step tm ob left _ h
  rw [runFrom_add, runFrom_add, first_run tm ob τ (fun s hs => ht.not_halted hs),
    enters_rewind tm ob left ht.halted, before u le_rfl]
  have final :
      (rewindInput Symbol).runFrom (rewindStart left) u =
        ⟨none,1,fun i => i.elim0,fun i => i.elim0,[]⟩ :=
    runFrom_rewindInput left.inputPos (fun i => i.elim0) (fun i => i.elim0) []
  rw [final]
  change (machine tm ob).runFrom (secondView ob left (tm.initCfg input)) j = _
  exact second_run tm ob left _ j


/-- The original head's final position gives an exact formula for the
first physical halt of the replay companion. -/
theorem replay_haltsAt_head_clock (tm : MultiTapeTM k Symbol State) (ob : Observer Symbol Summary)
    {τ : ℕ} (ht : tm.HaltsAt (tm.initCfg input) τ) :
    let left := tm.runFrom (tm.initCfg input) τ
    let u := left.inputPos.val - 1 + 2
    (machine tm ob).HaltsAt ((machine tm ob).initCfg input) (τ+u+τ) := by
  let left := tm.runFrom (tm.initCfg input) τ
  let u := left.inputPos.val - 1 + 2
  let w := machine tm ob
  let c := w.initCfg input
  change w.HaltsAt c (τ+u+τ)
  have exactAt (j : ℕ) : w.runFrom c (τ+u+j) = secondView ob left (tm.runFrom (tm.initCfg input) j) :=
    replay_exact_at_head_clock tm ob ht j
  refine ⟨?_, ?_⟩
  · rw [show w.runFrom c (τ+u+τ) = secondView ob left left from exactAt τ]
    unfold secondView
    have stopped : left.state = none := ht.halted
    rw [stopped]
    rfl
  · intro t earlier stopped
    have stopped' : (w.runFrom c t).state = none := stopped
    by_cases before : t ≤ τ+u
    · have stuck : (w.runFrom c (τ+u)).state = none :=
        (congrArg Cfg.state (w.runFrom_eq_of_halt c before stopped')).trans stopped'
      rw [show w.runFrom c (τ+u) = secondView ob left (tm.initCfg input) from exactAt 0] at stuck
      exact Option.some_ne_none _ stuck
    · have hbefore : t-(τ+u) < τ := by omega
      have eq : t = τ+u+(t-(τ+u)) := by omega
      rw [eq, exactAt] at stopped'
      have live := ht.not_halted hbefore
      let hright := (tm.runFrom (tm.initCfg input) (t-(τ+u)))
      change (secondView ob left hright).state = none at stopped'
      change hright.state ≠ none at live
      cases h : hright.state with
      | none => exact live h
      | some _ =>
        unfold secondView at stopped'
        simp only [h] at stopped'
        exact Option.some_ne_none _ stopped'

end NativeReplay

namespace NativeReplay

open Turing Turing.MultiTapeTM

variable {State Summary : Type}

instance [Finite State] [Finite Summary] : Finite (Control State Summary) := by
  let _ : Fintype State := Fintype.ofFinite _
  let _ : Fintype Summary := Fintype.ofFinite _
  let f : Control State Summary →
      (State × Summary) ⊕ (RewindState × Summary) ⊕ (State × Summary × Summary)
    | .first q a => .inl (q,a)
    | .rewind q a => .inr (.inl (q,a))
    | .second q a b => .inr (.inr (q,a,b))
  refine Finite.of_injective f ?_
  intro a b hab
  cases a <;> cases b <;> simp_all [f]

end NativeReplay

open Turing Turing.MultiTapeTM

theorem solution {k : ℕ} {Symbol : Type*} {State Summary : Type}
    [Finite State] [Finite Summary] [DecidableEq Summary]
    (worker : MultiTapeTM k Symbol State) (seed : Summary)
    (observe : Summary → Symbol → Summary) (failure : Symbol) :
    ∃ (R : Type) (_finite : Finite R) (replay : MultiTapeTM (k+k) Symbol R),
      ∀ input : List Symbol,
        (∀ t, (replay.runFrom (replay.initCfg input) t).output = []) ∧
        ∀ t, worker.HaltsAt (worker.initCfg input) t →
          let left := worker.runFrom (worker.initCfg input) t
          let rewind := left.inputPos.val - 1 + 2
          replay.HaltsAt (replay.initCfg input) (t+rewind+t) ∧
          ∀ j,
            let right := worker.runFrom (worker.initCfg input) j
            let physical := replay.runFrom (replay.initCfg input) (t+rewind+j)
            physical.inputPos = right.inputPos ∧
            ∀ i : Fin k,
              physical.workTapes (Fin.castAdd k i) = left.workTapes i ∧
              physical.workTapePos (Fin.castAdd k i) = left.workTapePos i ∧
              physical.workTapes (Fin.natAdd k i) = right.workTapes i ∧
              physical.workTapePos (Fin.natAdd k i) = right.workTapePos i := by
  let observer : NativeReplay.Observer Symbol Summary := ⟨seed, observe, failure⟩
  refine ⟨NativeReplay.Control State Summary, inferInstance, NativeReplay.machine worker observer, ?_⟩
  intro input
  refine ⟨fun t => NativeReplay.output_empty (input := input) worker observer t, ?_⟩
  intro t halts
  dsimp only
  refine ⟨NativeReplay.replay_haltsAt_head_clock worker observer halts, ?_⟩
  intro j
  rw [NativeReplay.replay_exact_at_head_clock worker observer halts j]
  constructor
  · rfl
  · intro i
    simp [NativeReplay.secondView, -Fin.natAdd_eq_addNat]

#print axioms solution
