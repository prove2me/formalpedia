-- Prove2me | solution 1 for PvsNP.multitape_history_tape_preserves_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T10:45:35.761232+00:00
-- url     : https://prove2.me/submissions/d7f1b247-f5d4-4e5c-a47a-6d9859bd618a

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing.MultiTapeTM.Universal

/-- A successful right move records the nonblank input symbol it leaves. -/
private def forwardRead (row : Key × Act) : Option ℕ :=
  match row.2.inputTape with
  | .pos => row.1.input
  | _ => none

private def recordedKey (key : Key) : Key := { key with work := none :: key.work }

private def recordingOp (a : Option ℕ) : Option (Option ℕ) × SignType :=
  match a with
  | none => (none,.zero)
  | some b => (some (some b),.pos)

private def recordedRow (row : Key × Act) : Key × Act :=
  (recordedKey row.1, { row.2 with workTapes := recordingOp (forwardRead row) :: row.2.workTapes })

/-- Prepend a private, write-only history tape without changing dispatch on existing tapes. -/
private def recordInputHistory (d : Desc) : Desc :=
  ⟨d.tapes+1,d.q₀,d.table.map recordedRow⟩

private def historyTape (past : List ℕ) : Tape :=
  ⟨(past.length : ℤ),past.reverse.map some,[]⟩

private def historyCfg (c : SCfg) (past : List ℕ) : SCfg :=
  { c with workTapes := historyTape past :: c.workTapes }

private def forwardEvent (d : Desc) (x : List ℕ) (c : SCfg) : Option ℕ :=
  c.state.bind fun q => (d.table.find? (fun row => decide (row.1 = c.key x q))).bind forwardRead

private def inputHistory (d : Desc) (x : List ℕ) : ℕ → List ℕ
  | 0 => []
  | t+1 => inputHistory d x t ++ (forwardEvent d x (((stepOut d x)^[t] (init d,[])).1)).toList

private theorem tape_apply_recording (past : List ℕ) (event : Option ℕ) :
    (historyTape past).apply (recordingOp event) = historyTape (past ++ event.toList) := by
  cases event with
  | none => simp [historyTape,recordingOp,Tape.apply,Tape.move]
  | some a => simp [historyTape,recordingOp,Tape.apply,Tape.write,Tape.move,Tape.read]

theorem recorded_lookup (d : Desc) (key : Key) :
    ((recordInputHistory d).table.find? (fun row => decide (row.1 = recordedKey key))) =
      (d.table.find? (fun row => decide (row.1 = key))).map recordedRow := by
  unfold recordInputHistory
  rw [List.find?_map]
  congr 2
  funext row
  change decide (recordedKey row.1 = recordedKey key) = decide (row.1 = key)
  have injective : Function.Injective recordedKey := by
    rintro ⟨a,b,c⟩ ⟨x,y,z⟩ h
    simpa [recordedKey] using h
  have sameKey : recordedKey row.1 = recordedKey key ↔ row.1 = key :=
    ⟨fun h => injective h,congrArg recordedKey⟩
  by_cases h : row.1 = key <;> simp [sameKey,h]

private theorem recorded_step (d : Desc) (x : List ℕ) (c : SCfg) (past : List ℕ) :
    step (recordInputHistory d) x (historyCfg c past) =
      (historyCfg (step d x c).1 (past ++ (forwardEvent d x c).toList), (step d x c).2) := by
  cases mode : c.state with
  | none =>
    simp [step,historyCfg,mode,forwardEvent]
  | some q =>
    have lifted : (historyCfg c past).key x q = recordedKey (c.key x q) := rfl
    simp only [step, show (historyCfg c past).state = some q from mode,mode,lifted,
      recorded_lookup,forwardEvent,Option.bind]
    cases matchRow : d.table.find? (fun row => decide (row.1 = c.key x q)) with
    | none => simp [historyCfg]
    | some row =>
      simp only [Option.map_some, Act.apply, recordedRow,
        historyCfg, applyTapes, tape_apply_recording]

private theorem recorded_run (d : Desc) (x : List ℕ) (t : ℕ) :
    (stepOut (recordInputHistory d) x)^[t] (init (recordInputHistory d),[]) =
      ((fun p : SCfg × List ℕ => (historyCfg p.1 (inputHistory d x t),p.2))
        ((stepOut d x)^[t] (init d,[]))) := by
  induction t with
  | zero => simp [init,recordInputHistory,historyCfg,historyTape,inputHistory,List.replicate_succ]
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
    simp only [stepOut,recorded_step,inputHistory]

/-- The added history tape changes no observed output or halting flag at any clock. -/
private theorem recorded_simulate (d : Desc) (x : List ℕ) (t : ℕ) :
    simulate (recordInputHistory d) x t = simulate d x t := by
  simp only [simulate,recorded_run]
  rfl

theorem solution (d : Desc) (x : List ℕ) (t : ℕ) :
    simulate ⟨d.tapes+1,d.q₀,d.table.map (fun row =>
      ({row.1 with work := none :: row.1.work},
        {row.2 with workTapes :=
          (match (match row.2.inputTape with | .pos => row.1.input | _ => none) with
           | none => (none,.zero)
           | some b => (some (some b),.pos)) :: row.2.workTapes}))⟩ x t = simulate d x t := by
  exact recorded_simulate d x t
