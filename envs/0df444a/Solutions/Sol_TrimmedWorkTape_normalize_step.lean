-- Prove2me | solution 1 for TrimmedWorkTape.normalize_step
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T22:13:10.689462+00:00
-- url     : https://prove2.me/submissions/b255139a-c2cd-4325-bcec-9fb8b21b982f

import Definitions.Def_TrimmedNativeWorkTape

open Turing.MultiTapeTM.Universal TrimmedWorkTape

theorem trim_cons (a : Option ℕ) (xs : List (Option ℕ)) :
    trim (a :: xs) = if a = none ∧ trim xs = [] then [] else a :: trim xs := by
  cases a <;> simp [trim]

theorem trim_idem (xs : List (Option ℕ)) : trim (trim xs) = trim xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [trim_cons]
    split_ifs with empty
    · rfl
    · rw [trim_cons, ih, if_neg empty]

private theorem trim_cons_again (a : Option ℕ) (xs : List (Option ℕ)) :
    trim (a :: trim xs) = trim (a :: xs) := by
  rw [trim_cons, trim_cons, trim_idem]

theorem trim_head (xs : List (Option ℕ)) : (trim xs).headD none = xs.headD none := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    rw [trim_cons]
    split_ifs with empty
    · simp [empty.1]
    · rfl

theorem trim_tail (xs : List (Option ℕ)) : trim xs.tail = (trim xs).tail := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    rw [trim_cons]
    split_ifs with empty
    · simp [empty.2]
    · rfl

theorem normalizeTape_idem (t : Tape) : normalizeTape (normalizeTape t) = normalizeTape t := by
  simp only [normalizeTape,trim_idem]

theorem normalizeTape_read (t : Tape) : (normalizeTape t).read = t.read :=
  trim_head t.right

private theorem normalizeTape_write (t : Tape) (a : Option ℕ) :
    normalizeTape ((normalizeTape t).write a) = normalizeTape (t.write a) := by
  simp only [normalizeTape,Tape.write,trim_idem,← trim_tail,trim_cons_again]

private theorem normalizeTape_move (t : Tape) (m : SignType) :
    normalizeTape ((normalizeTape t).move m) = normalizeTape (t.move m) := by
  cases m with
  | zero => exact normalizeTape_idem t
  | pos =>
    simp only [Tape.move,normalizeTape,Tape.read,trim_head,trim_cons_again,← trim_tail,trim_idem]
  | neg =>
    simp only [Tape.move,normalizeTape,trim_head,trim_cons_again,← trim_tail,trim_idem]

theorem normalizeTape_apply (t : Tape) (a : Option (Option ℕ) × SignType) :
    normalizeTape ((normalizeTape t).apply a) = normalizeTape (t.apply a) := by
  obtain ⟨symbol,move⟩ := a
  cases symbol with
  | none => exact normalizeTape_move t move
  | some s =>
    change normalizeTape (((normalizeTape t).write s).move move) =
      normalizeTape ((t.write s).move move)
    rw [← normalizeTape_move ((normalizeTape t).write s),normalizeTape_write,normalizeTape_move]

private theorem normalize_applyTapes (ts : List Tape) (acts : List (Option (Option ℕ) × SignType)) :
    (applyTapes (ts.map normalizeTape) acts).map normalizeTape =
      (applyTapes ts acts).map normalizeTape := by
  induction ts generalizing acts with
  | nil => rfl
  | cons t ts ih =>
    cases acts with
    | nil =>
      change normalizeTape (normalizeTape t) :: (ts.map normalizeTape).map normalizeTape =
        normalizeTape t :: ts.map normalizeTape
      simp only [normalizeTape_idem,List.map_map,Function.comp_def]
    | cons a acts =>
      simp only [List.map_cons,applyTapes,normalizeTape_apply,ih]

theorem normalizeConfiguration_idem (c : SCfg) :
    normalizeConfiguration (normalizeConfiguration c) = normalizeConfiguration c := by
  simp only [normalizeConfiguration,List.map_map,Function.comp_def,normalizeTape_idem]

private theorem normalize_reads (ts : List Tape) :
    (ts.map normalizeTape).map Tape.read = ts.map Tape.read := by
  simp only [List.map_map,Function.comp_def,normalizeTape_read]

/-- For every simulated input and every native table (including noncanonical
ones), trimming work tapes preserves the emitted symbol and next normalized
configuration. Work-tape motions and actions are unrestricted. -/
theorem solution (d : Desc) (x : List ℕ) (c : SCfg) :
    Prod.map normalizeConfiguration id (step d x (normalizeConfiguration c)) =
      Prod.map normalizeConfiguration id (step d x c) := by
  have key (q : ℕ) : (normalizeConfiguration c).key x q = c.key x q := by
    simp only [SCfg.key,normalizeConfiguration,normalize_reads]
  cases state : c.state with
  | none =>
    have state' : (normalizeConfiguration c).state = none := state
    simp only [step,state,state',Prod.map_apply,id_eq,normalizeConfiguration_idem]
  | some q =>
    have state' : (normalizeConfiguration c).state = some q := state
    simp only [step,state,state',key]
    split
    · simp only [Prod.map_apply,id_eq]
      cases c
      simp only [normalizeConfiguration,List.map_map,Function.comp_def,normalizeTape_idem]
    · simp only [Prod.map_apply,id_eq,Act.apply,normalizeConfiguration,normalize_applyTapes]

#print axioms solution
