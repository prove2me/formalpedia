-- Prove2me | solution 1 for PvsNP.OnlineWindowIO.Native.exact_online_run
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T04:19:38.471802+00:00
-- url     : https://prove2.me/submissions/ae600f22-433b-4567-8b46-bbe40b537b9b

import Definitions.Def_NativeOnlineSingleTape

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PvsNP.OnlineWindowIO.Native

open WorkBoundarySplice
open Turing.MultiTapeTM.Universal

variable {S A : Type}

theorem rawCode_injective : Function.Injective rawCode := by
  intro a b h
  cases a with
  | none => cases b <;> simp [rawCode] at h ⊢
  | some x =>
      cases b with
      | none => simp [rawCode] at h
      | some y => cases x <;> cases y <;> simp [rawCode] at h ⊢

private theorem rowKey_injective (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) :
    Function.Injective (rowKey state symbol) := by
  rintro ⟨s,a,i⟩ ⟨t,b,j⟩ eq
  have st := state.injective (congrArg Key.state eq)
  have ij := rawCode_injective (congrArg Key.input eq)
  have ab : symbol a = symbol b := by simpa [rowKey] using congrArg Key.work eq
  cases st
  cases ij
  cases symbol.injective ab
  rfl

private theorem lookup [Fintype S] [Fintype A] (M : OnlineMachine S A)
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (verdict : S → Option ℕ)
    (e : S × A × Option Bool) :
    (desc M state symbol initial verdict).table.find? (·.1 = rowKey state symbol e) =
       some (rowKey state symbol e,action M state symbol verdict e) := by
  classical
  let table := (desc M state symbol initial verdict).table
  have here : (rowKey state symbol e,action M state symbol verdict e) ∈ table := by
    exact List.mem_map.mpr ⟨e,by simp,rfl⟩
  have present : ∃ hit, table.find? (·.1 = rowKey state symbol e) = some hit := by
    cases found : table.find? (·.1 = rowKey state symbol e) with
    | none =>
        rw [List.find?_eq_none] at found
        have no := found _ here
        simp at no
    | some hit => exact ⟨hit,rfl⟩
  obtain ⟨hit,found⟩ := present
  have selected := List.mem_of_find?_eq_some found
  have key := List.find?_some found
  obtain ⟨origin,_,rfl⟩ := List.mem_map.mp selected
  have same : origin = e := rowKey_injective state symbol (by simpa using key)
  subst origin
  exact found

structure Corresponds (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (word : List Bool)
    (abstract : OnlineConfig S A) (native : SCfg) : Prop where
  control : native.state = some (state abstract.1.state)
  input : 0 < native.inputPos ∧ word.drop (native.inputPos-1) = abstract.2
  tape : ∃ t : Tape, native.workTapes = [t] ∧ t.head = abstract.1.head ∧
    ∀ z, t.cellAt z = symbol (abstract.1.tape z)

private theorem physical_input {word : List Bool} {raw : List Bool} {pos : ℕ}
    (positive : 0 < pos) (remaining : word.drop (pos-1) = raw) :
    inputSymbol (word.map Bool.toNat) pos = rawCode raw.head? := by
  rw [inputSymbol,if_neg (Nat.ne_of_gt positive),← List.map_drop,remaining,List.head?_map]
  rfl

private theorem next_input {word : List Bool} {raw : List Bool} {pos : ℕ}
    (positive : 0 < pos) (remaining : word.drop (pos-1) = raw) (advance : Bool) :
    let next := moveInput pos (rawCode raw.head?) (if advance then .pos else .zero)
    0 < next ∧ word.drop (next-1) = unreadAfter advance raw := by
  cases advance with
  | false => exact ⟨positive,remaining⟩
  | true =>
      cases raw with
      | nil =>
          simpa [moveInput,rawCode,Nat.ne_of_gt positive,unreadAfter] using And.intro positive remaining
      | cons b bs =>
          have dropNext : word.drop (pos+1-1) = bs := by
            have diff : pos + 1 - 1 = (pos - 1) + 1 := by omega
            rw [diff,← List.tail_drop,remaining]
            rfl
          exact ⟨by simp [rawCode,moveInput],by simpa [rawCode,moveInput,unreadAfter] using dropNext⟩

private theorem read_cell (t : Tape) : t.read = t.cellAt t.head := by
  simp only [Tape.read, Tape.cellAt, le_refl, ↓reduceIte, sub_self, Int.toNat_zero]
  cases t.right <;> rfl

private theorem write_cell (t : Tape) (o : Option ℕ) (z : ℤ) :
    (t.write o).cellAt z = if z = t.head then o else t.cellAt z := by
  unfold Tape.cellAt Tape.write
  split_ifs with h₁ h₂ <;> simp only at *
  · subst h₂; simp
  · obtain ⟨n, hn⟩ : ∃ n, (z - t.head).toNat = n + 1 := ⟨(z - t.head).toNat - 1, by omega⟩
    rw [hn, List.getD_cons_succ]
    rcases t.right with _ | ⟨a, r⟩ <;> simp
  · omega

private theorem move_cell (t : Tape) (m : SignType) (z : ℤ) : (t.move m).cellAt z = t.cellAt z := by
  unfold Tape.cellAt Tape.move
  rcases m with _ | _ | _ <;> simp only <;> split_ifs <;> try omega
  · obtain ⟨n, hn⟩ : ∃ n, (z - (t.head - 1)).toNat = n + 1 := ⟨(z - t.head).toNat, by omega⟩
    rw [hn, List.getD_cons_succ, show n = (z - t.head).toNat by omega]
  · rw [show (z - (t.head - 1)).toNat = 0 by omega, List.getD_cons_zero,
      show (t.head - z - 1).toNat = 0 by omega]
    rcases t.left with _ | ⟨a, l⟩ <;> simp
  · obtain ⟨n, hn⟩ : ∃ n, (t.head - z - 1).toNat = n + 1 :=
      ⟨(t.head - z - 1).toNat - 1, by omega⟩
    rw [show (t.head - 1 - z - 1).toNat = n by omega, hn]
    rcases t.left with _ | ⟨a, l⟩ <;> simp
  · rw [show (z - t.head).toNat = (z - (t.head + 1)).toNat + 1 by omega]
    rcases t.right with _ | ⟨a, r⟩ <;> simp
  · rw [show (t.head + 1 - z - 1).toNat = 0 by omega, show (z - t.head).toNat = 0 by omega]
    simp only [Tape.read, List.getD_cons_zero]
    cases t.right <;> rfl
  · rw [show (t.head + 1 - z - 1).toNat = (t.head - z - 1).toNat + 1 by omega]
    simp

private theorem move_head (t : Tape) (m : SignType) : (t.move m).head = t.head + m := by
  rcases m with _ | _ | _ <;> simp [Tape.move, SignType.cast, sub_eq_add_neg]

theorem refine_step [Fintype S] [Fintype A] {M : OnlineMachine S A}
    {state : S ↪ ℕ} {symbol : A ↪ Option ℕ} {initial : S} {verdict : S → Option ℕ}
    {word : List Bool} {a b : OnlineConfig S A} {native : SCfg}
    (rel : Corresponds state symbol word a native) (event : onlineStep M a = some b) :
    let result := step (desc M state symbol initial verdict) (word.map Bool.toNat) native
    Corresponds state symbol word b result.1 ∧ result.2 = none := by
  obtain ⟨t,tapes,head,cells⟩ := rel.tape
  have raw := physical_input rel.input.1 rel.input.2
  have read : t.read = symbol (a.1.tape a.1.head) := by rw [read_cell,cells,head]
  have found := lookup M state symbol initial verdict (a.1.state,a.1.tape a.1.head,a.2.head?)
  unfold onlineStep at event
  cases h : M a.1.state (a.1.tape a.1.head) a.2.head? with
  | none => simp [h] at event
  | some cmd =>
      rcases cmd with ⟨q,value,d,advance⟩
      simp only [h,Option.map_some,Option.some.injEq] at event
      subst b
      simp only [step_eq_stepWith,stepWith,rel.control,raw,tapes,List.map_cons,List.map_nil,read]
      rw [show (⟨state a.1.state,rawCode a.2.head?,[symbol (a.1.tape a.1.head)]⟩ : Key) =
        rowKey state symbol (a.1.state,a.1.tape a.1.head,a.2.head?) from rfl,found]
      simp only [action,h,applyTapes,Tape.apply,Option.elim_some]
      refine ⟨⟨rfl,next_input rel.input.1 rel.input.2 advance,?_⟩,trivial⟩
      refine ⟨_,rfl,?_,?_⟩
      · rw [move_head]
        cases d <;> simp [motion,Motion.shift,Tape.write,SignType.cast,head,sub_eq_add_neg]
      · intro z
        rw [move_cell,write_cell,head]
        by_cases atHead : z = a.1.head
        · simp [write,atHead]
        · simp [write,atHead,cells z]

theorem refine_run [Fintype S] [Fintype A] {M : OnlineMachine S A}
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (verdict : S → Option ℕ)
    {word : List Bool} {a b : OnlineConfig S A} {native : SCfg} {n : ℕ}
    (rel : Corresponds state symbol word a native) (run : OnlineRun M a b n) :
    Corresponds state symbol word b
      ((fun c => (step (desc M state symbol initial verdict) (word.map Bool.toNat) c).1)^[n] native) := by
  induction run generalizing native with
  | refl => exact rel
  | next first _ ih =>
      rw [Function.iterate_succ_apply]
      exact ih (refine_step (initial := initial) (verdict := verdict) rel first).1

theorem refine_stop [Fintype S] [Fintype A] {M : OnlineMachine S A}
    {state : S ↪ ℕ} {symbol : A ↪ Option ℕ} {initial : S} {verdict : S → Option ℕ}
    {word : List Bool} {a : OnlineConfig S A} {native : SCfg}
    (rel : Corresponds state symbol word a native) (stopped : onlineStep M a = none) :
    step (desc M state symbol initial verdict) (word.map Bool.toNat) native =
      ({native with state := none}, verdict a.1.state) := by
  obtain ⟨t,tapes,head,cells⟩ := rel.tape
  have raw := physical_input rel.input.1 rel.input.2
  have read : t.read = symbol (a.1.tape a.1.head) := by rw [read_cell,cells,head]
  have noCommand : M a.1.state (a.1.tape a.1.head) a.2.head? = none := by
    simpa [onlineStep] using stopped
  have found := lookup M state symbol initial verdict (a.1.state,a.1.tape a.1.head,a.2.head?)
  simp only [step_eq_stepWith,stepWith,rel.control,raw,tapes,List.map_cons,List.map_nil,read]
  rw [show (⟨state a.1.state,rawCode a.2.head?,[symbol (a.1.tape a.1.head)]⟩ : Key) =
    rowKey state symbol (a.1.state,a.1.tape a.1.head,a.2.head?) from rfl,found]
  simp [action,noCommand,moveInput,applyTapes]

private theorem init_corresponds [Fintype S] [Fintype A] (M : OnlineMachine S A)
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (blank : A)
    (blankEncoded : symbol blank = none) (verdict : S → Option ℕ) (word : List Bool) :
    Corresponds state symbol word (⟨initial,0,fun _ => blank⟩, word)
      (init (desc M state symbol initial verdict)) := by
  refine ⟨rfl,by simp [init,desc],⟨⟨0,[],[]⟩,rfl,rfl,?_⟩⟩
  intro z
  simp [blankEncoded,Tape.cellAt]

theorem table_one_way [Fintype S] [Fintype A] (M : OnlineMachine S A)
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (verdict : S → Option ℕ) :
    (desc M state symbol initial verdict).tapes = 1 ∧
      ∀ row ∈ (desc M state symbol initial verdict).table, row.2.inputTape ≠ .neg := by
  refine ⟨rfl,?_⟩
  intro row listed
  obtain ⟨⟨q,v,i⟩,_,rfl⟩ := List.mem_map.mp listed
  cases cmd : M q v i with
  | none => simp [action,cmd]
  | some payload =>
      rcases payload with ⟨q',v',d,advance⟩
      cases advance <;> simp [action,cmd]

theorem refine_run_output [Fintype S] [Fintype A] {M : OnlineMachine S A}
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (verdict : S → Option ℕ)
    {word : List Bool} {a b : OnlineConfig S A} {native : SCfg} {n : ℕ}
    (rel : Corresponds state symbol word a native) (run : OnlineRun M a b n) (acc : List ℕ) :
    ∃ t : SCfg,
      (stepOut (desc M state symbol initial verdict) (word.map Bool.toNat))^[n] (native,acc) =
        (t,acc) ∧ Corresponds state symbol word b t := by
  induction run generalizing native with
  | refl => exact ⟨native,rfl,rel⟩
  | next first _ ih =>
      obtain ⟨source,quiet⟩ := refine_step (initial := initial) (verdict := verdict) rel first
      obtain ⟨t,accurate,rest⟩ := ih source
      refine ⟨t,?_,rest⟩
      rw [Function.iterate_succ_apply]
      simpa [stepOut,quiet] using accurate

/-- Compiling a blank-tape online program to a descriptor preserves the
clock, apart from one terminal transition emitting the verdict. -/
theorem simulate [Fintype S] [Fintype A] {M : OnlineMachine S A}
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (blank : A)
    (blankEncoded : symbol blank = none) (verdict : S → Option ℕ)
    {word : List Bool} {b : OnlineConfig S A} {n : ℕ}
    (run : OnlineRun M (⟨initial,0,fun _ => blank⟩,word) b n)
    (terminal : onlineStep M b = none) :
    Turing.MultiTapeTM.Universal.simulate (desc M state symbol initial verdict) (word.map Bool.toNat) (n+1) =
      ((verdict b.1.state).toList,true) := by
  obtain ⟨t,steps,rel⟩ := refine_run_output state symbol initial verdict
    (init_corresponds M state symbol initial blank blankEncoded verdict word) run []
  have stopped := refine_stop (initial := initial) (verdict := verdict) rel terminal
  unfold Turing.MultiTapeTM.Universal.simulate
  rw [Function.iterate_succ_apply',steps]
  simp [stepOut,stopped]

end PvsNP.OnlineWindowIO.Native

open PvsNP.OnlineWindowIO PvsNP.OnlineWindowIO.Native

theorem solution
    {S A : Type} [Fintype S] [Fintype A] {M : OnlineMachine S A}
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (blank : A)
    (blankEncoded : symbol blank = none) (verdict : S → Option ℕ)
    {word : List Bool} {b : OnlineConfig S A} {n : ℕ}
    (run : OnlineRun M (⟨initial,0,fun _ => blank⟩,word) b n)
    (terminal : onlineStep M b = none) :
    (desc M state symbol initial verdict).tapes = 1 ∧
    (∀ row ∈ (desc M state symbol initial verdict).table, row.2.inputTape ≠ .neg) ∧
    Turing.MultiTapeTM.Universal.simulate (desc M state symbol initial verdict) (word.map Bool.toNat) (n+1) =
      ((verdict b.1.state).toList,true) := by
  obtain ⟨one,monotone⟩ := table_one_way M state symbol initial verdict
  exact ⟨one,monotone,simulate state symbol initial blank blankEncoded verdict run terminal⟩

#print axioms solution
