-- Prove2me | solution 1 for PvsNP.NativeStockTape.replay_step_exact
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T02:43:44.165702+00:00
-- url     : https://prove2.me/submissions/2cb0a6ec-65ac-4f37-85e7-7129572daaaf

import Definitions.Def_StockOneWorkReplay

set_option autoImplicit false

namespace PvsNP.NativeStockTape

section

variable {Γ : Type} [Inhabited Γ]

private theorem decode_head (decode : Option ℕ → Γ) (blank : decode none = default)
    (xs : List (Option ℕ)) : (xs.map decode).headI = decode (xs.headD none) := by
  cases xs with
  | nil => exact blank.symm
  | cons _ _ => rfl

theorem view_head (decode : Option ℕ → Γ) (blank : decode none = default) (t : WorkTape) :
    (view decode t).head = decode t.read := by
  exact decode_head decode blank t.right

omit [Inhabited Γ] in
private theorem map_tail (decode : Option ℕ → Γ) (xs : List (Option ℕ)) :
    xs.tail.map decode = (xs.map decode).tail := by
  cases xs <;> rfl

open Turing.MultiTapeTM.Universal in
theorem view_move (decode : Option ℕ → Γ) (blank : decode none = default)
    (t : WorkTape) (dir : Turing.Dir) :
    view decode (t.move (match dir with | .left => .neg | .right => .pos)) =
      (view decode t).move dir := by
  cases dir with
  | left =>
    simp only [view,Tape.move,Turing.Tape.move_left_mk',List.map_cons,
      Turing.ListBlank.tail_mk,Turing.ListBlank.cons_mk,Turing.ListBlank.head_mk,
      map_tail,decode_head decode blank]
  | right =>
    simp only [view,Tape.move,Tape.read,Turing.Tape.move_right_mk',List.map_cons,
      Turing.ListBlank.tail_mk,Turing.ListBlank.cons_mk,Turing.ListBlank.head_mk,
      map_tail,decode_head decode blank]

theorem view_write (decode : Option ℕ → Γ) (t : WorkTape) (symbol : Option ℕ) :
    view decode (t.write symbol) = (view decode t).write (decode symbol) := by
  simp only [view,Turing.MultiTapeTM.Universal.Tape.write,Turing.Tape.write_mk',
    List.map_cons,Turing.ListBlank.tail_mk,Turing.ListBlank.cons_mk,map_tail]

theorem view_apply (encode : Γ → Option ℕ) (decode : Option ℕ → Γ)
    (blank : decode none = default) (inverse : Function.LeftInverse decode encode)
    (t : WorkTape) (operation : Turing.TM0.Stmt Γ) :
    view decode (t.apply (nativeOp encode operation)) =
      match operation with
      | .move dir => (view decode t).move dir
      | .write a => (view decode t).write a := by
  cases operation with
  | move dir =>
    cases dir
    · exact view_move decode blank t .left
    · exact view_move decode blank t .right
  | write a =>
    change view decode (t.write (encode a)) = (view decode t).write a
    rw [view_write,inverse a]

end

open Turing.MultiTapeTM.Universal

variable {Γ Λ : Type} [Inhabited Λ]

private theorem find_of_unique {A : Type} (xs : List A) (test : A → Bool) (specific : A)
    (listed : specific ∈ xs) (hit : test specific = true)
    (unique : ∀ y ∈ xs, test y = true → y = specific) :
    xs.find? test = some specific := by
  cases found : xs.find? test with
  | none =>
    have absent := List.find?_eq_none.mp found specific listed
    rw [hit] at absent
    contradiction
  | some v =>
    rw [unique v (List.mem_of_find?_eq_some found) (List.find?_some found)]

theorem replayRows_find [Fintype Γ] [Fintype Λ] (M : Turing.TM0.Machine Γ Λ)
    (encodeState : Λ ↪ ℕ) (encodeSymbol : Γ → Option ℕ)
    (symbolInjective : Function.Injective encodeSymbol) (answer : Γ → Option ℕ)
    (q : Λ) (a : Γ) :
    (replayRows M encodeState encodeSymbol answer).find? (·.1 = replayKey encodeState encodeSymbol q a) =
      some (replayRow M encodeState encodeSymbol answer q a) := by
  apply find_of_unique
  · exact List.mem_map.mpr ⟨(q,a),by simp,rfl⟩
  · simp [replayRow]
  · intro row listed hit
    obtain ⟨⟨s,b⟩,_,rfl⟩ := List.mem_map.mp listed
    have key := of_decide_eq_true hit
    have labels := congrArg Key.state key
    have symbols := congrArg Key.work key
    change encodeState s+3 = encodeState q+3 at labels
    change [encodeSymbol b] = [encodeSymbol a] at symbols
    have sq : s = q := encodeState.injective (Nat.add_right_cancel labels)
    have ba : b = a := symbolInjective (by simpa using symbols)
    rw [sq,ba]

omit [Inhabited Λ] in
private theorem setup_find_none (setup : List (Key × Act))
    (early : ∀ row ∈ setup, row.1.state < 3)
    (encodeState : Λ ↪ ℕ) (encodeSymbol : Γ → Option ℕ) (q : Λ) (a : Γ) :
    setup.find? (·.1 = replayKey encodeState encodeSymbol q a) = none := by
  apply List.find?_eq_none.mpr
  intro row member matched
  have small := early row member
  have state := congrArg Key.state (of_decide_eq_true matched)
  change row.1.state = encodeState q+3 at state
  omega

private theorem range_headD (encode : Γ → Option ℕ) (blank : none ∈ Set.range encode)
    (cells : List (Option ℕ)) (valid : ∀ b ∈ cells, b ∈ Set.range encode) :
    cells.headD none ∈ Set.range encode := by
  cases cells with
  | nil => exact blank
  | cons b bs => exact valid b (by simp)

private theorem encodedTape_move (encode : Γ → Option ℕ) (blank : none ∈ Set.range encode)
    (t : WorkTape) (valid : EncodedTape encode t) (dir : SignType) :
    EncodedTape encode (t.move dir) := by
  cases dir with
  | zero => exact valid
  | pos =>
    constructor
    · intro b mem
      rcases List.mem_cons.mp mem with rfl | rest
      · exact range_headD encode blank t.right valid.2
      · exact valid.1 _ rest
    · exact fun b mem => valid.2 b (List.mem_of_mem_tail mem)
  | neg =>
    constructor
    · exact fun b mem => valid.1 b (List.mem_of_mem_tail mem)
    · intro b mem
      rcases List.mem_cons.mp mem with rfl | rest
      · exact range_headD encode blank t.left valid.1
      · exact valid.2 _ rest

private theorem encodedTape_apply (encode : Γ → Option ℕ) (blank : none ∈ Set.range encode)
    (t : WorkTape) (valid : EncodedTape encode t) (op : Turing.TM0.Stmt Γ) :
    EncodedTape encode (t.apply (nativeOp encode op)) := by
  cases op with
  | move dir =>
    cases dir
    · exact encodedTape_move encode blank t valid .neg
    · exact encodedTape_move encode blank t valid .pos
  | write a =>
    refine ⟨valid.1,?_⟩
    intro b mem
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨a,rfl⟩
    · exact valid.2 b (List.mem_of_mem_tail tail)

variable [Inhabited Γ]

/-- A finite table with one work tape exactly simulates a stock atomic
step while the physical input stays at its right end. -/
theorem _root_.solution [Fintype Γ] [Fintype Λ] (M : Turing.TM0.Machine Γ Λ)
    (encodeState : Λ ↪ ℕ) (encodeSymbol : Γ → Option ℕ) (decode : Option ℕ → Γ)
    (inverse : Function.LeftInverse decode encodeSymbol) (blank : encodeSymbol default = none)
    (answer : Γ → Option ℕ) (setup : List (Key × Act)) (early : ∀ row ∈ setup, row.1.state < 3)
    (input : List ℕ) (q : Λ) (t : WorkTape) (valid : EncodedTape encodeSymbol t) :
    let native := step (replayDescriptor M encodeState encodeSymbol answer setup) input
      (packConfig input encodeState q t)
    match Turing.TM0.step M ⟨q,view decode t⟩ with
    | none => native.1.state = none ∧ native.2 = answer (view decode t).head
    | some next => ∃ u : WorkTape, native = (packConfig input encodeState next.q u,none) ∧
        EncodedTape encodeSymbol u ∧ view decode u = next.Tape := by
  have blankDecode : decode none = default := by rw [← blank,inverse]
  let a := (view decode t).head
  have blankRange : none ∈ Set.range encodeSymbol := ⟨default,blank⟩
  have reading : t.read = encodeSymbol a := by
    obtain ⟨x,hx⟩ := range_headD encodeSymbol blankRange t.right valid.2
    dsimp only [a]
    rw [view_head decode blankDecode,show t.read = encodeSymbol x from hx.symm,inverse]
  have key : (packConfig input encodeState q t).key input (encodeState q+3) =
      replayKey encodeState encodeSymbol q a := by
    simp [packConfig,SCfg.key,replayKey,inputSymbol,reading]
  have looked : (replayDescriptor M encodeState encodeSymbol answer setup).table.find?
      (·.1 = replayKey encodeState encodeSymbol q a) = some (replayRow M encodeState encodeSymbol answer q a) := by
    unfold replayDescriptor
    rw [List.find?_append,setup_find_none setup early encodeState encodeSymbol q a]
    exact replayRows_find M encodeState encodeSymbol inverse.injective answer q a
  have runs : step (replayDescriptor M encodeState encodeSymbol answer setup) input
      (packConfig input encodeState q t) = ((replayRow M encodeState encodeSymbol answer q a).2.apply input
          (packConfig input encodeState q t), (replayRow M encodeState encodeSymbol answer q a).2.output) := by
    unfold step
    rw [show (packConfig input encodeState q t).state = some (encodeState q+3) from rfl]
    dsimp only
    rw [key,looked]
  dsimp only
  rw [runs]
  rw [show Turing.TM0.step M ⟨q, view decode t⟩ =
    (M q a).map (fun p => ⟨p.1, match p.2 with
      | .move dir => (view decode t).move dir
      | .write b => (view decode t).write b⟩) from rfl]
  cases command : M q a with
  | none => simp [replayRow, command, Act.apply, a]
  | some data =>
    obtain ⟨next,op⟩ := data
    simp only [Option.map_some]
    refine ⟨t.apply (nativeOp encodeSymbol op),?_,encodedTape_apply encodeSymbol blankRange t valid op,?_⟩
    · simp [replayRow,command,Act.apply,packConfig,moveInput,applyTapes]
    · exact view_apply encodeSymbol decode blankDecode inverse t op

end PvsNP.NativeStockTape

#print axioms solution
