-- Prove2me | solution 1 for PvsNP.multitape_input_bit_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T10:27:42.877671+00:00
-- url     : https://prove2.me/submissions/77ecd8dd-f879-497b-a579-9b54e9405d84

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib

set_option autoImplicit false

open Turing.MultiTapeTM.Universal

/-- The native lookup uses the first matching key, including for duplicated table entries. -/
private def selectedAction (d : Desc) (q : ℕ) (a : Option ℕ) (reads : List (Option ℕ)) : Option Act :=
  (d.table.find? (fun row => decide (row.1 = ⟨q,a,reads⟩))).map Prod.snd

/-- The two nonblank binary symbols cause the same selected action. -/
private def BitSymmetric (d : Desc) : Prop :=
  ∀ q reads, selectedAction d q (some 0) reads = selectedAction d q (some 1) reads

private theorem binary_read (w : List Bool) (p : ℕ) :
    inputSymbol (w.map Bool.toNat) p = none ∨ inputSymbol (w.map Bool.toNat) p = some 0 ∨
      inputSymbol (w.map Bool.toNat) p = some 1 := by
  unfold inputSymbol
  split
  · simp
  · simp only [List.head?_drop,List.getElem?_map]
    generalize w[p-1]? = b
    cases b with
    | none => simp
    | some bit => cases bit <;> simp

private theorem equal_presence (w v : List Bool) (len : w.length = v.length) (p : ℕ) :
    (inputSymbol (w.map Bool.toNat) p).isSome = (inputSymbol (v.map Bool.toNat) p).isSome := by
  rw [Bool.eq_iff_iff]
  simp only [isSome_inputSymbol,List.length_map,len]

private theorem same_selected (d : Desc) (symmetric : BitSymmetric d) (w v : List Bool)
    (len : w.length = v.length) (p q : ℕ) (reads : List (Option ℕ)) :
    selectedAction d q (inputSymbol (w.map Bool.toNat) p) reads =
      selectedAction d q (inputSymbol (v.map Bool.toNat) p) reads := by
  have kind := equal_presence w v len p
  rcases binary_read w p with a | a | a <;> rcases binary_read v p with b | b | b
  all_goals rw [a,b]
  all_goals first | rfl | exact symmetric q reads | exact (symmetric q reads).symm | simp [a,b] at kind

private theorem move_same (p : ℕ) (a b : Option ℕ) (h : a.isSome = b.isSome) (move : SignType) :
    moveInput p a move = moveInput p b move := by
  cases move <;> simp [moveInput,h]

private theorem step_in_terms_of_lookup (d : Desc) (c : SCfg) (q : ℕ) (reading : Option ℕ)
    (mode : c.state = some q) :
    stepWith d c reading = match selectedAction d q reading (c.workTapes.map Tape.read) with
      | none => ({ c with state := none }, none)
      | some a => (⟨a.state,moveInput c.inputPos reading a.inputTape,applyTapes c.workTapes a.workTapes⟩,
          a.output) := by
  simp only [stepWith,mode,selectedAction]
  cases d.table.find? (fun row => decide (row.1 = ⟨q,reading,c.workTapes.map Tape.read⟩)) <;> rfl

private theorem steps_of_equal_length (d : Desc) (symmetric : BitSymmetric d) (w v : List Bool)
    (len : w.length = v.length) (c : SCfg) :
    step d (w.map Bool.toNat) c = step d (v.map Bool.toNat) c := by
  rw [step_eq_stepWith,step_eq_stepWith]
  cases mode : c.state with
  | none => simp [stepWith,mode]
  | some q =>
    rw [step_in_terms_of_lookup d c q _ mode,step_in_terms_of_lookup d c q _ mode,
      same_selected d symmetric w v len c.inputPos q (c.workTapes.map Tape.read)]
    cases selectedAction d q (inputSymbol (v.map Bool.toNat) c.inputPos) (c.workTapes.map Tape.read) with
    | none => rfl
    | some action => simp only [move_same _ _ _ (equal_presence w v len c.inputPos) action.inputTape]

/-- For a bit-symmetric descriptor, equal-length binary inputs produce identical observations. -/
private theorem bit_symmetric_simulate (d : Desc) (symmetric : BitSymmetric d) (w v : List Bool)
    (len : w.length = v.length) (t : ℕ) : simulate d (w.map Bool.toNat) t = simulate d (v.map Bool.toNat) t := by
  have same : (stepOut d (w.map Bool.toNat))^[t] (init d,[]) =
      (stepOut d (v.map Bool.toNat))^[t] (init d,[]) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
      simp only [stepOut,steps_of_equal_length d symmetric w v len]
  simp only [simulate,same]

theorem solution (d : Desc)
    (symmetric : ∀ (q : ℕ) (reads : List (Option ℕ)),
      (d.table.find? (fun row => decide (row.1 = ⟨q,some 0,reads⟩))).map Prod.snd =
      (d.table.find? (fun row => decide (row.1 = ⟨q,some 1,reads⟩))).map Prod.snd)
    (w v : List Bool) (len : w.length = v.length) (t : ℕ) :
    simulate d (w.map Bool.toNat) t = simulate d (v.map Bool.toNat) t := by
  exact bit_symmetric_simulate d symmetric w v len t
