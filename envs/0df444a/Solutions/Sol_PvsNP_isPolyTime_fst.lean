-- Prove2me | solution 1 for PvsNP.isPolyTime_fst
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T06:46:07.530789+00:00
-- url     : https://prove2.me/submissions/daf9ee1f-043a-42ed-92ec-a64a8444a1a6

import Definitions.Def_PvsNP_complexity_classes

open Computability Turing PvsNP

namespace FstTM

/-- Labels of the projection machine: `copy` reads the leading self-delimiting block and
copies its payload to the auxiliary stack, `drain` discards the rest of the input, and
`emit` moves the auxiliary stack to the output stack. -/
inductive Lbl where
  | copy : Lbl
  | drain : Lbl
  | emit : Lbl
  deriving DecidableEq, Inhabited

instance : Fintype Lbl := ⟨{Lbl.copy, Lbl.drain, Lbl.emit}, by intro x; cases x <;> simp⟩

/-- The three stacks all carry bits. -/
abbrev Gam : Fin 3 → Type := fun _ => Bool

open TM2.Stmt in
/-- The program of the projection machine. Stack `0` is the input, stack `1` the output and
stack `2` an auxiliary stack used to restore the order of the copied bits. -/
def prog : Lbl → TM2.Stmt Gam Lbl (Option Bool)
  | .copy =>
      pop 0 (fun _ x => x) <|
        branch (fun v => v == some true)
          (pop 0 (fun _ x => x) <| push 2 (fun v => v.getD false) <| goto fun _ => .copy)
          (goto fun _ => .drain)
  | .drain =>
      pop 0 (fun _ x => x) <|
        branch (fun v => v.isSome) (goto fun _ => .drain) (goto fun _ => .emit)
  | .emit =>
      pop 2 (fun _ x => x) <|
        branch (fun v => v.isSome)
          (push 1 (fun v => v.getD false) <| goto fun _ => .emit)
          halt

/-- The bundled machine. -/
@[reducible] def machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Gam
  Λ := Lbl
  main := .copy
  σ := Option Bool
  initialState := none
  m := prog

/-- Stack contents as a function on the three stack indices. -/
def stk (a b c : List Bool) : ∀ k : Fin 3, List (Gam k)
  | 0 => a
  | 1 => b
  | 2 => c

@[simp] theorem stk_update_zero (a b c a' : List Bool) :
    Function.update (stk a b c) 0 a' = stk a' b c := by
  funext k; fin_cases k <;> simp [stk, Function.update]

@[simp] theorem stk_update_one (a b c b' : List Bool) :
    Function.update (stk a b c) 1 b' = stk a b' c := by
  funext k; fin_cases k <;> simp [stk, Function.update]

@[simp] theorem stk_update_two (a b c c' : List Bool) :
    Function.update (stk a b c) 2 c' = stk a b c' := by
  funext k; fin_cases k <;> simp [stk, Function.update]

/-- One `emit` step on a nonempty auxiliary stack moves one bit to the output stack. -/
theorem step_emit_cons (out aux : List Bool) (x : Bool) (v : Option Bool) :
    TM2.step prog ⟨some .emit, v, stk [] out (x :: aux)⟩
      = some ⟨some .emit, some x, stk [] (x :: out) aux⟩ := by
  cases x <;> simp [TM2.step, prog, stk]

/-- The `emit` phase: the auxiliary stack is emptied onto the output stack, and the machine
halts. -/
theorem emit_iter (aux out : List Bool) (v : Option Bool) :
    (flip bind (TM2.step prog))^[aux.length + 1] (some ⟨some .emit, v, stk [] out aux⟩)
      = some ⟨none, none, stk [] (aux.reverse ++ out) []⟩ := by
  induction aux generalizing out v with
  | nil => simp [TM2.step, prog, stk, flip]
  | cons x t ih =>
    rw [show (x :: t).length + 1 = (t.length + 1) + 1 by simp, Function.iterate_succ_apply]
    have h : (flip bind (TM2.step prog)) (some ⟨some .emit, v, stk [] out (x :: t)⟩)
        = some ⟨some .emit, some x, stk [] (x :: out) t⟩ := by
      simpa [flip] using step_emit_cons out t x v
    rw [h, ih (x :: out) (some x)]
    simp

/-- The `drain` phase: the remaining input is discarded and the machine enters `emit`. -/
theorem drain_iter (rest out aux : List Bool) (v : Option Bool) :
    (flip bind (TM2.step prog))^[rest.length + 1] (some ⟨some .drain, v, stk rest out aux⟩)
      = some ⟨some .emit, none, stk [] out aux⟩ := by
  induction rest generalizing v with
  | nil => simp [TM2.step, prog, stk, flip]
  | cons x t ih =>
    rw [show (x :: t).length + 1 = (t.length + 1) + 1 by simp, Function.iterate_succ_apply]
    have h : (flip bind (TM2.step prog)) (some ⟨some .drain, v, stk (x :: t) out aux⟩)
        = some ⟨some .drain, some x, stk t out aux⟩ := by
      cases x <;> simp [flip, TM2.step, prog, stk]
    rw [h, ih (some x)]

/-- The `copy` phase: the payload of the leading self-delimiting block is copied, in reverse
order, onto the auxiliary stack, and the machine enters `drain`. -/
theorem copy_iter (payload rest out aux : List Bool) (v : Option Bool) :
    (flip bind (TM2.step prog))^[payload.length + 1]
        (some ⟨some .copy, v, stk (BitstringEncoding.delimit payload ++ rest) out aux⟩)
      = some ⟨some .drain, some false, stk rest out (payload.reverse ++ aux)⟩ := by
  induction payload generalizing aux v with
  | nil => simp [BitstringEncoding.delimit, TM2.step, prog, stk, flip]
  | cons x t ih =>
    rw [show (x :: t).length + 1 = (t.length + 1) + 1 by simp, Function.iterate_succ_apply]
    have h : (flip bind (TM2.step prog))
          (some ⟨some .copy, v, stk (BitstringEncoding.delimit (x :: t) ++ rest) out aux⟩)
        = some ⟨some .copy, some x, stk (BitstringEncoding.delimit t ++ rest) out (x :: aux)⟩ := by
      cases x <;> simp [flip, TM2.step, prog, stk, BitstringEncoding.delimit]
    rw [h, ih (x :: aux) (some x)]
    simp

theorem initList_eq (l : List Bool) :
    initList machine l = ⟨some .copy, none, stk l [] []⟩ := by
  unfold initList
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [machine, stk]

theorem haltList_eq (l : List Bool) :
    haltList machine l = ⟨none, none, stk [] l []⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [machine, stk]

/-- The three phases combined: from the initial configuration on input `delimit u ++ w` the
machine reaches the halting configuration carrying `u` on the output stack. -/
theorem run_iter (u w : List Bool) :
    (flip bind (TM2.step prog))^[(u.length + 1) + ((w.length + 1) + (u.length + 1))]
        (some ⟨some .copy, none, stk (BitstringEncoding.delimit u ++ w) [] []⟩)
      = some ⟨none, none, stk [] u []⟩ := by
  rw [Function.iterate_add_apply _ (u.length + 1) ((w.length + 1) + (u.length + 1)),
    Function.iterate_add_apply _ (w.length + 1) (u.length + 1), copy_iter u w [] [] none,
    drain_iter w [] (u.reverse ++ []) (some false),
    show u.length + 1 = (u.reverse ++ []).length + 1 by simp,
    emit_iter (u.reverse ++ []) [] none]
  simp

/-- The machine computes the first projection: on input `delimit u ++ w` it halts with `u` on
the output stack, within `2 * (delimit u ++ w).length + 3` steps. -/
def machine_outputs (u w : List Bool) :
    TM2OutputsInTime machine (BitstringEncoding.delimit u ++ w) (some u)
      (2 * (BitstringEncoding.delimit u ++ w).length + 3) := by
  refine ⟨⟨(u.length + 1) + ((w.length + 1) + (u.length + 1)), ?_⟩, ?_⟩
  · rw [initList_eq]
    refine (run_iter u w).trans ?_
    show some (⟨none, none, stk [] u []⟩ : machine.Cfg) = some (haltList machine u)
    rw [haltList_eq]
    rfl
  · simp only [BitstringEncoding.length_delimit, List.length_append]
    omega

end FstTM

open PvsNP in
theorem solution {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (Prod.fst : α × β → α) := by
  refine ⟨?_⟩
  refine { tm := FstTM.machine, inputAlphabet := Equiv.refl Bool,
           outputAlphabet := Equiv.refl Bool, time := 2 * Polynomial.X + 3,
           outputsFun := ?_ }
  intro p
  have hmap : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => List.map_id l
  have e1 : (BitstringEncoding.toEncoding (α := α × β)).encode p
      = BitstringEncoding.delimit ((BitstringEncoding.toEncoding (α := α)).encode p.1)
        ++ (BitstringEncoding.toEncoding (α := β)).encode p.2 := rfl
  show TM2OutputsInTime FstTM.machine
      (List.map (Equiv.refl Bool).invFun ((BitstringEncoding.toEncoding (α := α × β)).encode p))
      (some (List.map (Equiv.refl Bool).invFun
        ((BitstringEncoding.toEncoding (α := α)).encode p.1)))
      (Polynomial.eval ((BitstringEncoding.toEncoding (α := α × β)).encode p).length
        (2 * Polynomial.X + 3))
  rw [hmap, hmap, e1]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  exact FstTM.machine_outputs _ _
