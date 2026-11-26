-- Prove2me | solution 1 for Turing.SubsequentialTransducer.tm2_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:48:39.87964+00:00
-- url     : https://prove2.me/submissions/faac20c0-4f5c-426e-8a40-7ed5cc4d0d1c

import Mathlib
import Definitions.Def_Turing_SubsequentialTransducer_run

open Turing StateTransition

set_option autoImplicit false

namespace Turing.SubsequentialTransducer

private inductive Stack
  | input | buffer | output
  deriving DecidableEq

private instance : Fintype Stack where
  elems := {.input, .buffer, .output}
  complete := by intro k; cases k <;> simp

private abbrev Alphabet (A B : Type) : Stack → Type
  | .input => A
  | .buffer | .output => B

private abbrev Label (A S : Type) := S ⊕ ((S × Option A) ⊕ Unit)

private abbrev Register (A B : Type) := Option A ⊕ Option B

private def memory {A B : Type} (xs : List A) (buf out : List B) :
    (k : Stack) → List (Alphabet A B k)
  | .input => xs
  | .buffer => buf
  | .output => out

private abbrev Statement (A B S : Type) :=
  TM2.Stmt (Alphabet A B) (Label A S) (Register A B)

private def pushWord {A B S : Type} (word : List B) (next : Statement A B S) :
    Statement A B S :=
  word.foldr (fun b p => .push .buffer (fun _ => b) p) next

private def code {A B S : Type} [Inhabited B]
    (step : S → A → S × List B) (finish : S → List B) :
    Label A S → Statement A B S
  | .inl s =>
      .pop .input (fun _ a => .inl a)
        (.goto fun r => .inr (.inl (s, r.getLeft?.getD none)))
  | .inr (.inl (s, some a)) =>
      pushWord (step s a).2 (.load (fun _ => .inl none)
        (.goto fun _ => .inl (step s a).1))
  | .inr (.inl (s, none)) =>
      pushWord (finish s) (.load (fun _ => .inl none)
        (.goto fun _ => .inr (.inr ())))
  | .inr (.inr ()) =>
      .pop .buffer (fun _ b => .inr b)
        (.branch (fun r => (r.getRight?.getD none).isSome)
          (.push .output (fun r => (r.getRight?.getD none).getD default)
            (.load (fun _ => .inl none) (.goto fun _ => .inr (.inr ()))))
          (.load (fun _ => .inl none) .halt))

private abbrev machine {A B S : Type} [Fintype A] [Fintype B] [Fintype S] [Inhabited B]
    (step : S → A → S × List B) (finish : S → List B) (initial : S) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A B
  Γk₀Fin := (inferInstance : Fintype A)
  Λ := Label A S
  main := .inl initial
  σ := Register A B
  initialState := .inl none
  m := code step finish

private theorem update_input {A B : Type} (xs ys : List A) (buf out : List B) :
    Function.update (memory xs buf out) .input ys = memory ys buf out := by
  funext k
  cases k <;> rfl

private theorem update_buffer {A B : Type} (xs : List A) (buf buf' out : List B) :
    Function.update (memory xs buf out) .buffer buf' = memory xs buf' out := by
  funext k
  cases k <;> rfl

private theorem update_output {A B : Type} (xs : List A) (buf out out' : List B) :
    Function.update (memory xs buf out) .output out' = memory xs buf out' := by
  funext k
  cases k <;> rfl

private theorem exec_pushWord {A B S : Type} (word : List B) (next : Statement A B S)
    (r : Register A B) (xs : List A) (buf out : List B) :
    TM2.stepAux (pushWord word next) r (memory xs buf out) =
      TM2.stepAux next r (memory xs (word.reverse ++ buf) out) := by
  induction word generalizing buf with
  | nil => rfl
  | cons b word ih =>
    change TM2.stepAux (pushWord word next) r
      (Function.update (memory xs buf out) .buffer (b :: buf)) = _
    rw [update_buffer, ih (b :: buf)]
    simp [List.reverse_cons, List.append_assoc]

private def cfg {A B S : Type} (l : Option (Label A S)) (r : Register A B)
    (xs : List A) (buf out : List B) :
    TM2.Cfg (Alphabet A B) (Label A S) (Register A B) :=
  ⟨l, r, memory xs buf out⟩

private abbrev reading {A B S : Type} (s : S) (xs : List A) (buf : List B) :=
  cfg (some (.inl s)) (.inl none) xs buf []

private abbrev reversing {B : Type} (A₀ : Type) (S₀ : Type) (buf out : List B) :=
  cfg (A := A₀) (B := B) (S := S₀) (some (.inr (.inr ()))) (.inl none) [] buf out

private abbrev stopped {B : Type} (A₀ : Type) (S₀ : Type) (out : List B) :=
  cfg (A := A₀) (B := B) (S := S₀) none (.inl none) [] [] out

private def one {C : Type} {f : C → Option C} {x y : C} (h : f x = some y) :
    EvalsToInTime f x (some y) 1 :=
  ⟨⟨1, h⟩, le_rfl⟩

private def followedBy {C : Type} {f : C → Option C} {m n : ℕ} {x y : C} {z : Option C}
    (h₁ : EvalsToInTime f x (some y) m) (h₂ : EvalsToInTime f y z n) :
    EvalsToInTime f x z (n + m) :=
  EvalsToInTime.trans f m n x y z h₁ h₂

private def two {C : Type} {f : C → Option C} {x y z : C}
    (h₁ : f x = some y) (h₂ : f y = some z) :
    EvalsToInTime f x (some z) 2 :=
  followedBy (one h₁) (one h₂)

private def widen {C : Type} {f : C → Option C} {x : C} {y : Option C} {m n : ℕ}
    (h : EvalsToInTime f x y m) (hle : m ≤ n) : EvalsToInTime f x y n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hle⟩

private def runReading {A B S : Type} [Inhabited B]
    (step : S → A → S × List B) (finish : S → List B)
    (s : S) (xs : List A) (buf : List B) :
    EvalsToInTime (TM2.step (code step finish)) (reading s xs buf)
      (some (reversing A S ((run step finish s xs).reverse ++ buf) [])) (xs.length * 2 + 2) := by
  induction xs generalizing s buf with
  | nil =>
    apply two (y := cfg (some (.inr (.inl (s, none)))) (.inl none) [] buf [])
    · simp [cfg, code, memory, Sum.getLeft?, update_input]
    · simp [cfg, code, run, exec_pushWord]
  | cons a xs ih =>
    have h₁ : EvalsToInTime (TM2.step (code step finish)) (reading s (a :: xs) buf)
        (some (reading (step s a).1 xs ((step s a).2.reverse ++ buf))) 2 := by
      apply two (y := cfg (some (.inr (.inl (s, some a)))) (.inl (some a)) xs buf [])
      · simp [cfg, code, memory, Sum.getLeft?, update_input]
      · simp [cfg, code, exec_pushWord]
    simpa [run, List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.succ_mul] using
      followedBy h₁ (ih (step s a).1 ((step s a).2.reverse ++ buf))

private def runReversing {A B S : Type} [Inhabited B]
    (step : S → A → S × List B) (finish : S → List B) (buf out : List B) :
    EvalsToInTime (TM2.step (code step finish)) (reversing A S buf out)
      (some (stopped A S (buf.reverse ++ out))) (buf.length + 1) := by
  induction buf generalizing out with
  | nil =>
    apply one
    simp [cfg, code, memory, Sum.getRight?, update_buffer]
  | cons b buf ih =>
    have h₁ : EvalsToInTime (TM2.step (code step finish)) (reversing A S (b :: buf) out)
        (some (reversing A S buf (b :: out))) 1 := by
      apply one
      simp [cfg, code, memory, Sum.getRight?, update_buffer, update_output]
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using followedBy h₁ (ih (b :: out))

private theorem output_length_le {A B S : Type} (step : S → A → S × List B)
    (finish : S → List B) (c : ℕ) (hstep : ∀ s a, (step s a).2.length ≤ c)
    (hfinish : ∀ s, (finish s).length ≤ c) (s : S) (xs : List A) :
    (run step finish s xs).length ≤ c * xs.length + c := by
  induction xs generalizing s with
  | nil => simpa [run] using hfinish s
  | cons a xs ih =>
    simp only [run, List.length_cons, List.length_append, Nat.mul_succ]
    have h := ih (step s a).1
    have h' := hstep s a
    omega

theorem _root_.solution {A B S : Type} [Fintype A] [Fintype B] [Fintype S] [Inhabited B]
    (step : S → A → S × List B) (finish : S → List B) (initial : S) :
    Nonempty (TM2ComputableInPolyTime (id : List A → List A) (id : List B → List B)
      (run step finish initial)) := by
  let tm := machine step finish initial
  let c := max (Finset.univ.sup fun p : S × A => (step p.1 p.2).2.length)
    (Finset.univ.sup fun s : S => (finish s).length)
  have h₁ (s : S) (a : A) : (step s a).2.length ≤ c :=
    (Finset.le_sup (f := fun p : S × A => (step p.1 p.2).2.length)
      (Finset.mem_univ (s, a))).trans (le_max_left ..)
  have h₂ (s : S) : (finish s).length ≤ c :=
    (Finset.le_sup (f := fun s : S => (finish s).length) (Finset.mem_univ s)).trans (le_max_right ..)
  refine ⟨{
    tm := tm
    inputAlphabet := Equiv.refl A
    outputAlphabet := Equiv.refl B
    time := Polynomial.C (c + 2) * Polynomial.X + Polynomial.C (c + 3)
    outputsFun := ?_ }⟩
  intro xs
  change EvalsToInTime tm.step (initList tm (xs.map (@id A)))
    (some (haltList tm ((run step finish initial xs).map (@id B)))) _
  simp only [List.map_id]
  have hi : initList tm xs = reading initial xs ([] : List B) := by
    change (⟨some (.inl initial), .inl none, _⟩ : tm.Cfg) = _
    congr
    funext j
    cases j <;> rfl
  have hh : haltList tm (run step finish initial xs) =
      stopped A S (run step finish initial xs) := by
    change (⟨none, .inl none, _⟩ : tm.Cfg) = _
    congr
    funext j
    cases j <;> rfl
  rw [hi, hh]
  have hr := followedBy (runReading step finish initial xs [])
    (runReversing step finish ((run step finish initial xs).reverse ++ []) [])
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hr
  apply widen hr
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, id_eq]
  rw [Nat.add_mul]
  have hlen := output_length_le step finish c h₁ h₂ initial xs
  omega

end Turing.SubsequentialTransducer
