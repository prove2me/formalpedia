-- Prove2me | solution 1 for PvsNP.native_index_query_window_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T03:06:26.052892+00:00
-- url     : https://prove2.me/submissions/4e19b6bf-8667-4e43-adb7-271bf641a084

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace PvsNP.FixedDescBlockSummary

open Turing Turing.MultiTapeTM

variable {k : ℕ} {Γ Q : Type} {x : List Γ}

abbrev Origins (k : ℕ) := Fin k → ℤ

/-- Two work-tape regions agree in coordinates measured from their respective
block origins. The current work heads have the same displacement. -/
structure Agrees (b : ℕ) (u v : Origins k) (a c : Cfg k Γ Q x) : Prop where
  state : a.state = c.state
  inputPos : a.inputPos = c.inputPos
  head : ∀ i, a.workTapePos i - u i = c.workTapePos i - v i
  work : ∀ i (z : ℤ), -(b : ℤ) ≤ z → z ≤ b →
    a.workTapes i (u i + z) = c.workTapes i (v i + z)

private theorem Agrees.reads {b : ℕ} {u v : Origins k} {a c : Cfg k Γ Q x}
    (h : Agrees b u v a c) (within : ∀ i, |a.workTapePos i - u i| ≤ b) :
    a.workTapeSymbols = c.workTapeSymbols := by
  funext i
  have both := abs_le.mp (within i)
  have eq := h.work i (a.workTapePos i - u i) both.1 both.2
  have right : v i + (a.workTapePos i - u i) = c.workTapePos i := by
    rw [h.head i]
    omega
  rw [right,show u i + (a.workTapePos i - u i) = a.workTapePos i by omega] at eq
  exact eq

private noncomputable def selected (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x) :
    Option (Action k Γ Q) :=
  a.state.map fun q => tm.tr q a.inputSymbol a.workTapeSymbols

private theorem Agrees.selected_eq (tm : MultiTapeTM k Γ Q)
    {b : ℕ} {u v : Origins k} {a c : Cfg k Γ Q x}
    (h : Agrees b u v a c) (within : ∀ i, |a.workTapePos i - u i| ≤ b) :
    selected tm a = selected tm c := by
  have readInput : a.inputSymbol = c.inputSymbol := by
    rw [Cfg.inputSymbol_eq_inputAt,Cfg.inputSymbol_eq_inputAt,h.inputPos]
  simp [selected,h.state,readInput,h.reads within]

private theorem step_selected (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x) :
    tm.step a = (selected tm a).elim a (·.apply a) := by
  cases h : a.state with
  | none => simpa only [selected,h,Option.map_none,Option.elim_none] using
      (step_of_halt (tm := tm) h)
  | some q => simpa only [selected,h,Option.map_some,Option.elim_some] using
      (step_of_state (tm := tm) h)

private theorem Agrees.apply {b : ℕ} {u v : Origins k} {a c : Cfg k Γ Q x}
    (h : Agrees b u v a c) (e : Action k Γ Q) :
    Agrees b u v (e.apply a) (e.apply c) := by
  refine ⟨rfl,by simp only [Action.apply_inputPos,h.inputPos],?_,?_⟩
  · intro i
    simp only [Action.apply_workTapePos]
    have := h.head i
    omega
  · intro i z lo hi
    have zAt : u i + z = a.workTapePos i ↔ v i + z = c.workTapePos i := by
      have := h.head i
      omega
    simp only [Action.apply_workTapes_eq_ite,zAt,h.work i z lo hi]

/-- Run histories can begin with different output prefixes. Their next step
adds the same zero or one output symbols. -/
private theorem Agrees.step (tm : MultiTapeTM k Γ Q)
    {b : ℕ} {u v : Origins k} {a c : Cfg k Γ Q x}
    (h : Agrees b u v a c) (within : ∀ i, |a.workTapePos i - u i| ≤ b) :
    Agrees b u v (tm.step a) (tm.step c) ∧
      ∃ e : List Γ, (tm.step a).output = a.output ++ e ∧
        (tm.step c).output = c.output ++ e := by
  rw [step_selected,step_selected,←h.selected_eq tm within]
  cases selected tm a with
  | none => exact ⟨h,[],by simp,by simp⟩
  | some ac => exact ⟨h.apply ac,ac.output.toList,rfl,rfl⟩

/-- Every translated work head remains within the elapsed time of its own
starting location. This holds from arbitrary configurations. -/
theorem head_displacement_le (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x)
    (t : ℕ) (i : Fin k) :
    |(tm.runFrom a t).workTapePos i - a.workTapePos i| ≤ t := by
  induction t with
  | zero => simp [MultiTapeTM.runFrom]
  | succ t ih =>
    have adjacent := MultiTapeNTM.Step.workTapePos_le
      (step_iff.mpr rfl : tm.Step (tm.runFrom a t) _) i
    rw [runFrom_succ]
    rw [abs_le] at adjacent ih ⊢
    push_cast
    omega

/-- A block reads only the initial cells at radius b. At every step through
the block it has the same state, input head and translated work heads, writes
the same entire translated window, and appends the same output chunk. -/
theorem runFrom_agrees (tm : MultiTapeTM k Γ Q) {b : ℕ} {a c : Cfg k Γ Q x}
    (initial : Agrees b a.workTapePos c.workTapePos a c) {t : ℕ} (within : t ≤ b) :
    Agrees b a.workTapePos c.workTapePos (tm.runFrom a t) (tm.runFrom c t) ∧
      ∃ out : List Γ, (tm.runFrom a t).output = a.output ++ out ∧
        (tm.runFrom c t).output = c.output ++ out := by
  induction t with
  | zero =>
    exact ⟨initial,[],by simp [MultiTapeTM.runFrom],by simp [MultiTapeTM.runFrom]⟩
  | succ t ih =>
    obtain ⟨h,out,ha,hc⟩ := ih (Nat.le_of_succ_le within)
    have radius i : |(tm.runFrom a t).workTapePos i - a.workTapePos i| ≤ b :=
      (head_displacement_le tm a t i).trans (by exact_mod_cast Nat.le_of_succ_le within)
    obtain ⟨next,e,ja,jc⟩ := h.step tm radius
    rw [runFrom_succ,runFrom_succ]
    exact ⟨next,out ++ e,by rw [ja,ha,List.append_assoc],by rw [jc,hc,List.append_assoc]⟩

/-- Cells beyond the initial block radius are unaffected. -/
theorem runFrom_unchanged_outside (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x)
    {b t : ℕ} (within : t ≤ b) (i : Fin k) (z : ℤ)
    (outside : (b : ℤ) < |z|) :
    (tm.runFrom a t).workTapes i (a.workTapePos i + z) =
      a.workTapes i (a.workTapePos i + z) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have nowhere : a.workTapePos i + z ≠ (tm.runFrom a t).workTapePos i := by
      intro eq
      have reached : (tm.runFrom a t).workTapePos i - a.workTapePos i = z := by omega
      have h := head_displacement_le tm a t i
      rw [reached] at h
      exact (not_le_of_gt outside) (h.trans (by exact_mod_cast Nat.le_of_succ_le within))
    rw [runFrom_succ,step_selected]
    cases selected tm (tm.runFrom a t) with
    | none => exact ih (Nat.le_of_succ_le within)
    | some ac =>
      simp only [Option.elim_some,Action.apply_workTapes_eq_ite,if_neg nowhere]
      exact ih (Nat.le_of_succ_le within)

/-- A finite word of relative cells per tape, from offset `-b` to `b`. -/
def workWindow (b : ℕ) (u : Origins k) (a : Cfg k Γ Q x) :
    Fin k → Fin (2*b+1) → Option Γ :=
  fun i j => a.workTapes i (u i + ((j.val : ℤ) - b))

/-- The starting control, position, and finite initial work windows
determine the block without reference to its absolute work-head origins. -/
theorem agrees_of_workWindow {b : ℕ} {a c : Cfg k Γ Q x}
    (mode : a.state = c.state) (position : a.inputPos = c.inputPos)
    (window : workWindow b a.workTapePos a = workWindow b c.workTapePos c) :
    Agrees b a.workTapePos c.workTapePos a c := by
  refine ⟨mode,position,fun _ => by simp only [sub_self],fun i z low high => ?_⟩
  let j : Fin (2*b+1) := ⟨(z+b).toNat,by omega⟩
  have code : (j.val : ℤ) - b = z := by dsimp [j]; omega
  have reads := congrFun (congrFun window i) j
  simpa only [workWindow,code] using reads

structure Summary (k n b : ℕ) (Γ Q : Type) where
  state : Option Q
  inputPos : Fin (n+2)
  displacement : Fin k → ℤ
  cells : Fin k → Fin (2*b+1) → Option Γ
  emitted : List Γ

/-- The result is expressed only in coordinates local to the initial heads.
The emitted chunk excludes any output already present at block start. -/
noncomputable def summarize (tm : MultiTapeTM k Γ Q) (b t : ℕ) (a : Cfg k Γ Q x) :
    Summary k x.length b Γ Q :=
  let c := tm.runFrom a t
  ⟨c.state,c.inputPos,fun i => c.workTapePos i - a.workTapePos i,
    workWindow b a.workTapePos c,c.output.drop a.output.length⟩

/-- Equal finite starting windows yield equal complete finite block results. -/
theorem summarize_eq (tm : MultiTapeTM k Γ Q) {b t : ℕ} (within : t ≤ b)
    {a c : Cfg k Γ Q x} (mode : a.state = c.state) (position : a.inputPos = c.inputPos)
    (window : workWindow b a.workTapePos a = workWindow b c.workTapePos c) :
    summarize tm b t a = summarize tm b t c := by
  obtain ⟨same,out,left,right⟩ :=
    runFrom_agrees tm (agrees_of_workWindow mode position window) within
  unfold summarize
  dsimp only
  congr 1
  · exact same.state
  · exact same.inputPos
  · exact funext same.head
  · funext i j
    exact same.work i ((j.val : ℤ) - b) (by omega) (by have := j.isLt; omega)
  · rw [left,right]
    simp only [List.drop_left]

end PvsNP.FixedDescBlockSummary

namespace PvsNP.NativeQueryRadius

open Turing Turing.MultiTapeTM PvsNP.FixedDescBlockSummary

/-- Arbitrary preprocessing stores the assignment on unrestricted tapes. The query
input and its start position depend only on the chosen index. The response uses
the output produced during this phase. No restriction is made on the absolute
positions of the work heads or on the nonblank cells. -/
theorem lookup_capacity {m k r : ℕ} {Γ Q : Type} [Fintype Γ] [Fintype Q]
    (tm : MultiTapeTM k Γ Q) (word : Fin m → List Γ)
    (start : (a : Fin m → Bool) → (j : Fin m) → Cfg k Γ Q (word j))
    (q : (Fin m → Bool) → Option Q)
    (w : (Fin m → Bool) → Fin k → Fin (2*r+1) → Option Γ)
    (pos : (j : Fin m) → Fin ((word j).length+2))
    (mode : ∀ a j, (start a j).state = q a)
    (position : ∀ a j, (start a j).inputPos = pos j)
    (cells : ∀ a j, workWindow r (start a j).workTapePos (start a j) = w a)
    (decode : Fin m → List Γ → Bool)
    (correct : ∀ a j, decode j (summarize tm r r (start a j)).emitted = a j) :
    2^m ≤ (Fintype.card Q + 1) * ((Fintype.card Γ + 1)^(2*r+1))^k := by
  let key (a : Fin m → Bool) := (q a, w a)
  have inj : Function.Injective key := by
    intro a b h
    have hq : q a = q b := congrArg Prod.fst h
    have hw : w a = w b := congrArg Prod.snd h
    funext j
    have block := summarize_eq tm (b := r) (t := r) (le_refl r)
      ((mode a j).trans (hq.trans (mode b j).symm))
      ((position a j).trans (position b j).symm)
      ((cells a j).trans (hw.trans (cells b j).symm))
    rw [← correct a j, ← correct b j, block]
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective key inj

end PvsNP.NativeQueryRadius

open Turing Turing.MultiTapeTM

theorem solution {m k r : ℕ} {Γ Q : Type} [Fintype Γ] [Fintype Q]
    (tm : MultiTapeTM k Γ Q) (word : Fin m → List Γ)
    (start : (a : Fin m → Bool) → (j : Fin m) → Cfg k Γ Q (word j))
    (q : (Fin m → Bool) → Option Q)
    (w : (Fin m → Bool) → Fin k → Fin (2*r+1) → Option Γ)
    (pos : (j : Fin m) → Fin ((word j).length+2))
    (mode : ∀ a j, (start a j).state = q a)
    (position : ∀ a j, (start a j).inputPos = pos j)
    (cells : ∀ a j, (fun (i : Fin k) (v : Fin (2*r+1)) => (start a j).workTapes i
      ((start a j).workTapePos i + ((v.val : ℤ) - r))) = w a)
    (decode : Fin m → List Γ → Bool)
    (correct : ∀ a j, decode j (((tm.runFrom (start a j) r).output).drop (start a j).output.length) = a j) :
    2^m ≤ (Fintype.card Q + 1) * ((Fintype.card Γ + 1)^(2*r+1))^k :=
  PvsNP.NativeQueryRadius.lookup_capacity tm word start q w pos mode position cells decode correct
