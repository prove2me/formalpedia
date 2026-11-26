-- Prove2me | solution 1 for Turing.MultiTapeTM.exists_exact_padded_configuration_readout
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T19:48:13.780799+00:00
-- url     : https://prove2.me/submissions/18911075-44e5-47d0-8c46-b14668e51b45

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Option

set_option autoImplicit false

namespace NativeCheckpointPadding

open Turing Turing.MultiTapeTM

variable {k : ℕ} {S Q : Type*} {input : List S}

inductive Phase
  | forward
  | backward
  deriving DecidableEq

instance : Finite Phase := by
  let encode : Phase → Bool := fun q => match q with
    | .forward => false
    | .backward => true
  apply Finite.of_injective encode
  intro a b
  cases a <;> cases b <;> simp [encode]

abbrev Control (Q : Type*) := Phase × Option Q

/-- An inactive worker step preserves all its fields. -/
def idle (q : Option Q) : Action k S Q :=
  ⟨.zero, fun _ => (none, .zero), none, q⟩

@[simp] theorem idle_apply (c : Cfg k S Q input) : (idle c.state).apply c = c := by
  cases c
  simp [idle, Action.apply]

/-- An already-halted worker takes an idle step. -/
noncomputable def work (M : MultiTapeTM k S Q) (q : Option Q)
    (a : Option S) (read : Fin k → Option S) : Action k S Q :=
  match q with
  | none => idle none
  | some q => M.tr q a read

theorem work_apply (M : MultiTapeTM k S Q) (c : Cfg k S Q input) :
    (work M c.state c.inputSymbol c.workTapeSymbols).apply c = M.step c := by
  cases h : c.state with
  | none => rw [step_of_halt h, work, ← h, idle_apply]
  | some q => rw [step_of_state h, work]

/-- Append a timing track. The source halt state stays stored in the
live controller so that the projection preserves every worker field. -/
def liftAction (phase : Phase) (move : SignType) (a : Action k S Q) :
    Action (k+1) S (Control Q) :=
  ⟨a.inputTape, Fin.lastCases (none, move) a.workTapes, a.output,
    some (phase, a.state)⟩

def attach (c : Cfg k S Q input) (phase : Phase) (timer : ℤ → Option S) (p : ℤ) :
    Cfg (k+1) S (Control Q) input :=
  ⟨some (phase, c.state), c.inputPos, Fin.lastCases timer c.workTapes,
    Fin.lastCases p c.workTapePos, c.output⟩

def project (c : Cfg (k+1) S (Control Q) input) : Cfg k S Q input :=
  ⟨c.state.bind Prod.snd, c.inputPos, fun i => c.workTapes i.castSucc,
    fun i => c.workTapePos i.castSucc, c.output⟩

@[simp] theorem project_attach (c : Cfg k S Q input) (phase : Phase)
    (timer : ℤ → Option S) (p : ℤ) :
    project (attach c phase timer p) = c := by
  cases c
  simp [project, attach]

theorem lift_apply (phase now : Phase) (move : SignType) (a : Action k S Q)
    (c : Cfg k S Q input) (timer : ℤ → Option S) (p : ℤ) :
    (liftAction phase move a).apply (attach c now timer p) =
      attach (a.apply c) phase timer (p + (move.cast : ℤ)) := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Action.apply, liftAction, attach]
    · simp [Action.apply, liftAction, attach]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Action.apply, liftAction, attach]
    · simp [Action.apply, liftAction, attach]
  · rfl

/-- Scan the marked interval rightward while simulating the worker. Turn
at the first blank and rewind while the worker is frozen. -/
noncomputable def transition (M : MultiTapeTM k S Q) (q : Control Q)
    (a : Option S) (s : Fin (k+1) → Option S) : Action (k+1) S (Control Q) :=
  match q.1, s (Fin.last k) with
  | .forward, some _ => liftAction .forward .pos (work M q.2 a (s ∘ Fin.castSucc))
  | .forward, none => liftAction .backward .neg (idle q.2)
  | .backward, some _ => liftAction .backward .neg (idle q.2)
  | .backward, none => liftAction .forward .pos (idle q.2)

noncomputable def machine (M : MultiTapeTM k S Q) : MultiTapeTM (k+1) S (Control Q) :=
  ofTr (.forward, some M.q₀) (transition M)

@[simp] private theorem attach_read (c : Cfg k S Q input) (phase : Phase)
    (timer : ℤ → Option S) (p : ℤ) :
    (attach c phase timer p).workTapeSymbols ∘ Fin.castSucc = c.workTapeSymbols := by
  funext i
  simp [Cfg.workTapeSymbols, attach]

private theorem attach_step (M : MultiTapeTM k S Q) (c : Cfg k S Q input)
    (phase : Phase) (timer : ℤ → Option S) (p : ℤ) :
    (machine M).step (attach c phase timer p) =
      match phase, timer p with
      | .forward, some _ => attach (M.step c) .forward timer (p+1)
      | .forward, none => attach c .backward timer (p-1)
      | .backward, some _ => attach c .backward timer (p-1)
      | .backward, none => attach c .forward timer (p+1) := by
  have hs : (attach c phase timer p).state = some (phase, c.state) := rfl
  have ha : (attach c phase timer p).inputSymbol = c.inputSymbol := rfl
  have ht : (attach c phase timer p).workTapeSymbols (Fin.last k) = timer p := by
    simp [Cfg.workTapeSymbols, attach]
  rw [step_of_state hs, machine, tr_ofTr]
  cases phase <;> cases hz : timer p <;>
    simp [transition, ht, hz, ha, lift_apply, work_apply, SignType.cast, sub_eq_add_neg]

/-- The only nonblank cells occupy positions 0 through n-1. -/
def timer (mark : S) (n : ℕ) (p : ℤ) : Option S :=
  if 0 ≤ p ∧ p < (n : ℤ) then some mark else none

theorem forward_prefix (M : MultiTapeTM k S Q) (c : Cfg k S Q input)
    (mark : S) (n t : ℕ) (before : t ≤ n) :
    (machine M).runFrom (attach c .forward (timer mark n) 0) t =
      attach (M.runFrom c t) .forward (timer mark n) (t : ℤ) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ, ih (by omega), attach_step, runFrom_succ]
    have h : timer mark n (t : ℤ) = some mark := by
      simp [timer, show t < n by omega]
    rw [h]
    simp

theorem backward_prefix (M : MultiTapeTM k S Q) (c : Cfg k S Q input)
    (mark : S) (n t : ℕ) (before : t ≤ n) :
    (machine M).runFrom
        (attach c .backward (timer mark n) ((n : ℤ)-1)) t =
      attach c .backward (timer mark n) ((n : ℤ)-1-(t : ℤ)) := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [runFrom_succ, ih (by omega), attach_step]
    have h : timer mark n ((n : ℤ)-1-(t : ℤ)) = some mark := by
      unfold timer
      split
      · rfl
      · omega
    rw [h]
    change attach c .backward (timer mark n) ((n : ℤ)-1-(t : ℤ)-1) = _
    rw [show (n : ℤ)-1-(t : ℤ)-1 = (n : ℤ)-1-((t+1 : ℕ) : ℤ) by omega]

/-- Each physical round returns the timer to its starting cell and
makes exactly n worker steps. -/
theorem whole_round (M : MultiTapeTM k S Q) (c : Cfg k S Q input)
    (mark : S) (n : ℕ) :
    (machine M).runFrom (attach c .forward (timer mark n) 0) (2*n+2) =
      attach (M.runFrom c n) .forward (timer mark n) 0 := by
  have steps : 2*n+2 = (n+1)+n+1 := by omega
  rw [steps, runFrom_succ, runFrom_add, runFrom_succ, forward_prefix M c mark n n le_rfl,
    attach_step]
  have edge : timer mark n (n : ℤ) = none := by simp [timer]
  rw [edge]
  change _ = _
  rw [backward_prefix M (M.runFrom c n) mark n n le_rfl, attach_step]
  have left : (n : ℤ) - 1 - (n : ℤ) = -1 := by omega
  rw [left]
  simp [timer]

theorem rounds (M : MultiTapeTM k S Q) (c : Cfg k S Q input)
    (mark : S) (n q : ℕ) :
    (machine M).runFrom (attach c .forward (timer mark n) 0) (q*(2*n+2)) =
      attach (M.runFrom c (q*n)) .forward (timer mark n) 0 := by
  induction q with
  | zero => simp [runFrom]
  | succ q ih =>
    rw [Nat.succ_mul q (2*n+2), Nat.succ_mul q n, runFrom_add, ih, whole_round, runFrom_add]

/-- The physical trajectory contains each worker state at a known
arithmetic address, including all heads, tapes, and output. -/
theorem exact_address (M : MultiTapeTM k S Q) (c : Cfg k S Q input)
    (mark : S) {n : ℕ} (positive : 0 < n) (t : ℕ) :
    let address := (t/n)*(2*n+2)+t%n
    project ((machine M).runFrom (attach c .forward (timer mark n) 0) address) =
      M.runFrom c t := by
  dsimp only
  rw [runFrom_add, rounds, forward_prefix M _ mark n _ (Nat.mod_lt _ positive).le, project_attach,
    ← runFrom_add]
  congr 1
  rw [Nat.mul_comm, Nat.div_add_mod]

end NativeCheckpointPadding

namespace NativeCheckpointBoot

open Turing Turing.MultiTapeTM NativeCheckpointPadding

variable {k : ℕ} {S Q : Type*} {input : List S}

inductive BootState (Q : Type*)
  | scan
  | rewind
  | active (q : Control Q)

instance [Finite Q] : Finite (BootState Q) := by
  let encode : BootState Q → Option (Option (Control Q))
    | .scan => none
    | .rewind => some none
    | .active q => some (some q)
  apply Finite.of_injective encode
  intro x y same
  cases x <;> cases y <;> simp_all [encode]

def bootAction (q : BootState Q) (write : Option (Option S)) (move : SignType) :
    Action (k+1) S (BootState Q) :=
  ⟨move, Fin.lastCases (write, move) (fun _ => (none, .zero)), none, some q⟩

def liftCfg (c : Cfg (k+1) S (Control Q) input) : Cfg (k+1) S (BootState Q) input :=
  c.mapState (Option.map BootState.active)

def lowerCfg (c : Cfg (k+1) S (BootState Q) input) : Cfg (k+1) S (Control Q) input :=
  c.mapState (fun q => q.bind (fun s => match s with
    | .active q => some q
    | _ => none))

@[simp] theorem lower_lift (c : Cfg (k+1) S (Control Q) input) : lowerCfg (liftCfg c) = c := by
  cases c with
  | mk state => cases state <;> rfl

def liftAction (a : Action (k+1) S (Control Q)) : Action (k+1) S (BootState Q) :=
  ⟨a.inputTape, a.workTapes, a.output, a.state.map BootState.active⟩

@[simp] theorem liftAction_apply (a : Action (k+1) S (Control Q))
    (c : Cfg (k+1) S (Control Q) input) : (liftAction a).apply (liftCfg c) = liftCfg (a.apply c) := by
  apply Cfg.ext <;> rfl

noncomputable def transition (M : MultiTapeTM k S Q) (mark : S)
    (q : BootState Q) (a : Option S) (seen : Fin (k+1) → Option S) :
    Action (k+1) S (BootState Q) :=
  match q with
  | .scan =>
    if a.isSome then bootAction .scan (some (some mark)) .pos else bootAction .rewind none .neg
  | .rewind =>
    if (seen (Fin.last k)).isSome then bootAction .rewind none .neg
    else bootAction (.active (.forward, some M.q₀)) none .pos
  | .active state => liftAction (NativeCheckpointPadding.transition M state a seen)

noncomputable def machine (M : MultiTapeTM k S Q) (mark : S) : MultiTapeTM (k+1) S (BootState Q) :=
  ofTr .scan (transition M mark)

theorem active_step (M : MultiTapeTM k S Q) (mark : S)
    (c : Cfg (k+1) S (Control Q) input) :
    (machine M mark).step (liftCfg c) = liftCfg ((NativeCheckpointPadding.machine M).step c) := by
  cases h : c.state with
  | none =>
    rw [step_of_halt, step_of_halt h]
    simpa [liftCfg] using h
  | some q =>
    have live : (liftCfg c).state = some (.active q) := by simp [liftCfg, h]
    rw [step_of_state live, step_of_state h, machine, NativeCheckpointPadding.machine, tr_ofTr, tr_ofTr]
    exact liftAction_apply _ c

theorem active_run (M : MultiTapeTM k S Q) (mark : S)
    (c : Cfg (k+1) S (Control Q) input) (t : ℕ) :
    (machine M mark).runFrom (liftCfg c) t = liftCfg ((NativeCheckpointPadding.machine M).runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runFrom_succ, runFrom_succ, ih, active_step]

private def blankCfg (q : BootState Q) (pos : Fin (input.length+2))
    (tape : ℤ → Option S) (head : ℤ) : Cfg (k+1) S (BootState Q) input :=
  ⟨some q, pos, Fin.lastCases tape (fun _ _ => none), Fin.lastCases head (fun _ => 0), []⟩

@[simp] private theorem blankCfg_read (q : BootState Q) (pos : Fin (input.length+2))
    (tape : ℤ → Option S) (head : ℤ) :
    (blankCfg (k := k) q pos tape head).workTapeSymbols (Fin.last k) = tape head := by
  simp [Cfg.workTapeSymbols, blankCfg]

private theorem boot_apply (now next : BootState Q) (pos : Fin (input.length+2))
    (tape : ℤ → Option S) (head : ℤ) (write : Option (Option S)) (move : SignType) :
    (bootAction next write move).apply (blankCfg (k := k) now pos tape head) =
      blankCfg next (moveInputPos pos move)
        (match write with | none => tape | some s => Function.update tape head s)
        (head + (move.cast : ℤ)) := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · cases write <;> simp [Action.apply, bootAction, blankCfg]
    · simp [Action.apply, bootAction, blankCfg]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Action.apply, bootAction, blankCfg]
    · simp [Action.apply, bootAction, blankCfg]
  · rfl

private theorem timer_extend (mark : S) (t : ℕ) :
    Function.update (timer mark t) (t : ℤ) (some mark) = timer mark (t+1) := by
  funext p
  by_cases eq : p = (t : ℤ)
  · subst p
    simp [timer]
  · rw [Function.update_of_ne eq]
    have test : (0 ≤ p ∧ p < ((t+1 : ℕ) : ℤ)) ↔ 0 ≤ p ∧ p < (t : ℤ) := by omega
    simp only [timer, test]

private theorem scan_run (M : MultiTapeTM k S Q) (mark : S) (input : List S) (t : ℕ)
    (within : t ≤ input.length) :
    (machine M mark).runFrom ((machine M mark).initCfg input) t =
      blankCfg .scan ⟨t+1, by omega⟩ (timer mark t) t := by
  induction t with
  | zero =>
    change Cfg.init BootState.scan input = _
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · funext p
        simp [blankCfg, timer, show ¬ (0 ≤ p ∧ p < 0) by omega]
      · simp [blankCfg]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [blankCfg]
    · rfl
  | succ t ih =>
    rw [runFrom_succ, ih (by omega)]
    rw [step_of_state (show (blankCfg ..).state = some BootState.scan by rfl), machine, tr_ofTr]
    have read : (blankCfg (Q := Q) (k := k) .scan
        (⟨t+1, by omega⟩ : Fin (input.length+2)) (timer mark t) t).inputSymbol =
        some (input[t]'(by omega)) := by
      apply inputSymbolInner t _ (by omega)
      simp [blankCfg, Nat.add_comm]
    rw [transition, read]
    simp only [Option.isSome_some, if_true]
    rw [boot_apply]
    change blankCfg .scan _ (Function.update (timer mark t) (t : ℤ) (some mark)) _ = _
    rw [timer_extend, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    simp [SignType.cast]

private theorem scan_turn (M : MultiTapeTM k S Q) (mark : S) (input : List S) :
    (machine M mark).runFrom ((machine M mark).initCfg input) (input.length+1) =
      blankCfg .rewind ⟨input.length, by omega⟩ (timer mark input.length)
        ((input.length : ℤ)-1) := by
  rw [runFrom_succ, scan_run M mark input input.length le_rfl]
  rw [step_of_state (show (blankCfg ..).state = some BootState.scan by rfl), machine, tr_ofTr]
  have read : (blankCfg (Q := Q) (k := k) .scan
      (⟨input.length+1, by omega⟩ : Fin (input.length+2)) (timer mark input.length)
      input.length).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr rfl)
  rw [transition, read]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false]
  rw [boot_apply, moveInputPos_neg_of_ne_left _ (by intro eq; exact Nat.succ_ne_zero _ (congrArg Fin.val eq))]
  simp [SignType.cast, sub_eq_add_neg]

private theorem rewind_run (M : MultiTapeTM k S Q) (mark : S) (input : List S) (j : ℕ)
    (within : j ≤ input.length) :
    (machine M mark).runFrom ((machine M mark).initCfg input) (input.length+1+j) =
      blankCfg .rewind ⟨input.length-j, by omega⟩ (timer mark input.length)
        ((input.length : ℤ)-1-(j : ℤ)) := by
  induction j with
  | zero => simpa using scan_turn M mark input
  | succ j ih =>
    rw [← Nat.add_assoc, runFrom_succ, ih (by omega)]
    rw [step_of_state (show (blankCfg ..).state = some BootState.rewind by rfl), machine, tr_ofTr]
    rw [transition]
    have read : timer mark input.length ((input.length : ℤ)-1-(j : ℤ)) = some mark := by
      apply if_pos
      omega
    simp only [blankCfg_read, read, Option.isSome_some, if_true]
    rw [boot_apply, moveInputPos_neg_of_ne_left _ (by intro eq; have h := congrArg Fin.val eq; simp at h; omega)]
    congr 1
    simp only [SignType.cast, Nat.cast_add, Nat.cast_one]
    omega

/-- The timer occupies exactly one cell per input symbol after a
forward pass followed by a rewind. The worker still starts at its
ordinary blank-tape configuration. -/
theorem boot (M : MultiTapeTM k S Q) (mark : S) (input : List S) :
    (machine M mark).runFrom ((machine M mark).initCfg input) (2*input.length+2) =
      liftCfg (attach (M.initCfg input) .forward (timer mark input.length) 0) := by
  rw [show 2*input.length+2 = input.length+1+input.length+1 by omega,
    runFrom_succ, rewind_run M mark input input.length le_rfl]
  rw [step_of_state (show (blankCfg ..).state = some BootState.rewind by rfl), machine, tr_ofTr]
  rw [transition]
  have head : (input.length : ℤ)-1-(input.length : ℤ) = -1 := by omega
  simp only [blankCfg_read, head]
  have empty : timer mark input.length (-1) = none := by simp [timer]
  rw [empty]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false]
  rw [boot_apply, moveInputPos_pos_of_ne_right _ (by simp)]
  simp [blankCfg, liftCfg, attach, Cfg.mapState, SignType.cast]

/-- A worker configuration at time t is present at an explicit physical
index on the blank-initialized native machine. -/
theorem exact_boot_address (M : MultiTapeTM k S Q) (mark : S) (input : List S)
    (nonempty : 0 < input.length) (t : ℕ) :
    let n := input.length
    let address := (2*n+2) + (t/n)*(2*n+2) + t%n
    project (lowerCfg ((machine M mark).runFrom ((machine M mark).initCfg input) address)) =
      M.runFrom (M.initCfg input) t := by
  dsimp only
  rw [Nat.add_assoc, runFrom_add, boot, active_run, lower_lift]
  exact exact_address M (M.initCfg input) mark nonempty t

/-- Including initialization, the requested physical address is at
most four times the worker index plus the linear initialization cost. -/
theorem address_le {n : ℕ} (positive : 0 < n) (t : ℕ) :
    (2*n+2) + (t/n)*(2*n+2) + t%n ≤ (2*n+2) + 4*t := by
  have stepBudget : 2*n+2 ≤ 4*n := by omega
  have full := Nat.mul_le_mul_left (t/n) stepBudget
  have remainderBudget := Nat.le_mul_of_pos_left (t%n) (by decide : 0 < 4)
  have split : (t/n)*n+t%n = t := by rw [Nat.mul_comm, Nat.div_add_mod]
  have cost : (t/n)*(2*n+2) + t%n ≤ 4*t := by
    calc
      (t/n)*(2*n+2) + t%n ≤ (t/n)*(4*n) + 4*(t%n) := Nat.add_le_add full remainderBudget
      _ = 4*((t/n)*n+t%n) := by rw [Nat.mul_add]; ac_rfl
      _ = 4*t := by rw [split]
  omega

end NativeCheckpointBoot

universe u v

open Turing Turing.MultiTapeTM

theorem solution {k : ℕ} {S : Type u} {Q : Type v} [Finite Q]
    (worker : MultiTapeTM k S Q) (mark : S) :
    ∃ (R : Type v) (_finite : Finite R) (wrapper : MultiTapeTM (k+1) S R)
      (projectState : ∀ {input : List S}, Cfg (k+1) S R input → Cfg k S Q input),
      ∀ (input : List S), 0 < input.length → ∀ t : ℕ,
        let n := input.length
        let address := (2*n+2) + (t/n)*(2*n+2) + t%n
        projectState (wrapper.runFrom (wrapper.initCfg input) address) =
          worker.runFrom (worker.initCfg input) t ∧
        address ≤ 2*n+2+4*t := by
  refine ⟨NativeCheckpointBoot.BootState Q, inferInstance,
    NativeCheckpointBoot.machine worker mark, fun config =>
      NativeCheckpointPadding.project (NativeCheckpointBoot.lowerCfg config), ?_⟩
  intro input positive t
  exact ⟨NativeCheckpointBoot.exact_boot_address worker mark input positive t,
    NativeCheckpointBoot.address_le positive t⟩

#print axioms solution
