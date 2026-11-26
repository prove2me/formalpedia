-- Prove2me | solution 1 for ReplayVerification.no_mismatch_after_deterministic_restart
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T20:04:29.059847+00:00
-- url     : https://prove2.me/submissions/2f181dc2-c805-4a79-8959-cdef8f177320

import Mathlib

set_option autoImplicit false

namespace TerminalSafety

variable {S : Type*}

/-- A time-indexed inductive certificate excluding bad states at the
terminal time. Earlier bad states may be transient. -/
def Valid (step : S → S) (initial : S) (bad : S → Prop) (T : ℕ)
    (I : ℕ → S → Prop) : Prop :=
  I 0 initial ∧
  (∀ t < T, ∀ x, I t x → I (t+1) (step x)) ∧
  (∀ x, I T x → ¬ bad x)

theorem advance {step : S → S} {T : ℕ} {I : ℕ → S → Prop}
    (closed : ∀ t < T, ∀ x, I t x → I (t+1) (step x))
    (t d : ℕ) (within : t+d ≤ T) {x : S} (included : I t x) :
    I (t+d) (step^[d] x) := by
  induction d with
  | zero => simpa using included
  | succ d ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact closed (t+d) (by omega) _ (ih (by omega))

theorem includes_orbit {step : S → S} {initial : S} {bad : S → Prop}
    {T : ℕ} {I : ℕ → S → Prop} (valid : Valid step initial bad T I)
    {t : ℕ} (before : t ≤ T) : I t (step^[t] initial) := by
  simpa only [Nat.zero_add] using
    advance valid.2.1 0 t (by simpa only [Nat.zero_add] using before) valid.1

theorem excludes_backward_bad {step : S → S} {initial : S} {bad : S → Prop}
    {T : ℕ} {I : ℕ → S → Prop} (valid : Valid step initial bad T I)
    {t : ℕ} (before : t ≤ T) {x : S} (included : I t x) :
    ¬ bad (step^[T-t] x) := by
  have atEnd := advance valid.2.1 t (T-t) (by omega) included
  have address : t+(T-t) = T := by omega
  rw [address] at atEnd
  exact valid.2.2 _ atEnd

/-- Reachability of the single genuine run at the indicated time. -/
def orbit (step : S → S) (initial : S) (t : ℕ) (x : S) : Prop :=
  x = step^[t] initial

/-- A state's own remaining trajectory does not lead to terminal badness. -/
def escapesBad (step : S → S) (bad : S → Prop) (T t : ℕ) (x : S) : Prop :=
  ¬ bad (step^[T-t] x)

theorem orbit_valid {step : S → S} {initial : S} {bad : S → Prop} {T : ℕ}
    (safe : ¬ bad (step^[T] initial)) : Valid step initial bad T (orbit step initial) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro t _ x hx
    change x = step^[t] initial at hx
    change step x = step^[t+1] initial
    rw [hx, Function.iterate_succ_apply']
  · intro x hx
    change x = step^[T] initial at hx
    rwa [hx]

theorem escapesBad_valid {step : S → S} {initial : S} {bad : S → Prop} {T : ℕ}
    (safe : ¬ bad (step^[T] initial)) : Valid step initial bad T (escapesBad step bad T) := by
  refine ⟨by simpa [escapesBad] using safe, ?_, ?_⟩
  · intro t within x hx
    have remain : T-t = (T-(t+1))+1 := by omega
    simpa only [escapesBad, remain, Function.iterate_succ_apply] using hx
  · intro x hx
    simpa [escapesBad] using hx

theorem valid_certificate_iff {step : S → S} {initial : S} {bad : S → Prop} {T : ℕ} :
    (∃ I, Valid step initial bad T I) ↔ ¬ bad (step^[T] initial) := by
  constructor
  · rintro ⟨I, valid⟩
    exact valid.2.2 _ (includes_orbit valid le_rfl)
  · intro safe
    exact ⟨_, orbit_valid safe⟩

/-- Every valid certificate lies between forward reachability and the
complement of backward reachability at every time through the horizon. -/
theorem certificate_bounds {step : S → S} {initial : S} {bad : S → Prop}
    {T : ℕ} {I : ℕ → S → Prop} (valid : Valid step initial bad T I)
    {t : ℕ} (within : t ≤ T) (x : S) :
    (orbit step initial t x → I t x) ∧ (I t x → escapesBad step bad T t x) := by
  refine ⟨?_, excludes_backward_bad valid within⟩
  intro hx
  change x = step^[t] initial at hx
  rw [hx]
  exact includes_orbit valid within

end TerminalSafety

namespace ReplaySafety

variable {Input Work Result : Type*}

structure Driver (Input Work Result : Type*) where
  init : Input → Work
  next : Work → Work
  halt : Work → Bool
  report : Work → Result
  successor : Input → Input

inductive State (Input Work Result : Type*)
  | first (i : Input) (worker : Work)
  | replay (i : Input) (claimed : Result) (worker : Work)
  | bad

def step [DecidableEq Result] (driver : Driver Input Work Result) :
    State Input Work Result → State Input Work Result
  | .first i worker =>
    if driver.halt worker then .replay i (driver.report worker) (driver.init i)
    else .first i (driver.next worker)
  | .replay i claim worker =>
    if driver.halt worker then
      if driver.report worker = claim then
        .first (driver.successor i) (driver.init (driver.successor i))
      else .bad
    else .replay i claim (driver.next worker)
  | .bad => .bad

/-- A fragment of the original computation up to its first halt. -/
def PrefixUntilHalt (driver : Driver Input Work Result) (i : Input) (n : ℕ) (worker : Work) : Prop :=
  worker = driver.next^[n] (driver.init i) ∧
  ∀ t < n, driver.halt (driver.next^[t] (driver.init i)) = false

theorem prefix_zero (driver : Driver Input Work Result) (i : Input) :
    PrefixUntilHalt driver i 0 (driver.init i) := ⟨rfl, fun _ impossible => (Nat.not_lt_zero _ impossible).elim⟩

theorem prefix_succ (driver : Driver Input Work Result) {i : Input} {n : ℕ} {worker : Work}
    (proof : PrefixUntilHalt driver i n worker) (live : driver.halt worker = false) :
    PrefixUntilHalt driver i (n+1) (driver.next worker) := by
  refine ⟨by rw [proof.1, Function.iterate_succ_apply'], ?_⟩
  intro t before
  rcases (Nat.lt_succ_iff.mp before).lt_or_eq with early | equal
  · exact proof.2 t early
  · simpa only [equal, ← proof.1] using live

/-- Two runs from the same state that stop at their first halt stop at
the same index and state. No common runtime bound is required. -/
theorem equal_first_halts (driver : Driver Input Work Result) {i : Input}
    {m n : ℕ} {a b : Work} (p : PrefixUntilHalt driver i m a) (q : PrefixUntilHalt driver i n b)
    (stoppedA : driver.halt a = true) (stoppedB : driver.halt b = true) :
    m = n ∧ a = b := by
  have atMost : m ≤ n := by
    by_contra! late
    have live := p.2 n late
    rw [← q.1, stoppedB] at live
    contradiction
  have atLeast : n ≤ m := by
    by_contra! late
    have live := q.2 m late
    rw [← p.1, stoppedA] at live
    contradiction
  have time : m = n := Nat.le_antisymm atMost atLeast
  exact ⟨time, by rw [p.1, q.1, time]⟩

def consistent (driver : Driver Input Work Result) : State Input Work Result → Prop
  | .first i worker => ∃ t, PrefixUntilHalt driver i t worker
  | .replay i claim worker =>
      (∃ t stopped, PrefixUntilHalt driver i t stopped ∧ driver.halt stopped = true ∧
        driver.report stopped = claim) ∧
      (∃ t, PrefixUntilHalt driver i t worker)
  | .bad => False

theorem consistent_step [DecidableEq Result] (driver : Driver Input Work Result)
    {s : State Input Work Result} (good : consistent driver s) :
    consistent driver (step driver s) := by
  cases s with
  | first i worker =>
    obtain ⟨t, pref⟩ := good
    cases h : driver.halt worker with
    | false => simpa only [step, h, Bool.false_eq_true, if_false, consistent]
        using (show ∃ n, PrefixUntilHalt driver i n (driver.next worker) from ⟨t+1, prefix_succ driver pref h⟩)
    | true =>
      simp only [step, h, if_true, consistent]
      exact ⟨⟨t,worker,pref,h,rfl⟩,⟨0,prefix_zero driver i⟩⟩
  | replay i claim worker =>
    obtain ⟨⟨elapsed,stopped,prev,halted,reported⟩,⟨t,pref⟩⟩ := good
    cases h : driver.halt worker with
    | false =>
      simp only [step, h, Bool.false_eq_true, if_false, consistent]
      exact ⟨⟨elapsed,stopped,prev,halted,reported⟩,⟨t+1,prefix_succ driver pref h⟩⟩
    | true =>
      have same : stopped = worker := (equal_first_halts driver prev pref halted h).2
      have report : driver.report worker = claim := same ▸ reported
      simp only [step, h, if_true, report, consistent]
      exact ⟨0,prefix_zero driver (driver.successor i)⟩
  | bad => exact good.elim

/-- Replaying a deterministic worker to its first halt is safe even
when runtime varies with the input or the worker never halts. -/
theorem never_bad [DecidableEq Result] (driver : Driver Input Work Result) (i : Input) (T : ℕ) :
    (step driver)^[T] (.first i (driver.init i)) ≠ State.bad := by
  have valid : TerminalSafety.Valid (step driver) (.first i (driver.init i))
      (· = State.bad) T (fun _ s => consistent driver s) := by
    refine ⟨⟨0,prefix_zero driver i⟩, fun _ _ _ => consistent_step driver, ?_⟩
    intro s good bad
    subst s
    exact good
  exact TerminalSafety.valid_certificate_iff.mp ⟨_,valid⟩

end ReplaySafety

theorem solution {Input Work Result : Type*} [DecidableEq Result]
    (init : Input → Work) (next : Work → Work) (halt : Work → Bool)
    (report : Work → Result) (successor : Input → Input)
    (first : Input) (T : ℕ) :
    let Control := (Input × Work) ⊕ ((Input × Result × Work) ⊕ Unit)
    let step : Control → Control := fun
      | .inl (i, w) =>
        if halt w then .inr (.inl (i, report w, init i)) else .inl (i, next w)
      | .inr (.inl (i, claim, w)) =>
        if halt w then
          if report w = claim then .inl (successor i, init (successor i)) else .inr (.inr ())
        else .inr (.inl (i, claim, next w))
      | .inr (.inr ()) => .inr (.inr ())
    step^[T] (.inl (first, init first)) ≠ .inr (.inr ()) := by
  intro Control step
  let driver : ReplaySafety.Driver Input Work Result := ⟨init, next, halt, report, successor⟩
  let decode : Control → ReplaySafety.State Input Work Result := fun
    | .inl (i, w) => .first i w
    | .inr (.inl (i, claim, w)) => .replay i claim w
    | .inr (.inr ()) => .bad
  have agrees (c : Control) : decode (step c) = ReplaySafety.step driver (decode c) := by
    rcases c with ⟨i, w⟩ | ⟨i, claim, w⟩ | u
    · by_cases h : halt w
      all_goals simp [step, decode, driver, ReplaySafety.step, h]
    · by_cases h : halt w
      · by_cases same : report w = claim
        all_goals simp [step, decode, driver, ReplaySafety.step, h, same]
      · simp [step, decode, driver, ReplaySafety.step, h]
    · cases u
      rfl
  have transfer (t : ℕ) (c : Control) :
      decode (step^[t] c) = (ReplaySafety.step driver)^[t] (decode c) := by
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', agrees, ih]
  intro bad
  have decoded := congrArg decode bad
  rw [transfer] at decoded
  exact ReplaySafety.never_bad driver first T decoded

#print axioms solution
