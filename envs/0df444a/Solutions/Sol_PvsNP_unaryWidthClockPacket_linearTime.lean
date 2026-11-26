-- Prove2me | solution 1 for PvsNP.unaryWidthClockPacket_linearTime
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T17:20:29.92714+00:00
-- url     : https://prove2.me/submissions/ba9c8c67-e460-4cbe-941b-3355dc0dc1b9

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace PvsNP.EffectiveGuessing.BidiagonalClock

open Turing StateTransition Computability
private abbrev Str := List Bool

def lowDigits : ℕ → Str → Str
  | 0, _ => []
  | w+1, bits => bits.headD false :: lowDigits w bits.tail

@[simp] theorem lowDigits_length (w : ℕ) (bits : Str) : (lowDigits w bits).length = w := by
  induction w generalizing bits with
  | zero => rfl
  | succ w ih => simp [lowDigits,ih]

private def encodeLanes (bits : Str) : Str :=
  bits.flatMap (fun b => [b,false])

/-- The high flag precedes the interleaved low clock and zeroed mask lanes. -/
def clippedPacket (w : ℕ) (bits : Str) : Str :=
  (bits.drop w).any id :: encodeLanes (lowDigits w bits)

private def parse (w : ℕ) : Str → Str
  | [] => clippedPacket w []
  | false::bits => clippedPacket w bits
  | true::bits => parse (w+1) bits

def decision (w : Str) : Str := parse 0 w

theorem decision_on_unary_prefix (w : ℕ) (bits : Str) :
    decision (List.replicate w true ++ false::bits) = clippedPacket w bits := by
  suffices ∀ j, parse j (List.replicate w true ++ false::bits) = clippedPacket (j+w) bits by
    simpa [decision] using this 0
  induction w with
  | zero => intro j; rfl
  | succ w ih =>
    intro j
    simp only [List.replicate_succ,List.cons_append,parse]
    rw [ih]
    congr 1
    omega

private inductive Stack | input | width | digits | output deriving DecidableEq

private instance : Fintype Stack :=
  ⟨{.input,.width,.digits,.output},by intro s; cases s <;> simp⟩
private inductive Label | first | low | high (b : Bool) | emit (b : Bool)
  deriving DecidableEq

private instance : Fintype Label :=
  ⟨{.first,.low,.high false,.high true,.emit false,.emit true},by
    intro l
    cases l with
    | high b | emit b => cases b <;> simp
    | _ => simp⟩

private abbrev Stmt := TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
private abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

private def jump (l : Label) : Stmt := .load (fun _ => none) (.goto fun _ => l)
private def pop (s : Stack) (tail : Stmt) : Stmt := .pop s (fun _ b => b) tail
private def pushRead (s : Stack) (tail : Stmt) : Stmt := .push s (fun b => b.getD false) tail

private def code : Label → Stmt
  | .first => pop .input (.branch (fun b => b.getD false)
      (.push .width (fun _ => false) (jump .first)) (jump .low))
  | .low => pop .width (.branch Option.isSome
      (pop .input (pushRead .digits (jump .low))) (jump (.high false)))
  | .high found => pop .input (.branch Option.isSome
      (.branch (fun b => b.getD false) (jump (.high true)) (jump (.high found)))
      (jump (.emit found)))
  | .emit found => pop .digits (.branch Option.isSome
      (.push .output (fun _ => false) (pushRead .output (jump (.emit found))))
      (.push .output (fun _ => found) (.load (fun _ => none) .halt)))

private abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .first
  σ := Option Bool
  initialState := none
  m := code

private def mem (w c d o : Str) : Stack → Str
  | .input => w
  | .width => c
  | .digits => d
  | .output => o

@[simp] private theorem upd_input (w c d o a : Str) :
    Function.update (mem w c d o) .input a = mem a c d o := by
  funext k; cases k <;> rfl
@[simp] private theorem upd_width (w c d o a : Str) :
    Function.update (mem w c d o) .width a = mem w a d o := by
  funext k; cases k <;> rfl
@[simp] private theorem upd_digits (w c d o a : Str) :
    Function.update (mem w c d o) .digits a = mem w c a o := by
  funext k; cases k <;> rfl
@[simp] private theorem upd_output (w c d o a : Str) :
    Function.update (mem w c d o) .output a = mem w c d a := by
  funext k; cases k <;> rfl

private def cfg (l : Option Label) (w c d o : Str) : Cfg := ⟨l,none,mem w c d o⟩
private abbrev Step := TM2.step code
private abbrev Trace := EvalsToInTime Step
private def one {x y : Cfg} (h : Step x = some y) : Trace x (some y) 1 :=
  ⟨⟨1,h⟩,le_rfl⟩
private def join {x y z : Cfg} {m n : ℕ} (h : Trace x (some y) m) (j : Trace y (some z) n) :
    Trace x (some z) (m+n) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans _ m n x y (some z) h j
private def weaken {x y : Cfg} {m n : ℕ} (h : Trace x (some y) m) (le : m ≤ n) :
    Trace x (some y) n := ⟨h.toEvalsTo,h.steps_le_m.trans le⟩

private def emitRun (d out : Str) (high : Bool) :
    Trace (cfg (some (.emit high)) [] [] d out)
      (some (cfg none [] [] [] (high::(encodeLanes d.reverse++out)))) (d.length+1) := by
  induction d generalizing out with
  | nil => exact one (by simp [cfg,code,jump,pop,pushRead,mem,encodeLanes])
  | cons b d ih =>
    have step : Trace (cfg (some (.emit high)) [] [] (b::d) out)
        (some (cfg (some (.emit high)) [] [] d (b::false::out))) 1 :=
      one (by simp [cfg,code,jump,pop,pushRead,mem])
    simp only [List.reverse_cons,encodeLanes,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.append_assoc,List.cons_append,List.nil_append]
    exact weaken (join step (ih (b::false::out))) (by simp only [List.length_cons]; omega)

private def highRun (bits d : Str) (found : Bool) :
    Trace (cfg (some (.high found)) bits [] d [])
      (some (cfg (some (.emit (found || bits.any id))) [] [] d [])) (bits.length+1) := by
  induction bits generalizing found with
  | nil => exact one (by simp [cfg,code,jump,pop,mem])
  | cons b bits ih =>
    have step : Trace (cfg (some (.high found)) (b::bits) [] d [])
        (some (cfg (some (.high (found || b))) bits [] d [])) 1 :=
      one (by cases b <;> simp [cfg,code,jump,pop,mem])
    simp only [List.any_cons,id_eq,← Bool.or_assoc]
    exact weaken (join step (ih (found || b))) (by simp only [List.length_cons]; omega)

private def lowRun (w : ℕ) (bits d : Str) :
    Trace (cfg (some .low) bits (List.replicate w false) d [])
      (some (cfg (some (.high false)) (bits.drop w) [] ((lowDigits w bits).reverse++d) [])) (w+1) := by
  induction w generalizing bits d with
  | zero => exact one (by simp [cfg,code,jump,pop,mem,lowDigits])
  | succ w ih =>
    have step : Trace (cfg (some .low) bits (List.replicate (w+1) false) d [])
        (some (cfg (some .low) bits.tail (List.replicate w false) (bits.headD false::d) [])) 1 :=
      one (by cases bits <;> simp [cfg,code,jump,pop,pushRead,mem,List.replicate_succ])
    have shape : bits.tail.drop w = bits.drop (w+1) := by cases bits <;> simp
    have done := join step (ih bits.tail (bits.headD false::d))
    rw [shape] at done
    simp only [lowDigits,List.reverse_cons,List.append_assoc,List.singleton_append]
    exact weaken done (by omega)

private def finishRun (w : ℕ) (bits : Str) :
    Trace (cfg (some .low) bits (List.replicate w false) [] [])
      (some (cfg none [] [] [] (clippedPacket w bits))) (2*w+bits.length+3) := by
  have low := lowRun w bits []
  simp only [List.append_nil] at low
  have high := highRun (bits.drop w) (lowDigits w bits).reverse false
  simp only [Bool.false_or] at high
  have emit := emitRun (lowDigits w bits).reverse [] ((bits.drop w).any id)
  simp only [List.reverse_reverse,List.append_nil, List.length_reverse,lowDigits_length] at emit
  have done := join (join low high) emit
  refine weaken done ?_
  rw [List.length_drop]
  omega

private def parseRun (w : ℕ) (bits : Str) :
    Trace (cfg (some .first) bits (List.replicate w false) [] [])
      (some (cfg none [] [] [] (parse w bits))) (2*w+3*bits.length+4) := by
  induction bits generalizing w with
  | nil =>
    have step : Trace (cfg (some .first) [] (List.replicate w false) [] [])
        (some (cfg (some .low) [] (List.replicate w false) [] [])) 1 :=
      one (by simp [cfg,code,jump,pop,mem])
    exact weaken (join step (finishRun w [])) (by simp only [List.length_nil]; omega)
  | cons b bits ih =>
    cases b with
    | false =>
      have step : Trace (cfg (some .first) (false::bits) (List.replicate w false) [] [])
          (some (cfg (some .low) bits (List.replicate w false) [] [])) 1 :=
        one (by simp [cfg,code,jump,pop,mem])
      exact weaken (join step (finishRun w bits)) (by simp only [List.length_cons]; omega)
    | true =>
      have step : Trace (cfg (some .first) (true::bits) (List.replicate w false) [] [])
          (some (cfg (some .first) bits (List.replicate (w+1) false) [] [])) 1 :=
        one (by simp [cfg,code,jump,pop,mem,List.replicate_succ])
      exact weaken (join step (ih (w+1))) (by simp only [List.length_cons]; omega)

private theorem init_eq (w : Str) : initList machine w = cfg (some .first) w [] [] [] := by
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext k; cases k <;> rfl

private theorem halt_eq (bits : Str) : haltList machine bits = cfg none [] [] [] bits := by
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext k; cases k <;> rfl

theorem decision_machine :
    ∃ M : TM2ComputableInTime (id : Str → Str) (id : Str → Str) decision,
      ∀ n, M.time n = 3*n+4 := by
  refine ⟨⟨⟨machine,Equiv.refl Bool,Equiv.refl Bool⟩,fun n => 3*n+4,?_⟩,fun _ => rfl⟩
  intro w
  change TM2OutputsInTime machine (w.map id) (some ((decision w).map id)) (3*w.length+4)
  simp only [List.map_id]
  unfold TM2OutputsInTime
  change Trace (initList machine w) (some (haltList machine (decision w))) _
  rw [init_eq w,halt_eq (decision w)]
  simpa only [List.replicate_zero,Nat.mul_zero,Nat.zero_add,decision] using parseRun 0 w

private theorem lowDigits_eq_padded (w : ℕ) (bits : Str) :
    lowDigits w bits = bits.take w ++ List.replicate (w - bits.length) false := by
  induction w generalizing bits with
  | zero => simp [lowDigits]
  | succ w ih =>
    cases bits with
    | nil =>
      simp only [lowDigits,List.headD_nil,List.tail_nil,ih]
      simp [List.replicate_succ]
    | cons b bits =>
      simp only [lowDigits,List.headD_cons,List.tail_cons,ih,List.take_succ_cons,List.length_cons,
        Nat.add_sub_add_right,List.cons_append]

theorem decision_canonical (w : ℕ) (bits : Str) :
    decision (List.replicate w true ++ false :: bits) =
      (bits.drop w).any id ::
        ((bits.take w ++ List.replicate (w - bits.length) false).flatMap
          (fun b => [b, false])) := by
  simp only [decision_on_unary_prefix,clippedPacket,encodeLanes,lowDigits_eq_padded]

end PvsNP.EffectiveGuessing.BidiagonalClock

open Turing Computability

theorem solution :
  ∃ (f : List Bool → List Bool)
    (M : TM2ComputableInTime (id : List Bool → List Bool) (id : List Bool → List Bool) f),
    (∀ n : ℕ, M.time n = 3 * n + 4) ∧
    ∀ (w : ℕ) (bits : List Bool),
      f (List.replicate w true ++ false :: bits) =
        (bits.drop w).any id ::
          ((bits.take w ++ List.replicate (w - bits.length) false).flatMap
            (fun b => [b, false])) := by
  obtain ⟨M, hM⟩ := PvsNP.EffectiveGuessing.BidiagonalClock.decision_machine
  exact ⟨_, M, hM, PvsNP.EffectiveGuessing.BidiagonalClock.decision_canonical⟩
