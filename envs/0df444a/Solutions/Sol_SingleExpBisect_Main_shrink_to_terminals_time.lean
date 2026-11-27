-- Prove2me | solution 1 for SingleExpBisect.Main.shrink_to_terminals_time
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:50:07.898059+00:00
-- url     : https://prove2.me/submissions/daed6e01-cdb6-4e2c-a547-b8ff157f0713

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Encodings
import Definitions.Def_SingleExpBisect_Main_Graphs

set_option autoImplicit false

open Turing

namespace BitStacks

abbrev Mem (K : Type) := K → List Bool

/-- One straight-line, finitely branching stack instruction. Each read sees one bit or EOF. -/
inductive Action (K Λ : Type) where
  | stop (label : Option Λ)
  | peek (k : K) (next : Option Bool → Action K Λ)
  | drop (k : K) (next : Action K Λ)
  | push (k : K) (b : Bool) (next : Action K Λ)

namespace Action
variable {K Λ : Type} [DecidableEq K]

def run : Action K Λ → Mem K → Option Λ × Mem K
  | .stop l, m => (l,m)
  | .peek k f, m => (f (m k).head?).run m
  | .drop k a, m => a.run (Function.update m k (m k).tail)
  | .push k b a, m => a.run (Function.update m k (b::m k))

def compile : Action K Λ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool)
  | .stop (some l) => .load (fun _ => none) (.goto (fun _ => l))
  | .stop none => .load (fun _ => none) .halt
  | .peek k f => .peek k (fun _ v => v) (.branch Option.isNone (f none).compile
        (.branch (fun v => v.getD false) (f (some true)).compile (f (some false)).compile))
  | .drop k a => .pop k (fun v _ => v) a.compile
  | .push k b a => .push k (fun _ => b) a.compile

theorem correct (a : Action K Λ) (s : Option Bool) (m : Mem K) :
    TM2.stepAux a.compile s m = ⟨(a.run m).1, none, (a.run m).2⟩ := by
  induction a generalizing s m with
  | stop l => cases l <;> rfl
  | drop k a ih => exact ih _ _
  | push k b a ih => exact ih _ _
  | peek k f ih =>
    cases h : (m k).head? with
    | none => simpa [compile,run,TM2.stepAux,h] using ih none none m
    | some b => cases b <;> simp [compile,run,TM2.stepAux,h,ih]

end Action

variable {K Λ : Type} [DecidableEq K] [Fintype K] [Fintype Λ]
/-- An ordinary bundled Mathlib machine, with Boolean alphabets on every stack. -/
def machine (entry : Λ) (io : K) (code : Λ → Action K Λ) : TM2ComputableAux Bool Bool where
  tm := { K := K, k₀ := io, k₁ := io, Γ := fun _ => Bool, Λ := Λ,
          main := entry, σ := Option Bool, initialState := none, m := fun l => (code l).compile }
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

def isolated (k : K) (s : List Bool) : Mem K :=
  (initList (machine () k (fun _ => .stop none)).tm s).stk

/-- Exactly n bit-stack instructions from a live or halted configuration. -/
inductive Path (code : Λ → Action K Λ) : Option Λ → Mem K → ℕ → Option Λ → Mem K → Prop where
  | refl (l m) : Path code l m 0 l m
  | step {l m} : Path code (some l) m 1 ((code l).run m).1 ((code l).run m).2
  | join {a m b n z p k h} : Path code a m k b n → Path code b n h z p → Path code a m (k+h) z p

theorem Path.outputs {entry io code src dst t bound} (h : Path (K:=K) (Λ:=Λ)
    code (some entry) (isolated (K:=K) io src) t none (isolated (K:=K) io dst)) (hb : t ≤ bound) :
    HMBinPacking.OutputsWithin (machine entry io code) src dst bound := by
  let M := machine entry io code
  let c (l m) : M.tm.Cfg := ⟨l,none,m⟩
  have sem {l m j r n} (p : Path code l m j r n) :
      (flip bind M.tm.step)^[j] (some (c l m)) = some (c r n) := by
    induction p with
    | refl => rfl
    | @step l m =>
      change some (TM2.stepAux (code l).compile none m) = _
      rw [Action.correct]; rfl
    | @join _ _ _ _ _ _ k g _ _ a b => rw [Nat.add_comm k g,Function.iterate_add_apply,a,b]
  have init : initList M.tm (src.map M.inputAlphabet.symm) = c (some entry) (isolated (K:=K) io src) := by
    have eqmap : src.map M.inputAlphabet.symm = src := List.map_id _
    rw [eqmap]
    rfl
  have halt : haltList M.tm (dst.map M.outputAlphabet.symm) = c none (isolated (K:=K) io dst) := by
    have eqmap : dst.map M.outputAlphabet.symm = dst := List.map_id _
    rw [eqmap]
    rfl
  refine ⟨⟨⟨t,?_⟩,hb⟩⟩
  change (flip bind M.tm.step)^[t] (some (initList M.tm (src.map M.inputAlphabet.symm))) =
    some (haltList M.tm (dst.map M.outputAlphabet.symm))
  rw [init,halt]; exact sem h

end BitStacks

namespace BitStacks
open Action
variable {K K' Λ Λ' : Type} [DecidableEq K] [DecidableEq K']

/-- Install a hardware operation in a larger finite machine by renaming its
registers injectively and its labels. No additional steps are charged. -/
def Action.rename (r : K ↪ K') (l : Option Λ → Option Λ') : Action K Λ → Action K' Λ'
  | .stop x => .stop (l x)
  | .peek k f => .peek (r k) (fun b => (f b).rename r l)
  | .drop k a => .drop (r k) (a.rename r l)
  | .push k b a => .push (r k) b (a.rename r l)

def Agrees (r : K ↪ K') (m : Mem K) (n : Mem K') : Prop := ∀ k, n (r k) = m k

private theorem sameUpdate (r : K ↪ K') {m n} (h : Agrees r m n) (k : K) (s : List Bool) :
    Agrees r (Function.update m k s) (Function.update n (r k) s) := by
  intro i; by_cases e : i=k
  · subst i; simp
  · rw [Function.update_of_ne e,Function.update_of_ne (r.injective.ne e)]
    exact h i

theorem renameRun (a : Action K Λ) (r : K ↪ K') (l : Option Λ → Option Λ')
    (m : Mem K) (n : Mem K') (h : Agrees r m n) :
    let small := a.run m
    let large := (a.rename r l).run n
    large.1=l small.1 ∧ Agrees r small.2 large.2 ∧
      ∀ k, (∀ j, r j ≠ k) → large.2 k = n k := by
  induction a generalizing m n with
  | stop z => exact ⟨rfl,h,fun _ _ => rfl⟩
  | peek k f ih =>
    simp only [Action.rename,Action.run,h k]
    exact ih _ m n h
  | drop k a ih =>
    obtain ⟨hl,ha,ho⟩ := ih _ _ (sameUpdate r h k (m k).tail)
    simp only [Action.rename,Action.run,h k]
    refine ⟨hl,ha,?_⟩
    intro p hp;rw [ho p hp,Function.update_of_ne (Ne.symm (hp k))]
  | push k b a ih =>
    obtain ⟨hl,ha,ho⟩ := ih _ _ (sameUpdate r h k (b::m k))
    simp only [Action.rename,Action.run,h k]
    refine ⟨hl,ha,?_⟩
    intro p hp; rw [ho p hp,Function.update_of_ne (Ne.symm (hp k))]

/-- A finite trace can be assembled as a subroutine. The caller may replace a
halt by a continuation and every unused caller register is preserved. -/
theorem Path.rename {program : Λ → Action K Λ} {i m t o n}
    (p : Path program i m t o n) (r : K ↪ K') (label : Λ → Λ') (exit : Option Λ')
    (code : Λ' → Action K' Λ')
    (implementation : ∀ j, code (label j) =
      (program j).rename r (fun q => q.elim exit (fun v => some (label v))))
    (before : Mem K') (h : Agrees r m before) :
    ∃ after : Mem K', Path code (i.elim exit (fun v => some (label v))) before t
        (o.elim exit (fun v => some (label v))) after ∧ Agrees r n after ∧
      ∀ k, (∀ j, r j ≠ k) → after k = before k := by
  induction p generalizing before with
  | refl l m => exact ⟨before,Path.refl _ _,h,fun _ _ => rfl⟩
  | @step j m =>
    have info := renameRun (program j) r (fun q => q.elim exit (fun v => some (label v))) m before h
    have st := Path.step (code:=code) (l:=label j) (m:=before)
    rw [implementation] at st
    exact ⟨_,info.1 ▸ st, info.2⟩
  | @join _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
    obtain ⟨middle,p₁,a₁,rest₁⟩ := h₁ _ h
    obtain ⟨after,p₂,a₂,rest₂⟩ := h₂ _ a₁
    exact ⟨after,p₁.join p₂,a₂,fun k hk => (rest₂ k hk).trans (rest₁ k hk)⟩

end BitStacks

namespace BitStacks

/-- A program fragment has a distinguished entry. Its only exit is the absent label. -/
structure Block (K : Type) where
  L : Type
  [finiteL : Fintype L]
  entry : L
  code : L → Action K L
attribute [instance] Block.finiteL

namespace Block
variable {K : Type} [DecidableEq K]
def Run (p : Block K) (m : Mem K) (steps : ℕ) (n : Mem K) := Path p.code (some p.entry) m steps none n

def embed {L M : Type} (place : L → M) (exit : Option M) (p : Action K L) : Action K M :=
  p.rename (Function.Embedding.refl K) (fun q => q.elim exit (fun l => some (place l)))

theorem Run.install {p : Block K} {m n : Mem K} {t : ℕ} (h : p.Run m t n)
    {M : Type} (place : p.L → M) (exit : Option M) (code : M → Action K M)
    (installed : ∀ l, code (place l) = embed place exit (p.code l)) :
    Path code (some (place p.entry)) m t exit n := by
  obtain ⟨v,trace,agree,_⟩ := h.rename (Function.Embedding.refl K) place exit code installed m (fun _ => rfl)
  have eqn : v = n := funext (fun k => agree k)
  exact eqn ▸ trace

def atom (a : Action K Unit) : Block K := ⟨Unit,(),fun _ => a⟩

theorem atom_run (a : Action K Unit) (m n : Mem K) (h : a.run m = (none,n)) :
    (atom a).Run m 1 n := by
  have st := Path.step (code:=(atom a).code) (l:=()) (m:=m)
  change Path _ _ _ 1 (a.run m).1 (a.run m).2 at st
  simpa only [Run,atom,h] using st

def thenDo (p q : Block K) : Block K where
  L := p.L ⊕ q.L
  entry := Sum.inl p.entry
  code := Sum.elim (fun l => embed Sum.inl (some (Sum.inr q.entry)) (p.code l))
    (fun l => embed Sum.inr none (q.code l))

infixr:55 " >>> " => thenDo

theorem seq {p q : Block K} {m u n : Mem K} {a b : ℕ} (h : p.Run m a u) (g : q.Run u b n) :
    (p >>> q).Run m (a+b) n :=
  (h.install Sum.inl (some (Sum.inr q.entry)) (p >>> q).code (fun _ => rfl)).join
    (g.install Sum.inr none (p >>> q).code (fun _ => rfl))

def choice (k : K) (test : Option Bool → Bool) (yes no : Block K) : Block K where
  L := Option (yes.L ⊕ no.L)
  entry := none
  code
    | none => .peek k fun v => .stop (some (some (if test v then .inl yes.entry else .inr no.entry)))
    | some (.inl l) => embed (fun x => some (.inl x)) none (yes.code l)
    | some (.inr l) => embed (fun x => some (.inr x)) none (no.code l)

theorem yes {k : K} {test : Option Bool → Bool} {p q : Block K} {m n : Mem K} {t : ℕ}
    (ok : test (m k).head? = true) (h : p.Run m t n) : (choice k test p q).Run m (1+t) n := by
  let b := choice k test p q
  have s := Path.step (code:=b.code) (l:=none) (m:=m)
  change Path b.code _ _ 1 _ _ at s
  simp only [b,choice,Action.run,ok,if_true] at s
  exact s.join (h.install (fun x => some (Sum.inl x)) none b.code (fun _ => rfl))

theorem no {k : K} {test : Option Bool → Bool} {p q : Block K} {m n : Mem K} {t : ℕ}
    (bad : test (m k).head? = false) (h : q.Run m t n) : (choice k test p q).Run m (1+t) n := by
  let b := choice k test p q
  have s := Path.step (code:=b.code) (l:=none) (m:=m)
  simp only [b,choice,Action.run,bad,Bool.false_eq_true,if_false] at s
  exact s.join (h.install (fun x => some (Sum.inr x)) none b.code (fun _ => rfl))

def loop (k : K) (test : Option Bool → Bool) (body : Block K) : Block K where
  L := Option body.L
  entry := none
  code
    | none => .peek k fun v => .stop (if test v then some (some body.entry) else none)
    | some l => embed some (some none) (body.code l)

theorem done {k : K} {test : Option Bool → Bool} {p : Block K} {m : Mem K}
    (h : test (m k).head? = false) : (loop k test p).Run m 1 m := by
  have s := Path.step (code:=(loop k test p).code) (l:=none) (m:=m)
  simpa only [Run,loop,Action.run,h,Bool.false_eq_true,if_false] using s

theorem more {k : K} {test : Option Bool → Bool} {p : Block K} {m u n : Mem K} {a b : ℕ}
    (ok : test (m k).head? = true) (h : p.Run m a u) (g : (loop k test p).Run u b n) :
    (loop k test p).Run m (1+a+b) n := by
  let l := loop k test p
  have s := Path.step (code:=l.code) (l:=none) (m:=m)
  simp only [l,loop,Action.run,ok,if_true] at s
  exact (s.join (h.install some (some none) l.code (fun _ => rfl))).join g

def Within (p : Block K) (m : Mem K) (t : ℕ) (n : Mem K) := ∃ a ≤ t, p.Run m a n

theorem Run.within {p : Block K} {m n : Mem K} {a : ℕ} (h : p.Run m a n) : p.Within m a n := ⟨a,le_rfl,h⟩
theorem Within.mono {p : Block K} {m n : Mem K} {a b : ℕ} (h : p.Within m a n) (bound : a ≤ b) :
    p.Within m b n := by obtain ⟨t,l,r⟩ := h; exact ⟨t,l.trans bound,r⟩
theorem Within.seq {p q : Block K} {m u n : Mem K} {a b : ℕ} (h : p.Within m a u) (g : q.Within u b n) :
    (p >>> q).Within m (a+b) n := by
  obtain ⟨s,x,r⟩ := h; obtain ⟨t,y,f⟩ := g
  exact ⟨s+t,Nat.add_le_add x y,Block.seq r f⟩

theorem Within.outputs [Fintype K] {p : Block K} (io : K) (src out : List Bool) {t : ℕ}
    (h : p.Within (isolated io src) t (isolated io out)) :
    HMBinPacking.OutputsWithin (machine p.entry io p.code) src out t := by
  obtain ⟨_,le,r⟩ := h; exact Path.outputs r le
end Block
end BitStacks

namespace BitStacks.Block
variable {K : Type} [DecidableEq K]

abbrev setWord (m : Mem K) (k : K) (v : List Bool) : Mem K := Function.update m k v
def skip : Block K := atom (.stop none)
def pop (a : K) : Block K := atom (.drop a (.stop none))
def push (a : K) (b : Bool) : Block K := atom (.push a b (.stop none))
def shift (a b : K) : Block K := atom (.peek a fun v => .drop a (.push b (v.getD false) (.stop none)))
def present (x : Option Bool) := x.isSome
def marked (x : Option Bool) := x.getD false
def drain (a : K) := loop a present (pop a)
def transfer (a b : K) := loop a present (shift a b)

theorem pop_run (a : K) (m : Mem K) : (pop a).Run m 1 (setWord m a (m a).tail) := atom_run _ _ _ rfl
theorem push_run (a : K) (b : Bool) (m : Mem K) :
    (push a b).Run m 1 (setWord m a (b::m a)) := atom_run _ _ _ rfl
theorem skip_run (m : Mem K) : (skip (K:=K)).Run m 1 m := atom_run _ _ _ rfl
theorem shift_run (a b : K) (ab : a ≠ b) (m : Mem K) (x : Bool) (xs : List Bool)
    (read : m a = x::xs) :
    (shift a b).Run m 1 (setWord (setWord m a xs) b (x::m b)) := by
  apply atom_run
  simp [shift,Action.run,read,Function.update_of_ne (Ne.symm ab)]

/-- Executes one physical pass through a stack, preserving the other registers. -/
theorem transfer_run (a b : K) (ab : a ≠ b) (m : Mem K) (xs : List Bool) (eqn : m a = xs) :
    (transfer a b).Run m (2*xs.length+1) (setWord (setWord m a []) b (xs.reverse++m b)) := by
  induction xs generalizing m with
  | nil =>
    have stop := done (k:=a) (test:=present) (p:=shift a b) (m:=m) (by simp [present,eqn])
    have em : setWord (setWord m a []) b (List.reverse ([]:List Bool) ++ m b) = m := by
      funext i; by_cases hb : i=b
      · subst i; simp
      · by_cases ha : i=a
        · subst i; simp [Function.update_of_ne ab,eqn]
        · simp [Function.update_of_ne hb,Function.update_of_ne ha]
    rw [em]; exact stop
  | cons x xs ih =>
    let u := setWord (setWord m a xs) b (x::m b)
    have hm : u a = xs := by simp [u,Function.update_of_ne ab]
    have hb : u b = x::m b := by simp [u]
    have go := more (k:=a) (test:=present) (p:=shift a b) (m:=m)
      (by simp [present,eqn]) (shift_run a b ab m x xs eqn) (ih u hm)
    have endeq : setWord (setWord u a []) b (xs.reverse++u b) =
        setWord (setWord m a []) b ((x::xs).reverse++m b) := by
      funext i; by_cases e : i=b
      · subst i; simp [hb,List.reverse_cons,List.append_assoc]
      · by_cases f : i=a
        · subst i; simp [Function.update_of_ne ab]
        · simp [u,Function.update_of_ne e,Function.update_of_ne f]
    rw [endeq] at go
    have eqt : 1+1+(2*xs.length+1) = 2*(x::xs).length+1 := by simp; omega
    rw [eqt] at go; exact go

/-- The guard is tested once at the end and once for every consumed token. -/
theorem while_list {a : K} {test : Option Bool → Bool} {p : Block K}
    {S : Type} (m : List Bool → S → Mem K) (step : Bool → S → S)
    (cost : Bool → S → ℕ) (xs : List Bool) (s : S)
    (stop : ∀ st, test ((m [] st) a).head? = false)
    (go : ∀ x ∈ xs, ∀ rest st, test ((m (x::rest) st) a).head? = true ∧
      p.Run (m (x::rest) st) (cost x st) (m rest (step x st))) :
    ∃ t, (loop a test p).Run (m xs s) t (m [] (xs.foldl (fun u b => step b u) s)) ∧
      t = (xs.foldl (fun v x => (v.1+1+cost x v.2,step x v.2)) (0,s)).1+1 := by
  have run (ys : List Bool) (u : S) (acc : ℕ) (sub : ∀ x ∈ ys, x ∈ xs) :
      ∃ t, (loop a test p).Run (m ys u) t (m [] (ys.foldl (fun st x => step x st) u)) ∧
        acc+t = (ys.foldl (fun v x => (v.1+1+cost x v.2,step x v.2)) (acc,u)).1+1 := by
    induction ys generalizing u acc with
    | nil => exact ⟨1,done (stop u),rfl⟩
    | cons x ys ih =>
      obtain ⟨on,one⟩ := go x (sub x (by simp)) ys u
      obtain ⟨t,r,e⟩ := ih (step x u) (acc+1+cost x u) (fun v hv => sub v (by simp [hv]))
      refine ⟨1+cost x u+t,more on one r,?_⟩
      change acc+(1+cost x u+t)=_
      simpa only [List.foldl_cons,Nat.add_assoc] using e
  obtain ⟨t,r,e⟩ := run xs s 0 (fun _ h => h)
  exact ⟨t,r,by simpa using e⟩

end BitStacks.Block

namespace SingleExpBisect.ShrinkMachine
open BitStacks Block
inductive R | input | width | bits | units | temp | base | count | saved | out | mark deriving DecidableEq
open R
instance : Fintype R := ⟨{input,width,bits,units,temp,base,count,saved,out,mark},by intro r; cases r <;> decide⟩
structure S where
  input : List Bool := []
  width : List Bool := []
  bits : List Bool := []
  units : List Bool := []
  temp : List Bool := []
  base : List Bool := []
  count : List Bool := []
  saved : List Bool := []
  out : List Bool := []
  mark : List Bool := []
def S.mem (s : S) : Mem R
  | .input => s.input
  | .width => s.width
  | .bits => s.bits
  | .units => s.units
  | .temp => s.temp
  | .base => s.base
  | .count => s.count
  | .saved => s.saved
  | .out => s.out
  | .mark => s.mark
@[simp] theorem mem_input (s : S) : s.mem .input = s.input := rfl
@[simp] theorem put_input (s : S) (x : List Bool) : setWord s.mem .input x = ({s with input := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_width (s : S) : s.mem .width = s.width := rfl
@[simp] theorem put_width (s : S) (x : List Bool) : setWord s.mem .width x = ({s with width := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_bits (s : S) : s.mem .bits = s.bits := rfl
@[simp] theorem put_bits (s : S) (x : List Bool) : setWord s.mem .bits x = ({s with bits := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_units (s : S) : s.mem .units = s.units := rfl
@[simp] theorem put_units (s : S) (x : List Bool) : setWord s.mem .units x = ({s with units := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_temp (s : S) : s.mem .temp = s.temp := rfl
@[simp] theorem put_temp (s : S) (x : List Bool) : setWord s.mem .temp x = ({s with temp := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_base (s : S) : s.mem .base = s.base := rfl
@[simp] theorem put_base (s : S) (x : List Bool) : setWord s.mem .base x = ({s with base := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_count (s : S) : s.mem .count = s.count := rfl
@[simp] theorem put_count (s : S) (x : List Bool) : setWord s.mem .count x = ({s with count := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_saved (s : S) : s.mem .saved = s.saved := rfl
@[simp] theorem put_saved (s : S) (x : List Bool) : setWord s.mem .saved x = ({s with saved := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_out (s : S) : s.mem .out = s.out := rfl
@[simp] theorem put_out (s : S) (x : List Bool) : setWord s.mem .out x = ({s with out := x} : S).mem := by funext i; cases i <;> rfl
@[simp] theorem mem_mark (s : S) : s.mem .mark = s.mark := rfl
@[simp] theorem put_mark (s : S) (x : List Bool) : setWord s.mem .mark x = ({s with mark := x} : S).mem := by funext i; cases i <;> rfl
end SingleExpBisect.ShrinkMachine

namespace SingleExpBisect.ShrinkMachine
open BitStacks Block R
def yesPush {L : Type} (f : Bool) (k : R) (b : Bool) (rest : Action R L) : Action R L :=
  if f then .push k b rest else rest
def stash (f : Bool) (w xs : List Bool) := if f then w.reverse++xs else xs
def enc (w : List Bool) := List.replicate w.length true ++ false::w
def headStep (f : Bool) : Block R :=
  atom (.drop input (.push width true (yesPush f saved true (.stop none))))
def splitStep (f : Bool) : Block R := atom (.drop input (yesPush f saved false (.stop none)))
def digitStep (f v : Bool) : Block R :=
  atom (.peek input fun x => .drop width (.drop input
    (yesPush v bits (x.getD false) (yesPush f saved (x.getD false) (.stop none)))))
def header (f : Bool) := loop input marked (headStep f)
def digits (f v : Bool) := loop width present (digitStep f v)
def readWord (f v : Bool) := header f >>> splitStep f >>> digits f v

private theorem oneHead (f) (s : S) (tail : List Bool) :
    (headStep f).Run ({s with input := true::tail} : S).mem 1
      ({s with input:=tail,width:=true::s.width,saved:=stash f [true] s.saved} : S).mem := by
  cases f <;> apply atom_run <;> simp [yesPush,Action.run,stash]

private theorem readHeader (f) (j : ℕ) (tail : List Bool) (s : S) :
    (header f).Run ({s with input:=List.replicate j true ++ false::tail} : S).mem (2*j+1)
      ({s with input:=false::tail,width:=List.replicate j true ++ s.width, saved:=stash f (List.replicate j true) s.saved} : S).mem := by
  induction j generalizing s with
  | zero =>
    simpa [header,stash] using (done (k:=input) (test:=marked) (p:=headStep f)
      (m:=({s with input:=false::tail} : S).mem) (by simp [marked]))
  | succ j ih =>
    let rest := List.replicate j true ++ false::tail
    let u := {s with width:=true::s.width,saved:=stash f [true] s.saved}
    have one := oneHead f s rest
    have after := ih u
    have tr := more (k:=input) (test:=marked) (p:=headStep f) (m:=({s with input:=true::rest} : S).mem)
      (by simp [marked]) one after
    have tm : 1+1+(2*j+1)=2*(j+1)+1 := by omega
    rw [tm] at tr
    have join (x : List Bool) : List.replicate j true ++ true::x = List.replicate (j+1) true ++ x := by
      rw [List.replicate_add]; simp [List.append_assoc]
    have extend (x : List Bool) : List.replicate j true ++ true::x = true::(List.replicate j true ++ x) :=
      (join x).trans (by rw [List.replicate_succ]; rfl)
    cases f <;> simpa [rest,u,stash,header,List.replicate_succ,List.reverse_cons,List.append_assoc,extend] using tr

private theorem oneDigit (f v) (s : S) (b : Bool) (xs ys : List Bool) :
    (digitStep f v).Run ({s with input:=b::xs,width:=true::ys} : S).mem 1
      ({s with input:=xs,width:=ys,bits:=stash v [b] s.bits,saved:=stash f [b] s.saved} : S).mem := by
  cases f <;> cases v <;> apply atom_run <;> simp [yesPush,Action.run,stash]

private theorem readDigits (f v) (w tail : List Bool) (s : S) :
    (digits f v).Run ({s with input:=w++tail,width:=List.replicate w.length true} : S).mem
      (2*w.length+1) ({s with input:=tail,width:=[],bits:=stash v w s.bits,saved:=stash f w s.saved} : S).mem := by
  induction w generalizing s with
  | nil =>
    simpa [digits,stash] using (done (k:=width) (test:=present) (p:=digitStep f v)
      (m:=({s with input:=tail,width:=[]} : S).mem) (by simp [present]))
  | cons x xs ih =>
    let u := {s with bits:=stash v [x] s.bits,saved:=stash f [x] s.saved}
    have one := oneDigit f v s x (xs++tail) (List.replicate xs.length true)
    have tr := more (k:=width) (test:=present) (p:=digitStep f v) (by simp [present]) one (ih u)
    have tm : 1+1+(2*xs.length+1) = 2*(x::xs).length+1 := by simp; omega
    rw [tm] at tr
    cases f <;> cases v <;> simpa [u,stash,digits,List.replicate_succ,List.reverse_cons,List.append_assoc] using tr

/-- Physically parse one self-delimiting word, optionally retaining a reversed copy
of its encoding and/or its digits. The bound counts original TM2 transitions. -/
theorem read_run (f v : Bool) (w tail : List Bool) (s : S) (empty : s.width=[]) :
    (readWord f v).Run ({s with input:=enc w ++ tail} : S).mem (4*w.length+3)
      ({s with input:=tail,width:=[],bits:=stash v w s.bits,saved:=stash f (enc w) s.saved} : S).mem := by
  let u := {s with width:=List.replicate w.length true, saved:=stash f (List.replicate w.length true) s.saved}
  let z := {u with saved:=stash f [false] u.saved}
  have a := readHeader f w.length (w++tail) s
  have b : (splitStep f).Run ({u with input:=false::(w++tail)} : S).mem 1
      ({z with input:=w++tail}:S).mem := by
    cases f <;> apply atom_run <;> simp [yesPush,Action.run,z,stash]
  have c := readDigits f v w tail z
  have a' : (header f).Run ({s with input:=enc w ++ tail} : S).mem (2*w.length+1)
      ({u with input:=false::(w++tail)} : S).mem := by simpa [enc,u,empty,List.append_assoc] using a
  have comp := Block.seq a' (Block.seq b c)
  have tm : 2*w.length+1+(1+(2*w.length+1))=4*w.length+3 := by omega
  rw [tm] at comp
  cases f <;> simpa [readWord,u,z,stash,enc,List.reverse_append,List.reverse_cons,List.append_assoc] using comp
end SingleExpBisect.ShrinkMachine

namespace SingleExpBisect.ShrinkMachine
open BitStacks Block R

def marks (n : ℕ) := List.replicate n true
def twiceStep : Block R := atom (.drop units (.push temp true (.push temp true (.stop none))))
def scatter := loop units present twiceStep
def addBit : Block R := choice bits marked (push units true) skip
def binaryStep := scatter >>> transfer temp units >>> addBit >>> pop bits
def decode := loop bits present binaryStep
def value (u : ℕ) (xs : List Bool) := xs.foldl (fun z b => 2*z+b.toNat) u

private theorem appendMarks (a b : ℕ) : marks a ++ marks b = marks (a+b) := (List.replicate_add ..).symm
private theorem two_marks (n : ℕ) : true::true::marks n = marks (n+2) := by simp [marks,List.replicate_succ]
private theorem one_marks (n : ℕ) : true::marks n = marks (n+1) := by simp [marks,List.replicate_succ]

theorem scatter_run (u v) (s : S) :
    scatter.Run ({s with units:=marks u,temp:=marks v} : S).mem (2*u+1)
      ({s with units:=[],temp:=marks (2*u+v)} : S).mem := by
  induction u generalizing v with
  | zero => simpa [scatter,marks] using (done (k:=units) (test:=present) (p:=twiceStep)
      (m:=({s with units:=[],temp:=marks v} : S).mem) (by simp [present]))
  | succ u ih =>
    let m := ({s with units:=marks (u+1),temp:=marks v} : S)
    have one : twiceStep.Run m.mem 1 ({s with units:=marks u,temp:=marks (v+2)} : S).mem := by
      apply atom_run; simp [m,Action.run,marks,List.replicate_succ]
    have run := more (k:=units) (test:=present) (p:=twiceStep) (m:=m.mem)
      (by simp [m,present,marks,List.replicate_succ]) one (ih (v+2))
    have cost : 1+1+(2*u+1) = 2*(u+1)+1 := by omega
    have sum : 2*u+(v+2) = 2*(u+1)+v := by omega
    rw [cost,sum] at run; exact run

private theorem extra_run (b : Bool) (tail : List Bool) (u : ℕ) (s : S) :
    addBit.Run ({s with bits:=b::tail,units:=marks u}:S).mem 2
      ({s with bits:=b::tail,units:=marks (u+b.toNat)}:S).mem := by
  cases b with
  | false =>
    apply no (k:=bits) (test:=marked) (t:=1) (p:=push units true) (q:=skip) (by simp [marked])
    exact skip_run _
  | true =>
    apply yes (k:=bits) (test:=marked) (t:=1) (p:=push units true) (q:=skip) (by simp [marked])
    simpa [Bool.toNat,one_marks] using (push_run units true ({s with bits:=true::tail,units:=marks u}:S).mem)

theorem binary_run (b) (tail : List Bool) (u : ℕ) (s : S) :
    binaryStep.Run ({s with bits:=b::tail,units:=marks u,temp:=[]}:S).mem (6*u+5)
      ({s with bits:=tail,units:=marks (2*u+b.toNat),temp:=[]}:S).mem := by
  let w : S := {s with bits:=b::tail}
  let r : S := {w with units:=[],temp:=marks (2*u)}
  have a := scatter_run u 0 w
  have f := transfer_run temp units (by decide) r.mem (marks (2*u)) rfl
  have t : (transfer temp units).Run r.mem (2*(2*u)+1) ({w with temp:=[],units:=marks (2*u)}:S).mem := by
    simpa [r,marks] using f
  have e := extra_run b tail (2*u) ({s with temp:=[]}:S)
  have z := pop_run bits ({s with temp:=[],bits:=b::tail,units:=marks (2*u+b.toNat)}:S).mem
  have tr := Block.seq (p:=scatter) (q:=transfer temp units >>> addBit >>> pop bits)
    (show scatter.Run ({s with bits:=b::tail,units:=marks u,temp:=[]} : S).mem (2*u+1) r.mem by
      simpa [r,w,marks] using a)
    (Block.seq t (Block.seq e (by simpa using z)))
  have cost : 2*u+1+(2*(2*u)+1+(2+1)) = 6*u+5 := by omega
  rw [cost] at tr; exact tr

theorem value_ge (u : ℕ) (xs : List Bool) : u ≤ value u xs := by
  induction xs generalizing u with
  | nil => exact le_rfl
  | cons b bs ih =>
    exact (show u ≤ 2*u+b.toNat by omega).trans (ih _)

theorem decode_run (xs : List Bool) (u : ℕ) (s : S) :
    decode.Within ({s with bits:=xs,units:=marks u,temp:=[]} : S).mem
      (1+xs.length*(6*value u xs+6))
      ({s with bits:=[],units:=marks (value u xs),temp:=[]} : S).mem := by
  induction xs generalizing u with
  | nil =>
    simpa [decode,value] using (done (k:=bits) (test:=present) (p:=binaryStep)
      (m:=({s with bits:=[],units:=marks u,temp:=[]} : S).mem) (by simp [present])).within
  | cons x xs ih =>
    obtain ⟨t,le,rr⟩ := ih (2*u+x.toNat)
    have one := binary_run x xs u s
    have res := more (k:=bits) (test:=present) (p:=binaryStep) (by simp [present]) one rr
    refine ⟨_,?_,res⟩
    have hu := value_ge u (x::xs)
    change u ≤ value (2*u+x.toNat) xs at hu
    change _ ≤ 1+(xs.length+1)*(6*value (2*u+x.toNat) xs+6)
    rw [Nat.add_mul,Nat.one_mul]; omega

theorem bits_value (n : ℕ) : value 0 n.bits.reverse=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n ok ih =>
    rw [Nat.bits_append_bit _ _ ok,List.reverse_cons]
    change (n.bits.reverse++[b]).foldl _ 0=_
    rw [List.foldl_append]
    change 2*value 0 n.bits.reverse+b.toNat=_
    rw [ih]; cases b <;> simp [Nat.bit] <;> omega
end SingleExpBisect.ShrinkMachine

namespace BitStacks.Block
variable {K : Type} [DecidableEq K]
def duplicateUnary (a b c : K) : Block K :=
  loop a present (atom (.drop a (.push b true (.push c true (.stop none)))))
theorem duplicate_run (a b c : K) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (n : ℕ) (m : Mem K) (start : m a = List.replicate n true) :
    (duplicateUnary a b c).Run m (2*n+1)
      (setWord (setWord (setWord m a []) b (List.replicate n true++m b)) c (List.replicate n true++m c)) := by
  let atomStep := atom (.drop a (.push b true (.push c true (.stop none))))
  induction n generalizing m with
  | zero =>
    have base := done (k:=a) (test:=present) (p:=atomStep) (m:=m) (by simp [present,start])
    have endeq : setWord (setWord (setWord m a []) b (m b)) c (m c) = m := by
      funext k; by_cases ec : k=c
      · subst k; simp
      · by_cases eb : k=b
        · subst k; simp [Function.update_of_ne bc]
        · by_cases ea : k=a
          · subst k; simp [Function.update_of_ne ac,Function.update_of_ne ab,start]
          · simp [Function.update_of_ne ec,Function.update_of_ne eb,Function.update_of_ne ea]
    simpa only [duplicateUnary,atomStep,List.replicate_zero,List.nil_append,endeq,Nat.mul_zero,Nat.zero_add] using base
  | succ n ih =>
    let s := setWord (setWord (setWord m a (List.replicate n true)) b (true::m b)) c (true::m c)
    have h (z : List Bool) : List.replicate n true ++ true::z = List.replicate (n+1) true ++z := by
      rw [List.replicate_add]; simp [List.append_assoc]
    have ea : s a = List.replicate n true := by simp [s,Function.update_of_ne ac,Function.update_of_ne ab]
    have eb : s b = true::m b := by simp [s,Function.update_of_ne bc]
    have ec : s c = true::m c := by simp [s]
    have st : atomStep.Run m 1 s := by
      apply atom_run; simp [Action.run,start,List.replicate_succ,s,Function.update_of_ne (Ne.symm ab),
        Function.update_of_ne (Ne.symm bc),Function.update_of_ne (Ne.symm ac)]
    have rr := more (k:=a) (test:=present) (p:=atomStep) (m:=m) (by simp [start,present,List.replicate_succ]) st (ih s ea)
    have ee : setWord (setWord (setWord s a []) b (List.replicate n true++s b)) c (List.replicate n true++s c) =
        setWord (setWord (setWord m a []) b (List.replicate (n+1) true++m b)) c (List.replicate (n+1) true++m c) := by
      funext k; by_cases cc : k=c
      · subst k; simp [ec,h]
      · by_cases bb : k=b
        · subst k; simp [Function.update_of_ne bc,eb,h]
        · by_cases aa : k=a
          · subst k; simp [Function.update_of_ne ac,Function.update_of_ne ab]
          · simp [s,Function.update_of_ne cc,Function.update_of_ne bb,Function.update_of_ne aa]
    have tm : 1+1+(2*n+1)=2*(n+1)+1 := by omega
    rw [ee,tm] at rr; exact rr

def consume (a b : K) : Block K := loop a present (atom (.drop a (.drop b (.stop none))))
theorem consume_run (a b : K) (dif : a≠b) (m : Mem K) (xs rest : List Bool)
    (ea : m a=List.replicate xs.length true) (eb : m b=xs++rest) :
    (consume a b).Run m (2*xs.length+1) (setWord (setWord m a []) b rest) := by
  let body := atom (.drop a (.drop b (.stop none)))
  induction xs generalizing m with
  | nil =>
    have eqn : setWord (setWord m a []) b rest=m := by
      funext k; by_cases e : k=b
      · subst k; simp [eb]
      · by_cases f : k=a
        · subst k; simp [Function.update_of_ne dif,ea]
        · simp [Function.update_of_ne e,Function.update_of_ne f]
    rw [eqn]; exact done (by simp [ea,present])
  | cons x xs ih =>
    let z := setWord (setWord m a (List.replicate xs.length true)) b (xs++rest)
    have st : body.Run m 1 z := by
      apply atom_run; simp [Action.run,ea,eb,List.replicate_succ,z,Function.update_of_ne (Ne.symm dif)]
    have ha : z a=List.replicate xs.length true := by simp [z,Function.update_of_ne dif]
    have hb : z b=xs++rest := by simp [z]
    have rr := more (k:=a) (test:=present) (p:=body) (m:=m) (by simp [present,ea,List.replicate_succ])
      st (ih z ha hb)
    have endeq : setWord (setWord z a []) b rest = setWord (setWord m a []) b rest := by
      funext k; by_cases e : k=b
      · subst k; simp
      · by_cases f : k=a
        · subst k; simp [Function.update_of_ne dif]
        · simp [z,Function.update_of_ne e,Function.update_of_ne f]
    have time : 1+1+(2*xs.length+1)=2*(x::xs).length+1 := by simp; omega
    rw [time,endeq] at rr; exact rr

theorem drain_run (a : K) (m : Mem K) (xs : List Bool) (read : m a=xs) :
    (drain a).Run m (2*xs.length+1) (setWord m a []) := by
  induction xs generalizing m with
  | nil =>
    have sm : setWord m a []=m := by rw [← read]; exact Function.update_eq_self _ _
    rw [sm]; exact done (by simp [present,read])
  | cons b xs ih =>
    let s := setWord m a xs
    have er : s a=xs := by simp [s]
    have one : (pop a).Run m 1 s := by simpa [s,read] using pop_run a m
    have rr := more (k:=a) (test:=present) (by simp [present,read]) one (ih s er)
    have eqn : setWord s a []=setWord m a [] := by simp [s,Function.update_idem]
    have time : 1+1+(2*xs.length+1)=2*(b::xs).length+1 := by simp; omega
    rw [eqn,time] at rr; exact rr
end BitStacks.Block

namespace SingleExpBisect.ShrinkMachine
open BitStacks Block R
def makeRows := duplicateUnary units base count
def refill := duplicateUnary base units temp >>> transfer temp base
def row := refill >>> consume units input >>> pop count
def matrix := makeRows >>> loop count present row >>> drain base

theorem rows_ready (n : ℕ) (s : S) :
    makeRows.Run ({s with units:=marks n,base:=[],count:=[]} : S).mem (2*n+1)
      ({s with units:=[],base:=marks n,count:=marks n} : S).mem := by
  simpa [makeRows,marks] using duplicate_run units base count (by decide) (by decide) (by decide) n
    ({s with units:=marks n,base:=[],count:=[]} : S).mem rfl

theorem refill_run (n : ℕ) (s : S) :
    refill.Run ({s with base:=marks n,units:=[],temp:=[]} : S).mem (4*n+2)
      ({s with base:=marks n,units:=marks n,temp:=[]} : S).mem := by
  let t : S := {s with base:=[],units:=marks n,temp:=marks n}
  have a : (duplicateUnary base units temp).Run ({s with base:=marks n,units:=[],temp:=[]} : S).mem (2*n+1) t.mem := by
    simpa [t,marks] using duplicate_run base units temp (by decide) (by decide) (by decide) n
      ({s with base:=marks n,units:=[],temp:=[]} : S).mem rfl
  have b := transfer_run temp base (by decide) t.mem (marks n) rfl
  have seqn := Block.seq a b
  have tm : 2*n+1+(2*n+1)=4*n+2 := by omega
  simpa [refill,t,marks,tm] using seqn

theorem row_run (xs tail : List Bool) (r : ℕ) (s : S) :
    row.Run ({s with input:=xs++tail,base:=marks xs.length,units:=[],temp:=[],count:=marks (r+1)} : S).mem
      (6*xs.length+4) ({s with input:=tail,base:=marks xs.length,units:=[],temp:=[],count:=marks r} : S).mem := by
  let u : S := {s with input:=xs++tail,count:=marks (r+1)}
  let q : S := {u with base:=marks xs.length,units:=marks xs.length,temp:=[]}
  let z : S := {q with units:=[],input:=tail}
  have a := refill_run xs.length u
  have b : (consume units input).Run q.mem (2*xs.length+1) z.mem := by
    simpa [z] using consume_run units input (by decide) q.mem xs tail rfl rfl
  have c := pop_run count z.mem
  have seqn := Block.seq a (Block.seq b c)
  have tm : 4*xs.length+2+(2*xs.length+1+1)=6*xs.length+4 := by omega
  simpa [row,u,q,z,marks,List.replicate_succ,tm] using seqn

theorem skip_rows (n : ℕ) (rows : List (List Bool)) (len : ∀ xs ∈ rows, xs.length=n)
    (tail : List Bool) (s : S) :
    (loop count present row).Run ({s with input:=rows.flatten++tail,base:=marks n,units:=[],temp:=[],count:=marks rows.length} : S).mem
      (rows.length*(6*n+5)+1) ({s with input:=tail,base:=marks n,units:=[],temp:=[],count:=[]} : S).mem := by
  induction rows with
  | nil => simpa [marks] using (done (k:=count) (test:=present) (p:=row)
      (m:=({s with input:=tail,base:=marks n,units:=[],temp:=[],count:=[]} : S).mem) (by simp [present]))
  | cons x xs ih =>
    have wl := len x (by simp)
    have a := row_run x (xs.flatten++tail) xs.length s
    rw [wl] at a
    have tr := more (k:=count) (test:=present) (by simp [present,marks,List.replicate_succ])
      a (ih (fun y hy => len y (by simp [hy])))
    have tm : 1+(6*n+4)+(xs.length*(6*n+5)+1) = (x::xs).length*(6*n+5)+1 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega
    rw [tm] at tr; simpa [List.flatten_cons,List.append_assoc] using tr

theorem matrix_run (n : ℕ) (rows : List (List Bool)) (size : rows.length = n)
    (len : ∀ xs ∈ rows, xs.length=n) (tail : List Bool) (s : S) :
    matrix.Run ({s with input:=rows.flatten++tail,units:=marks n,base:=[],count:=[],temp:=[]} : S).mem
      (6*n^2+9*n+3) ({s with input:=tail,units:=[],base:=[],count:=[],temp:=[]} : S).mem := by
  let h : S := {s with input:=rows.flatten++tail,temp:=[]}
  let z : S := {s with input:=tail,base:=marks n,units:=[],count:=[],temp:=[]}
  have a := rows_ready n h
  have b := skip_rows n rows len tail s
  rw [size] at b
  have c := drain_run base z.mem (marks n) rfl
  have tr := Block.seq a (Block.seq b c)
  have tm : 2*n+1+(n*(6*n+5)+1+(2*n+1)) = 6*n^2+9*n+3 := by
    ring
  simpa [matrix,h,z,marks,tm] using tr
end SingleExpBisect.ShrinkMachine

namespace SingleExpBisect.ShrinkMachine
open BitStacks Block R
def readNumber (remember : Bool) := readWord remember true >>> decode
def capture := loop units present (pop units >>> readWord true false)
def payload (ws : List (List Bool)) := ws.flatMap enc
def wordCost (n : ℕ) := (4*n.bits.length+3)+(1+n.bits.length*(6*n+6))

theorem number_run (f : Bool) (n : ℕ) (tail : List Bool) (s : S)
    (hw : s.width=[]) (hb : s.bits=[]) (hu : s.units=[]) (ht : s.temp=[]) :
    (readNumber f).Within ({s with input:=enc n.bits++tail}:S).mem (wordCost n)
      ({s with input:=tail,width:=[],bits:=[],units:=marks n,temp:=[],saved:=stash f (enc n.bits) s.saved}:S).mem := by
  let z : S := {s with input:=tail,width:=[],saved:=stash f (enc n.bits) s.saved}
  have a := read_run f true n.bits tail s hw
  have a' : (readWord f true).Run ({s with input:=enc n.bits++tail}:S).mem (4*n.bits.length+3)
      ({z with bits:=n.bits.reverse,units:=marks 0,temp:=[]}:S).mem := by
    simpa [z,stash,hb,hu,ht,marks] using a
  have b := decode_run n.bits.reverse 0 z
  rw [bits_value,List.length_reverse] at b
  exact a'.within.seq b

theorem capture_run (ws : List (List Bool)) (tail : List Bool) (s : S) :
    capture.Within ({s with input:=payload ws++tail,units:=marks ws.length,width:=[]} : S).mem
      (1+5*(payload ws).length)
      ({s with input:=tail,units:=[],width:=[],saved:=(payload ws).reverse++s.saved}:S).mem := by
  induction ws generalizing s with
  | nil =>
    simpa [capture,payload,marks] using (done (k:=units) (test:=present) (p:=pop units >>> readWord true false)
      (m:=({s with input:=tail,units:=[],width:=[]} : S).mem) (by simp [present])).within
  | cons x xs ih =>
    let rem := payload xs++tail
    let u : S := {s with input:=enc x++rem,units:=marks (xs.length+1),width:=[]}
    let v : S := {u with units:=marks xs.length}
    let z : S := {s with saved:=(enc x).reverse++s.saved}
    have p : (pop units).Run u.mem 1 v.mem := by
      simpa [u,v,marks,List.replicate_succ] using pop_run units u.mem
    have q := read_run true false x rem v rfl
    obtain ⟨t,ht,h⟩ := ih z
    have one : (pop units >>> readWord true false).Run u.mem (1+(4*x.length+3))
        ({z with input:=rem,units:=marks xs.length,width:=[]}:S).mem := by
      simpa [u,v,z,stash,rem] using Block.seq p q
    have r := more (k:=units) (test:=present) (m:=u.mem) (by simp [u,present,marks,List.replicate_succ]) one h
    refine ⟨1+(1+(4*x.length+3))+t,?_,?_⟩
    · change 1+(1+(4*x.length+3))+t ≤ 1+5*((enc x)++payload xs).length
      simp only [enc,List.length_append,List.length_cons,List.length_replicate]; omega
    · simpa [capture,payload,u,z,rem,List.reverse_append,List.append_assoc] using r

def copyBody : Block R := atom (.peek saved fun v => .drop saved (.drop input (.push out (v.getD false) (.stop none))))
def copyWhile := loop saved present copyBody
theorem copyWhile_run (xs ys tail : List Bool) (s : S) (len : xs.length=ys.length) :
    copyWhile.Run ({s with saved:=xs,input:=ys++tail}:S).mem (2*xs.length+1)
      ({s with saved:=[],input:=tail,out:=xs.reverse++s.out}:S).mem := by
  induction xs generalizing s ys with
  | nil =>
    have ynil : ys=[] := List.length_eq_zero_iff.mp len.symm
    subst ys
    simpa [copyWhile] using (done (k:=saved) (test:=present)
      (p:=copyBody)
      (m:=({s with input:=tail,saved:=[]}:S).mem) (by simp [present]))
  | cons b xs ih =>
    cases ys with
    | nil => simp at len
    | cons y ys =>
      have ll : xs.length=ys.length := by simpa using len
      let u : S := {s with input:=y::(ys++tail),saved:=b::xs}
      let v : S := {s with out:=b::s.out}
      let body := copyBody
      have st : body.Run u.mem 1 ({v with input:=ys++tail,saved:=xs}:S).mem := by
        apply atom_run; simp [Action.run,u,v]
      have rr := more (k:=saved) (test:=present) (m:=u.mem) (by simp [u,present]) st (ih ys v ll)
      have time : 1+1+(2*xs.length+1) = 2*(b::xs).length+1 := by simp; omega
      rw [time] at rr
      simpa [u,v,copyWhile,List.reverse_cons,List.append_assoc] using rr
end SingleExpBisect.ShrinkMachine

namespace SingleExpBisect.ShrinkMachine
open BitStacks Block R
def emit := transfer out saved >>> transfer saved input >>> push input true
def select := choice input present (drain input >>> emit) (drain out >>> push input false)
theorem emit_run (x : List Bool) (s : S) :
    emit.Run ({s with out:=x,saved:=[],input:=[]}:S).mem (4*x.length+3)
      ({s with input:=true::x,out:=[],saved:=[]}:S).mem := by
  let a : S := {s with out:=x,saved:=[],input:=[]}
  let b : S := {s with out:=[],saved:=x.reverse,input:=[]}
  let c : S := {s with out:=[],saved:=[],input:=x}
  have p : (transfer out saved).Run a.mem (2*x.length+1) b.mem := by
    simpa [a,b] using transfer_run out saved (by decide) a.mem x rfl
  have q : (transfer saved input).Run b.mem (2*x.length+1) c.mem := by
    simpa [b,c] using transfer_run saved input (by decide) b.mem x.reverse rfl
  have t := Block.seq p (Block.seq q (push_run input true c.mem))
  have tm : 2*x.length+1+(2*x.length+1+1)=4*x.length+3 := by omega
  simpa [emit,a,c,tm] using t

def pickWord (x y : List Bool) := if y.isEmpty then [false] else true::x
theorem select_run (x y : List Bool) (s : S) :
    select.Within ({s with out:=x,saved:=[],input:=y}:S).mem (2*y.length+4*x.length+5)
      ({s with input:=pickWord x y,out:=[],saved:=[]}:S).mem := by
  let a : S := {s with out:=x,saved:=[],input:=y}
  cases y with
  | nil =>
    have t := drain_run out a.mem x rfl
    have p := push_run input false ({a with out:=[]}:S).mem
    simp only [put_out] at t
    have c := Block.seq t p
    have r := no (k:=input) (test:=present) (p:=drain input >>> emit) (m:=a.mem) (by simp [a,present]) c
    refine ⟨1+(2*x.length+1+1),?_,?_⟩
    · change 1+(2*x.length+1+1) ≤ 2*0+4*x.length+5; omega
    · simpa [a,pickWord,select] using r
  | cons b ys =>
    have d := drain_run input a.mem (b::ys) rfl
    have e := emit_run x s
    simp only [put_input] at d
    have c := Block.seq d e
    have r := yes (k:=input) (test:=present) (q:=drain out >>> push input false) (m:=a.mem)
      (by simp [a,present]) c
    refine ⟨1+(2*(b::ys).length+1+(4*x.length+3)),?_,?_⟩
    · show 1+(2*(b::ys).length+1+(4*x.length+3)) ≤ _; omega
    · simpa [a,pickWord,select] using r

def compareAndSelect := copyWhile >>> select
theorem compare_run (x y : List Bool) (le : x.length ≤ y.length) (s : S) :
    compareAndSelect.Within ({s with out:=[],saved:=x.reverse,input:=y}:S).mem
      (6*x.length+2*y.length+6)
      ({s with out:=[],saved:=[],input:=if x.length=y.length then [false] else true::x}:S).mem := by
  let left := y.take x.length
  let tail := y.drop x.length
  have len : x.reverse.length=left.length := by simp [left,Nat.min_eq_left le]
  have c := copyWhile_run x.reverse left tail ({s with out:=[]}:S) len
  have e := select_run x tail s
  have cc : copyWhile.Run ({s with out:=[],saved:=x.reverse,input:=y}:S).mem (2*x.length+1)
      ({s with input:=tail,saved:=[],out:=x}:S).mem := by
    simpa [left,tail] using c
  have d := cc.within.seq e
  have cost : 2*x.length+1+(2*tail.length+4*x.length+5) ≤ 6*x.length+2*y.length+6 := by
    simp [tail]; omega
  have value : pickWord x tail = if x.length=y.length then [false] else true::x := by
    by_cases same : x.length=y.length
    · simp [pickWord,tail,same]
    · have smaller : x.length < y.length := by omega
      have ne : tail.isEmpty = false := by cases h : tail with
        | nil => have l : tail.length=0 := by simp [h]
                 simp [tail] at l; omega
        | cons => rfl
      simp [pickWord,same,ne]
  rw [← value]
  exact d.mono cost

end SingleExpBisect.ShrinkMachine

namespace SingleExpBisect.ShrinkMachine
open BitStacks Block R

def program := readNumber false >>> matrix >>> readWord false false >>> readNumber true >>> capture >>> compareAndSelect
def machine := BitStacks.machine program.entry input program.code
def setCode (x : ℕ) (ws : List (List Bool)) := enc x.bits ++ payload ws
def inputCode (n : ℕ) (rows : List (List Bool)) (k x : ℕ) (ws : List (List Bool)) (y : List Bool) :=
  enc n.bits ++ rows.flatten ++ enc k.bits ++ setCode x ws ++ y
def budget (n k x : ℕ) (ws : List (List Bool)) (y : List Bool) :=
  wordCost n + ((6*n^2+9*n+3) + ((4*k.bits.length+3) + (wordCost x +
    ((1+5*(payload ws).length) + (6*(setCode x ws).length+2*y.length+6)))))

theorem program_runs (n : ℕ) (rows : List (List Bool)) (k x : ℕ) (ws : List (List Bool)) (y : List Bool)
    (nr : rows.length=n) (rows_ok : ∀ l∈rows,l.length=n) (len : ws.length=x) (le : (setCode x ws).length ≤ y.length) :
    HMBinPacking.OutputsWithin machine (inputCode n rows k x ws y)
      (if (setCode x ws).length=y.length then [false] else true::setCode x ws) (budget n k x ws y) := by
  let z : S := {}
  let sx := setCode x ws
  let rest := sx++y
  let krest := enc k.bits++rest
  let nrst := rows.flatten++krest
  let w := enc x.bits
  have a := number_run false n nrst z rfl rfl rfl rfl
  have b := matrix_run n rows nr rows_ok krest z
  have c := read_run false false k.bits rest z rfl
  have d := number_run true x (payload ws++y) z rfl rfl rfl rfl
  have e := capture_run ws y ({z with saved:=w.reverse}:S)
  have f := compare_run sx y le z
  let state (i : List Bool) : S := {input:=i}
  have e' : capture.Within ({input:=payload ws++y,units:=marks x,saved:=w.reverse}:S).mem
      (1+5*(payload ws).length) ({input:=y,saved:=sx.reverse}:S).mem := by
    simpa [z,w,sx,setCode,len,List.reverse_append] using e
  have d' : (readNumber true).Within (state rest).mem (wordCost x)
      ({input:=payload ws++y,units:=marks x,saved:=w.reverse}:S).mem := by
    simpa [state,rest,sx,setCode,w,stash,z,List.append_assoc] using d
  have c' : (readWord false false).Within (state krest).mem (4*k.bits.length+3) (state rest).mem := by
    simpa [krest,state,z,stash] using c.within
  have b' : matrix.Within ({input:=nrst,units:=marks n}:S).mem (6*n^2+9*n+3) (state krest).mem := by
    simpa [z,nrst,state] using b.within
  have a' : (readNumber false).Within (state (inputCode n rows k x ws y)).mem (wordCost n)
      ({input:=nrst,units:=marks n}:S).mem := by
    simpa [state,nrst,krest,rest,sx,inputCode,z,stash,List.append_assoc] using a
  have trace := a'.seq (b'.seq (c'.seq (d'.seq (e'.seq f))))
  have same (v : List Bool) : isolated (K:=R) input v = (state v).mem := by
    funext q; cases q <;> rfl
  let ans := if sx.length=y.length then [false] else true::sx
  have tr : program.Within (isolated input (inputCode n rows k x ws y)) (budget n k x ws y) (isolated input ans) := by
    rw [same,same]
    exact trace
  exact tr.outputs _ _ _
end SingleExpBisect.ShrinkMachine

open scoped Classical
namespace SingleExpBisect.ShrinkMachine
open SingleExpBisect.Main MinBisectFPT ExponomialAssortment.FPTAS

private theorem naturalLength (n : ℕ) : (encodeNat n).length ≤ 2*n+1 := by
  have h : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  simpa [encodeNat, ← Nat.size_eq_bits_len, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using Nat.add_le_add (Nat.add_le_add h h) (le_refl 1)

private theorem flatLength {α β : Type} (l : List α) (f : α → List β) (bound : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ bound) :
    (l.flatMap f).length ≤ l.length * bound := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    omega

theorem inputLength {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    (encodeInput G k).length ≤ n*n + 2*n + 2*k + 2 := by
  classical
  have h := flatLength (List.finRange n)
    (fun u => (List.finRange n).map fun v => decide (G.Adj u v)) n (by simp)
  simp only [List.length_finRange] at h
  simp only [encodeInput, List.length_append]
  have hn := naturalLength n
  have hk := naturalLength k
  omega

theorem setLength {n : ℕ} (A : Finset (Fin n)) :
    (encodeSet A).length ≤ (n+1)*(2*n+1) := by
  classical
  let vertices := (List.finRange n).filter (· ∈ A)
  have h := flatLength vertices (fun v => encodeNat v.val) (2*n+1)
    (fun v _ => (naturalLength v.val).trans (by have hh := v.isLt; omega))
  have hv : vertices.length ≤ n := (List.length_filter_le _ _).trans_eq List.length_finRange
  have ha := naturalLength A.card
  have hc : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hm := Nat.mul_le_mul_right (2*n+1) hv
  change (encodeNat A.card ++ vertices.flatMap _).length ≤ _
  rw [List.length_append, Nat.succ_mul]
  omega

theorem smallBag {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n))
    (small : B.card ≤ 4*k+1) : IsEdgeUnbreakable G Finset.univ B (2*k) k := by
  intro A _ _
  have card := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at card
  omega

private lemma comp_closed {n : ℕ} {G : SimpleGraph (Fin n)} {X K : Finset (Fin n)}
    (hc : IsComponent G X K) {u v : Fin n} (hu : u ∈ K) (hv : v ∈ X) (ha : G.Adj u v) : v ∈ K := by
  classical
  have H : (G.induce ((K : Set (Fin n)) ∪ {v})).Connected := by
    apply SimpleGraph.connected_induce_union hc.2.1.preconnected _ hu (Set.mem_singleton v) ha
    exact SimpleGraph.Preconnected.of_subsingleton
  have HH : (G.induce (↑(insert v K) : Set (Fin n))).Connected := by
    have hset : (↑(insert v K) : Set (Fin n)) = (K : Set _) ∪ {v} := by ext; simp
    rw [hset]
    exact H
  have hx : insert v K ⊆ X := Finset.insert_subset hv hc.1
  have he := hc.2.2 (insert v K) (Finset.subset_insert _ _) hx HH
  exact he ▸ Finset.mem_insert_self v K
private lemma nbr_mem {n : ℕ} (H : SimpleGraph (Fin n)) (K : Finset (Fin n)) (v : Fin n) :
    v ∈ nbr H K ↔ v ∉ K ∧ ∃ u ∈ K, H.Adj u v := by simp [nbr]

private lemma nbr_component {n : ℕ} (H : SimpleGraph (Fin n)) (B K : Finset (Fin n))
    (hk : IsComponent H (Finset.univ \ B) K) : nbr H K ⊆ B := by
  intro v hv
  obtain ⟨hn,u,hu,h⟩ := (nbr_mem ..).mp hv
  by_contra hno
  exact hn (comp_closed hk hu (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hno⟩) h)

theorem adhesion_le_card {n : ℕ} (H : SimpleGraph (Fin n)) (B : Finset (Fin n)) :
    adh H B ≤ B.card := by
  classical
  apply Finset.sup_le
  intro K h
  exact Finset.card_le_card (nbr_component H B K (Finset.mem_filter.mp h).2)


noncomputable def elts {n : ℕ} (X : Finset (Fin n)) := (List.finRange n).filter (· ∈ X)
noncomputable def words {n : ℕ} (X : Finset (Fin n)) := (elts X).map fun a => a.val.bits
noncomputable def rows {n : ℕ} (G : SimpleGraph (Fin n)) :=
  (List.finRange n).map (fun u => (List.finRange n).map fun v => decide (G.Adj u v))

theorem elts_size {n : ℕ} (X : Finset (Fin n)) : (elts X).length = X.card := by
  have eqn : (elts X).toFinset = X := by ext i; simp [elts]
  have nd : (elts X).Nodup := (List.nodup_finRange n).filter _
  exact (List.toFinset_card_of_nodup nd).symm.trans (congrArg Finset.card eqn)

theorem set_code {n : ℕ} (X : Finset (Fin n)) : setCode X.card (words X) = encodeSet X := by
  simp only [setCode,words,payload,List.flatMap_map,encodeSet,elts]
  simp [enc,encodeNat,List.append_assoc]

private theorem chargedFilter {n : ℕ} (l : List (Fin n)) (X B : Finset (Fin n)) (sub : X ⊆ B) :
    ((l.filter (· ∈ X)).flatMap (fun v => encodeNat v.val)).length + (l.filter (· ∈ B)).length ≤
      ((l.filter (· ∈ B)).flatMap (fun v => encodeNat v.val)).length + (l.filter (· ∈ X)).length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_flatMap] at ih
    have pos : 0 < (encodeNat i.val).length := by simp [encodeNat]
    by_cases a : i ∈ X
    · have b := sub a
      simp [a,b] <;> omega
    · by_cases b : i ∈ B <;> simp [a,b] <;> omega

private theorem natLenMono {x b : ℕ} (h : x ≤ b) : (encodeNat x).length ≤ (encodeNat b).length := by
  have v := Nat.size_le_size h
  simp only [← Nat.size_eq_bits_len] at v
  simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil]; omega

theorem setLen {n : ℕ} (X B : Finset (Fin n)) (sub : X ⊆ B) :
    (encodeSet X).length ≤ (encodeSet B).length ∧
      ((encodeSet X).length = (encodeSet B).length ↔ X=B) := by
  have h := chargedFilter (List.finRange n) X B sub
  change _ + (elts B).length ≤ _ + (elts X).length at h
  rw [elts_size,elts_size] at h
  have c := Finset.card_le_card sub
  have hd := natLenMono c
  constructor
  · simp only [encodeSet,List.length_append]; omega
  · constructor
    · intro eqn
      apply Finset.eq_of_subset_of_card_le sub
      simp only [encodeSet,List.length_append] at eqn
      omega
    · rintro rfl; rfl

theorem bound {n : ℕ} (k : ℕ) (X B : Finset (Fin n)) :
    budget n k X.card (words X) (encodeSet B) ≤ stepBound 64 k n := by
  have xn : X.card ≤ n := by simpa using Finset.card_le_univ X
  have bnd (t : ℕ) : t.bits.length ≤ t := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have sizeX := setLength X; have sizeB := setLength B
  have payloadX : (payload (words X)).length ≤ (encodeSet X).length := by
    rw [← set_code X]; simp [setCode]
  have unit (t : ℕ) (h : t ≤ n) : wordCost t ≤ 10*(n+1)^2 := by
    unfold wordCost
    calc
      _ ≤ (4*n+3)+(1+n*(6*n+6)) := by gcongr <;> first | exact (bnd t).trans h | exact h
      _ ≤ _ := by nlinarith
  have exp : 2*k+1 ≤ 2^(64*k) := by have h := Nat.lt_two_pow_self (n:=64*k); omega
  have degree : (n+1)^2 ≤ (n+1)^64 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold budget
  rw [set_code X]
  calc
    _ ≤ 10*(n+1)^2 + ((6*n^2+9*n+3) + ((4*k+3) + (10*(n+1)^2 +
        ((1+5*((n+1)*(2*n+1)))+(6*((n+1)*(2*n+1))+2*((n+1)*(2*n+1))+6))))) := by
      gcongr
      all_goals first | exact unit n le_rfl | exact unit X.card xn | exact bnd k
                      | exact sizeX | exact sizeB | exact payloadX.trans sizeX
    _ ≤ 64*(2*k+1)*(n+1)^2 := by nlinarith
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left 64 exp) degree
end SingleExpBisect.ShrinkMachine

open scoped Classical
namespace SingleExpBisect.ShrinkMachine
open SingleExpBisect.Main MinBisectFPT ExponomialAssortment.FPTAS

theorem official_run {n : ℕ} (H : SimpleGraph (Fin n)) (k : ℕ) (X B : Finset (Fin n)) (sub : X ⊆ B) :
    HMBinPacking.OutputsWithin machine (encodeInput H k ++ encodeSet X ++ encodeSet B)
      (if X=B then [false] else true::encodeSet X) (stepBound 64 k n) := by
  let rs := rows H
  let ws := words X
  have size : rs.length=n := by simp [rs,rows]
  have lens : ∀ l ∈ rs, l.length=n := by
    intro l h; obtain ⟨_,_,rfl⟩ := List.mem_map.mp h; simp
  have count : ws.length=X.card := by simp [ws,words,elts_size]
  have l := (setLen X B sub).1
  have le : (setCode X.card ws).length ≤ (encodeSet B).length := by simpa [ws,set_code] using l
  have t := program_runs n rs k X.card ws (encodeSet B) size lens count le
  have eqin : inputCode n rs k X.card ws (encodeSet B) = encodeInput H k ++ encodeSet X ++ encodeSet B := by
    simp [inputCode,ws,rs,set_code,encodeInput,encodeNat,enc,rows,List.flatMap_def,List.append_assoc]
  rw [eqin] at t
  have out : (if (setCode X.card ws).length=(encodeSet B).length then [false] else true::setCode X.card ws) =
      (if X=B then [false] else true::encodeSet X) := by
    simp only [ws,set_code,(setLen X B sub).2]
  rw [out] at t
  obtain ⟨⟨ht,hle⟩⟩ := t
  exact ⟨⟨ht,hle.trans (bound k X B)⟩⟩

theorem terminal_machine :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (k : ℕ) (X B : Finset (Fin n)),
      X ⊆ B → let out := if X=B then [false] else true::encodeSet X
      HMBinPacking.OutputsWithin M (encodeInput H k ++ encodeSet X ++ encodeSet B) out (stepBound 64 k n) ∧
      (X.card ≤ 2*k+1 → (X=B ∨ X.card ≤ 2*k ∨ adh H X ≤ 2*k) →
        ((out=[false] ∧ IsEdgeUnbreakable H Finset.univ B (2*k) k) ∨
          ∃ B' : Finset (Fin n), out=true::encodeSet B' ∧ X ⊆ B' ∧ B'.card < B.card ∧ adh H B' ≤ 2*k)) := by
  refine ⟨machine,?_⟩
  intro n H k X B sub out
  refine ⟨official_run H k X B sub,?_⟩
  intro small ok
  by_cases eqn : X=B
  · subst B
    exact Or.inl ⟨by simp [out],smallBag _ _ _ (by omega)⟩
  · have proper : X ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨sub,eqn⟩
    have a : adh H X ≤ 2*k := by
      rcases ok with e|sm|hd
      · exact (eqn e).elim
      · exact (adhesion_le_card H X).trans sm
      · exact hd
    exact Or.inr ⟨X,by simp [out,eqn],Finset.Subset.refl _,Finset.card_lt_card proper,a⟩
end SingleExpBisect.ShrinkMachine

open scoped Classical
open SingleExpBisect.Main MinBisectFPT

theorem solution :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (k : ℕ) (X B : Finset (Fin n)),
      X ⊆ B → let out := if X=B then [false] else true::encodeSet X
      HMBinPacking.OutputsWithin M (encodeInput H k ++ encodeSet X ++ encodeSet B) out (stepBound 64 k n) ∧
      (X.card ≤ 2*k+1 → (X=B ∨ X.card ≤ 2*k ∨ adh H X ≤ 2*k) →
        ((out=[false] ∧ IsEdgeUnbreakable H Finset.univ B (2*k) k) ∨
          ∃ B' : Finset (Fin n), out=true::encodeSet B' ∧ X ⊆ B' ∧ B'.card < B.card ∧ adh H B' ≤ 2*k)) := SingleExpBisect.ShrinkMachine.terminal_machine
