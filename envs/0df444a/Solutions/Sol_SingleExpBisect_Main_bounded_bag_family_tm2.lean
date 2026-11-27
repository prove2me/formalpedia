-- Prove2me | solution 1 for SingleExpBisect.Main.bounded_bag_family_tm2
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:28:20.859858+00:00
-- url     : https://prove2.me/submissions/36e1e57f-5504-4f7f-b177-26f54630253a

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


set_option autoImplicit false
namespace SingleExpBisect.MaskTable
open SingleExpBisect.ShrinkMachine
open BitStacks Block R

abbrev Token := Option Bool
def token : Token → List Bool
  | none => [false]
  | some b => [true,b]
def pack (ts : List Token) := ts.flatMap token
def addToken (b : Bool) : Token → List Token
  | none => [none,some b]
  | some x => [some x]
def addBit (b : Bool) (ts : List Token) := ts.flatMap (addToken b)
def tokens : ℕ → List Token
  | 0 => [none]
  | i+1 => addBit false (tokens i) ++ addBit true (tokens i)
def masks : ℕ → List (List Bool)
  | 0 => [[]]
  | i+1 => (masks i).map (false::·) ++ (masks i).map (true::·)
def row (bs : List Bool) : List Token := none::bs.map some

private theorem add_row (b : Bool) (xs : List Bool) : addBit b (row xs) = row (b::xs) := by
  simp [addBit,row,addToken,List.flatMap_map]
  induction xs <;> simp_all

theorem tokens_rows (i : ℕ) : tokens i = (masks i).flatMap row := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have add_rows (b : Bool) : addBit b ((masks i).flatMap row) =
        ((masks i).map (b::·)).flatMap row := by
      unfold addBit
      rw [List.flatMap_assoc,List.flatMap_map]
      apply List.flatMap_congr
      intro a _
      exact add_row b a
    simp only [tokens,masks,List.flatMap_append,ih,add_rows]

theorem masks_length (i : ℕ) : (masks i).length = 2^i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [masks,ih,pow_succ]; omega

theorem masks_mem (i : ℕ) (xs : List Bool) : xs ∈ masks i ↔ xs.length = i := by
  induction i generalizing xs with
  | zero => simp [masks]
  | succ i ih =>
    cases xs with
    | nil => simp [masks]
    | cons b xs => cases b <;> simp [masks,ih]

theorem masks_nodup (i : ℕ) : (masks i).Nodup := by
  induction i with
  | zero => simp [masks]
  | succ i ih =>
    rw [masks,List.nodup_append]
    exact ⟨ih.map (fun _ _ e => List.cons.inj e |>.2),ih.map (fun _ _ e => List.cons.inj e |>.2),
      by intro a ha d hd; obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha; obtain ⟨y,_,rfl⟩ := List.mem_map.mp hd; simp⟩

theorem tokens_length (i : ℕ) : (tokens i).length = (i+1)*2^i := by
  rw [tokens_rows, List.length_flatMap]
  have eq : (masks i).map (fun a => (row a).length) = (masks i).map (fun _ => i+1) := by
    apply List.map_congr_left
    intro xs h
    simp [row,(masks_mem i xs).mp h]
  rw [eq]
  simp [masks_length,Nat.mul_comm]

theorem pack_length (ts : List Token) : (pack ts).length ≤ 2*ts.length := by
  induction ts with
  | nil => simp [pack]
  | cons t ts ih =>
    change (token t ++ pack ts).length ≤ _
    cases t <;> simp [token] <;> omega

/-- Input tape `base` stores start-of-row and data tokens. On every token
the finite instruction copies at most two bits to the scratch tape and
appends at most three bits to the reversed result tape. -/
def passBody (save b : Bool) : Block R := atom (.peek base fun top =>
  if top.getD false then
    .drop base (.peek base fun val => .drop base
      (.push out true (.push out (val.getD false)
        (if save then .push temp true (.push temp (val.getD false) (.stop none)) else .stop none))))
  else
    .drop base (.push out false (.push out true (.push out b
      (if save then .push temp false (.stop none) else .stop none)))))

def pass (save b : Bool) := loop base present (passBody save b)

theorem pass_run (save b : Bool) (ts : List Token) (s : S) :
    (pass save b).Run ({s with base:=pack ts}:S).mem (2*ts.length+1)
      ({s with base:=[],out:=(pack (addBit b ts)).reverse++s.out, temp:=if save then (pack ts).reverse++s.temp else s.temp}:S).mem := by
  induction ts generalizing s with
  | nil =>
    have d := done (k:=base) (test:=present) (p:=passBody save b) (m:=({s with base:=[]}:S).mem) (by simp [present])
    cases save <;> simpa [pass,pack,addBit,present] using d
  | cons t ts ih =>
    let u : S := {s with out:=(pack (addToken b t)).reverse++s.out, temp:=if save then (token t).reverse++s.temp else s.temp}
    have ht : (passBody save b).Run ({s with base:=pack (t::ts)}:S).mem 1
        ({u with base:=pack ts}:S).mem := by
      apply atom_run
      cases t <;> cases save <;> simp [passBody,Action.run,u,pack,token,addToken]
    have hguard : present (({s with base:=pack (t::ts)}:S).mem base).head? = true := by
      cases t <;> simp [pack,token,present]
    have h := more hguard ht (ih u)
    have tim : 1+1+(2*ts.length+1) = 2*(t::ts).length+1 := by simp; omega
    rw [tim] at h
    cases save <;> simpa [pass,u,pack,addBit,List.reverse_append,List.append_assoc] using h

def twice := pass true false >>> transfer temp base >>> pass false true >>> transfer out base
def doubled (ts : List Token) := addBit false ts ++ addBit true ts

theorem twice_run (ts : List Token) (s : S) :
    twice.Run ({s with base:=pack ts,temp:=[],out:=[]}:S).mem
      ((2*ts.length+1) + ((2*(pack ts).length+1) + ((2*ts.length+1) + (2*(pack (doubled ts)).length+1))))
      ({s with base:=pack (doubled ts),temp:=[],out:=[]}:S).mem := by
  let rev := (pack (addBit false ts)).reverse
  let src := ({s with temp:=[],out:=[]}:S)
  have a := pass_run true false ts src
  let one : S := {s with base:=[],temp:=(pack ts).reverse,out:=rev}
  have b := transfer_run temp base (by decide) one.mem (pack ts).reverse rfl
  have c := pass_run false true ts ({s with temp:=[],out:=rev}:S)
  let last : S := {s with base:=[],temp:=[],out:=(pack (doubled ts)).reverse}
  have d := transfer_run out base (by decide) last.mem (pack (doubled ts)).reverse rfl
  have ha : (pass true false).Run ({s with base:=pack ts,temp:=[],out:=[]}:S).mem
      (2*ts.length+1) one.mem := by simpa [src,one,rev] using a
  have hb : (transfer temp base).Run one.mem (2*(pack ts).length+1) ({s with base:=pack ts,temp:=[],out:=rev}:S).mem := by
    simpa [one] using b
  have hc : (pass false true).Run ({s with base:=pack ts,temp:=[],out:=rev}:S).mem
      (2*ts.length+1) last.mem := by
    simpa [last,rev,doubled,pack,List.reverse_append] using c
  have hd : (transfer out base).Run last.mem (2*(pack (doubled ts)).length+1)
      ({s with base:=pack (doubled ts),temp:=[],out:=[]}:S).mem := by
    simpa [last] using d
  exact Block.seq (p:=pass true false) (q:=transfer temp base >>> pass false true >>> transfer out base) ha
    (Block.seq hb (Block.seq hc hd))

end SingleExpBisect.MaskTable


set_option autoImplicit false
namespace SingleExpBisect.MaskTable
open SingleExpBisect.ShrinkMachine
open BitStacks Block R

private def roundBody := pop units >>> twice
def build := loop units present roundBody
private def stageCost (i : ℕ) :=
  (2*(tokens i).length+1) + ((2*(pack (tokens i)).length+1) +
    ((2*(tokens i).length+1) + (2*(pack (tokens (i+1))).length+1)))

private theorem stage_bound (b i : ℕ) (hi : i < b) :
    2 + stageCost i ≤ 20*((b+1)*2^b)+6 := by
  have l0 : (tokens i).length ≤ (b+1)*2^b := by
    rw [tokens_length]
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
  have l1 : (tokens (i+1)).length ≤ (b+1)*2^b := by
    rw [tokens_length]
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
  have p0 := pack_length (tokens i)
  have p1 := pack_length (tokens (i+1))
  unfold stageCost
  omega

theorem build_run (b left i : ℕ) (h : i+left=b) (s : S) :
    build.Within ({s with base:=pack (tokens i),units:=marks left,temp:=[],out:=[]}:S).mem
      (left*(20*((b+1)*2^b)+6)+1)
      ({s with base:=pack (tokens b),units:=[],temp:=[],out:=[]}:S).mem := by
  induction left generalizing i s with
  | zero =>
    simp only [Nat.add_zero] at h
    subst i
    have st := done (k:=units) (test:=present) (p:=roundBody)
      (m:=({s with base:=pack (tokens b),units:=[],temp:=[],out:=[]}:S).mem) (by simp [present])
    exact ⟨1,by simp,by simpa [build,marks,present] using st⟩
  | succ rem ih =>
    let init : S := {s with base:=pack (tokens i),units:=marks (rem+1),temp:=[],out:=[]}
    let middle : S := {init with units:=marks rem}
    let next : S := {s with base:=pack (tokens (i+1)),units:=marks rem,temp:=[],out:=[]}
    have hp : (pop units).Run init.mem 1 middle.mem := by
      simpa [init,middle,marks,List.replicate_succ] using pop_run units init.mem
    have hb : twice.Run middle.mem (stageCost i) next.mem := by
      simpa [middle,init,next,stageCost,doubled,tokens] using twice_run (tokens i) middle
    have body : roundBody.Run init.mem (1+stageCost i) next.mem := Block.seq hp hb
    obtain ⟨t,ht,tr⟩ := ih (i+1) (by omega) s
    have trace := more (k:=units) (test:=present) (m:=init.mem) (by simp [init,present,marks,List.replicate_succ])
      body tr
    have budget := stage_bound b i (by omega)
    refine ⟨_,?_,trace⟩
    rw [Nat.succ_mul]
    omega

/-- The read-out pass drops row markers and emits exactly the data bits. -/
private def emitBody : Block R := atom (.peek base fun top =>
  if top.getD false then
    .drop base (.peek base fun val => .drop base (.push out (val.getD false) (.stop none)))
  else .drop base (.stop none))
private def emit := loop base present emitBody

private theorem emit_run (ts : List Token) (s : S) :
    emit.Run ({s with base:=pack ts}:S).mem (2*ts.length+1)
      ({s with base:=[],out:=(ts.filterMap id).reverse++s.out}:S).mem := by
  induction ts generalizing s with
  | nil =>
    simpa [emit,pack,present] using done (k:=base) (test:=present) (p:=emitBody)
      (m:=({s with base:=[]}:S).mem) (by simp [present])
  | cons t ts ih =>
    let u : S := {s with out:=t.toList++s.out}
    have step : emitBody.Run ({s with base:=pack (t::ts)}:S).mem 1 ({u with base:=pack ts}:S).mem := by
      apply atom_run
      cases t <;> simp [Action.run,u,pack,token]
    have guard : present (({s with base:=pack (t::ts)}:S).mem base).head? = true := by
      cases t <;> simp [pack,token,present]
    have tr := more guard step (ih u)
    have tim : 1+1+(2*ts.length+1) = 2*(t::ts).length+1 := by simp; omega
    rw [tim] at tr
    cases t <;> simpa [u,emit,List.reverse_cons,List.append_assoc] using tr

theorem tokens_data (b : ℕ) : (tokens b).filterMap id = (masks b).flatten := by
  rw [tokens_rows]
  have eq (xs : List Bool) : (row xs).filterMap id = xs := by
    simp [row,List.filterMap_map]
  have h (l : List (List Bool)) : (l.flatMap row).filterMap id = l.flatten := by
    induction l with
    | nil => rfl
    | cons x xs ih => simp only [List.flatMap_cons,List.filterMap_append,List.flatten_cons,eq,ih]
  exact h _

theorem data_length (b : ℕ) : (masks b).flatten.length = b*2^b := by
  rw [List.length_flatten]
  have eq : (masks b).map List.length = (masks b).map (fun _ => b) := by
    apply List.map_congr_left
    intro xs hx
    exact (masks_mem b xs).mp hx
  rw [eq]; simp [masks_length,Nat.mul_comm]

def program := readNumber false >>> push base false >>> build >>> emit >>> transfer out input
def machine := BitStacks.machine program.entry input program.code
def budget (b : ℕ) := wordCost b + (1 + ((b*(20*((b+1)*2^b)+6)+1) +
    ((2*((b+1)*2^b)+1) + (2*(b*2^b)+1))))

/-- One fixed finite-stack TM2. The result concatenates every b-bit word
exactly once, in lexicographic order with false before true. -/
theorem machine_runs (b : ℕ) : HMBinPacking.OutputsWithin machine (enc b.bits) (masks b).flatten (budget b) := by
  let z : S := {}
  let start (xs : List Bool) : S := {input:=xs}
  let one : S := {units:=marks b}
  let two : S := {units:=marks b,base:=[false]}
  let finished : S := {base:=pack (tokens b)}
  let rev : S := {out:=(masks b).flatten.reverse}
  have a : (readNumber false).Within (start (enc b.bits)).mem (wordCost b) one.mem := by
    simpa [z,start,one,stash] using number_run false b [] z rfl rfl rfl rfl
  have c : (push base false).Run one.mem 1 two.mem := by
    simpa [one,two] using push_run base false one.mem
  have d : build.Within two.mem (b*(20*((b+1)*2^b)+6)+1) finished.mem := by
    simpa [two,finished,z,tokens,pack,token] using build_run b b 0 (by omega) z
  have e : emit.Run finished.mem (2*((b+1)*2^b)+1) rev.mem := by
    have tr := emit_run (tokens b) z
    rw [tokens_data,tokens_length] at tr
    simpa [finished,rev,z] using tr
  have f : (transfer out input).Run rev.mem (2*(b*2^b)+1) (start (masks b).flatten).mem := by
    have tr := transfer_run out input (by decide) rev.mem (masks b).flatten.reverse rfl
    rw [List.length_reverse,data_length] at tr
    simpa [rev,start] using tr
  have trace := a.seq (c.within.seq (d.seq (e.within.seq f.within)))
  have iso (xs : List Bool) : isolated (K:=R) input xs = (start xs).mem := by
    funext r; cases r <;> rfl
  have final : program.Within (isolated input (enc b.bits)) (budget b) (isolated input (masks b).flatten) := by
    rw [iso,iso]
    exact trace
  exact final.outputs _ _ _

end SingleExpBisect.MaskTable

namespace SingleExpBisect.MaskSelect
open SingleExpBisect.ShrinkMachine
open BitStacks Block R

def ones : List Bool → ℕ
  | true :: xs => ones xs + 1
  | _ => 0

def remainder : List Bool → List Bool
  | true :: xs => remainder xs
  | xs => xs

def inc (w : List Bool) := List.replicate (ones w) false ++ true :: (remainder w).tail

theorem inc_bits (n : ℕ) : inc n.bits = (n+1).bits := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n=0
    · subst n; rfl
    let q := n/2
    have hq : q < n := by dsimp [q]; omega
    have cases' : n = 2*q ∨ n = 2*q+1 := by dsimp [q]; omega
    rcases cases' with e | e
    · have hqn : q ≠ 0 := by omega
      rw [e,Nat.bit0_bits _ hqn,Nat.bit1_bits]
      simp [inc,ones,remainder]
    · rw [e,Nat.bit1_bits,show 2*q+1+1 = 2*(q+1) by omega,Nat.bit0_bits _ (by omega),←ih q hq]
      simp [inc,ones,remainder,List.replicate_succ]

theorem bounded_ones (w : List Bool) : ones w ≤ w.length := by
  induction w with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [ones] <;> omega

private def carryAtom : Block R := atom (.drop bits (.push temp false (.stop none)))
private def carry := loop bits marked carryAtom
private def topOne : Block R := atom (.drop bits (.push bits true (.stop none)))
def increment := carry >>> topOne >>> transfer temp bits

private theorem carry_run (w : List Bool) (s : S) :
    carry.Run ({s with bits:=w}:S).mem (2*ones w+1)
      ({s with bits:=remainder w,temp:=List.replicate (ones w) false ++ s.temp}:S).mem := by
  induction w generalizing s with
  | nil =>
    exact done (k:=bits) (test:=marked) (p:=carryAtom) (m:=({s with bits:=[]}:S).mem) rfl
  | cons b xs ih =>
    cases b with
    | false => exact done (k:=bits) (test:=marked) (p:=carryAtom) (m:=({s with bits:=false::xs}:S).mem) rfl
    | true =>
      let u : S := {s with temp:=false::s.temp}
      have st : carryAtom.Run ({s with bits:=true::xs}:S).mem 1 ({u with bits:=xs}:S).mem := by
        apply atom_run; simp [Action.run,u]
      have go := more (k:=bits) (test:=marked) (m:=({s with bits:=true::xs}:S).mem) (by rfl) st (ih u)
      have he : List.replicate (ones xs) false ++ false::s.temp =
          List.replicate (ones xs+1) false ++ s.temp := by rw [List.replicate_add]; simp [List.append_assoc]
      have tm : 1+1+(2*ones xs+1) = 2*ones (true::xs)+1 := by simp [ones]; omega
      rw [tm] at go
      simpa [u,remainder,ones,he,carry] using go

theorem increment_run (w : List Bool) (s : S) :
    increment.Run ({s with bits:=w,temp:=[]}:S).mem (4*ones w+3)
      ({s with bits:=inc w,temp:=[]}:S).mem := by
  let a : S := {s with bits:=remainder w,temp:=List.replicate (ones w) false}
  let b : S := {a with bits:=true::(remainder w).tail}
  have ca : carry.Run ({s with bits:=w,temp:=[]}:S).mem (2*ones w+1) a.mem := by
    simpa [a] using carry_run w ({s with temp:=[]}:S)
  have bo : topOne.Run a.mem 1 b.mem := by apply atom_run; simp [Action.run,a,b]
  have tr : (transfer temp bits).Run b.mem (2*ones w+1) ({s with bits:=inc w,temp:=[]}:S).mem := by
    simpa [b,a,inc] using transfer_run temp bits (by decide) b.mem (List.replicate (ones w) false) rfl
  have rr := Block.seq (p:=carry) (q:=topOne >>> transfer temp bits) ca (Block.seq bo tr)
  have tm : (2*ones w+1)+(1+(2*ones w+1)) = 4*ones w+3 := by omega
  rw [tm] at rr
  exact rr

def framed : List (Bool × List Bool) → List Bool
  | [] => []
  | (flag,w)::xs => flag :: (enc w ++ framed xs)

def kept : List (Bool × List Bool) → List (List Bool)
  | [] => []
  | (false,_)::xs => kept xs
  | (true,w)::xs => w::kept xs

private def step := choice input marked
  (pop input >>> readWord true false >>> increment) (pop input >>> readWord false false)
private def scan := loop input present step

private def scanCost : ℕ → List (Bool × List Bool) → ℕ
  | _,[] => 1
  | c,(false,w)::xs => 1+(1+(1+(4*w.length+3))) + scanCost c xs
  | c,(true,w)::xs => 1+(1+(1+((4*w.length+3)+(4*ones c.bits+3)))) + scanCost (c+1) xs

private theorem scan_run (l : List (Bool × List Bool)) (c : ℕ) (s : S) :
    scan.Run ({s with input:=framed l,bits:=c.bits,width:=[],temp:=[]}:S).mem (scanCost c l)
      ({s with input:=[],bits:=(c+(kept l).length).bits,width:=[],temp:=[],saved:=(payload (kept l)).reverse++s.saved}:S).mem := by
  induction l generalizing c s with
  | nil =>
    simpa [scanCost,framed,kept,payload,scan] using done (k:=input) (test:=present) (p:=step)
      (m:=({s with input:=[],bits:=c.bits,width:=[],temp:=[]}:S).mem) (by rfl)
  | cons p xs ih =>
    obtain ⟨flag,w⟩ := p
    let s₀ : S := {s with bits:=c.bits,width:=[],temp:=[]}
    let tail := framed xs
    let start : S := {s₀ with input:=flag::(enc w ++ tail)}
    let mid : S := {s₀ with input:=enc w ++ tail}
    have popok : (pop input).Run start.mem 1 mid.mem := by simpa [start,mid] using pop_run input start.mem
    cases flag with
    | false =>
      have skip : (readWord false false).Run mid.mem (4*w.length+3) ({s₀ with input:=tail}:S).mem := by
        simpa [mid,stash,s₀] using read_run false false w tail s₀ rfl
      have body := no (k:=input) (test:=marked) (p:=pop input >>> readWord true false >>> increment) (m:=start.mem)
        (by rfl) (Block.seq popok skip)
      have tr := more (k:=input) (test:=present) (m:=start.mem) (by rfl) body (ih c s)
      simpa [start,s₀,scan,step,scanCost,kept,framed,tail] using tr
    | true =>
      let savedWord := (enc w).reverse++s.saved
      let after : S := {s₀ with input:=tail,saved:=savedWord}
      have save : (readWord true false).Run mid.mem (4*w.length+3) after.mem := by
        simpa [mid,after,stash,s₀,savedWord] using read_run true false w tail s₀ rfl
      have bump : increment.Run after.mem (4*ones c.bits+3) ({after with bits:=(c+1).bits}:S).mem := by
        simpa [after,s₀,inc_bits] using increment_run c.bits after
      have body := yes (k:=input) (test:=marked) (q:=pop input >>> readWord false false) (m:=start.mem)
        (by rfl) (Block.seq popok (Block.seq save bump))
      have tr := more (k:=input) (test:=present) (m:=start.mem) (by rfl) body
        (ih (c+1) ({s with saved:=savedWord}:S))
      simpa [start,s₀,scan,step,scanCost,kept,framed,tail,payload,savedWord,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tr


private def countStep : Block R := atom (.peek bits fun v => .drop bits
  (.push temp (v.getD false) (.push width true (.stop none))))
private def reverseCount := loop bits present countStep
def headerOut := reverseCount >>> transfer temp input >>> push input false >>> transfer width input

private theorem reverseCount_run (bs : List Bool) (s : S) :
    reverseCount.Run ({s with bits:=bs}:S).mem (2*bs.length+1)
      ({s with bits:=[],temp:=bs.reverse++s.temp,width:=List.replicate bs.length true++s.width}:S).mem := by
  induction bs generalizing s with
  | nil =>
    simpa [reverseCount] using done (k:=bits) (test:=present) (p:=countStep)
      (m:=({s with bits:=[]}:S).mem) (by rfl)
  | cons b bs ih =>
    let u : S := {s with temp:=b::s.temp,width:=true::s.width}
    have st : countStep.Run ({s with bits:=b::bs}:S).mem 1 ({u with bits:=bs}:S).mem := by
      apply atom_run; simp [Action.run,u]
    have r := more (k:=bits) (test:=present) (m:=({s with bits:=b::bs}:S).mem) (by rfl) st (ih u)
    have e : List.replicate bs.length true ++ true::s.width = List.replicate (bs.length+1) true ++s.width := by
      rw [List.replicate_add]; simp [List.append_assoc]
    have eq : 1+1+(2*bs.length+1) = 2*(b::bs).length+1 := by simp; omega
    rw [eq] at r
    simpa [reverseCount,u,e,List.reverse_cons,List.append_assoc] using r

theorem headerOut_run (w : List Bool) (s : S) :
    headerOut.Run ({s with bits:=w,temp:=[],width:=[]}:S).mem (6*w.length+4)
      ({s with bits:=[],temp:=[],width:=[],input:=enc w ++ s.input}:S).mem := by
  let a : S := {s with bits:=[],temp:=w.reverse,width:=List.replicate w.length true}
  let b : S := {a with temp:=[],input:=w++s.input}
  let c : S := {b with input:=false::(w++s.input)}
  have r : reverseCount.Run ({s with bits:=w,temp:=[],width:=[]}:S).mem (2*w.length+1) a.mem := by
    simpa [a] using reverseCount_run w ({s with temp:=[],width:=[]}:S)
  have t : (transfer temp input).Run a.mem (2*w.length+1) b.mem := by
    simpa [a,b] using transfer_run temp input (by decide) a.mem w.reverse rfl
  have p : (push input false).Run b.mem 1 c.mem := by simpa [b,c] using push_run input false b.mem
  have d : (transfer width input).Run c.mem (2*w.length+1)
      ({s with bits:=[],temp:=[],width:=[],input:=enc w ++ s.input}:S).mem := by
    simpa [a,b,c,enc,List.append_assoc] using transfer_run width input (by decide) c.mem
      (List.replicate w.length true) rfl
  have run := Block.seq (p:=reverseCount) (q:=transfer temp input >>> push input false >>> transfer width input)
    r (Block.seq t (Block.seq p d))
  have eq : (2*w.length+1) + ((2*w.length+1) + (1+(2*w.length+1))) = 6*w.length+4 := by omega
  rw [eq] at run; exact run

def program := scan >>> transfer saved input >>> headerOut
def machine := BitStacks.machine program.entry input program.code
def budget (l : List (Bool × List Bool)) :=
  scanCost 0 l + ((2*(payload (kept l)).length+1)+(6*(kept l).length.bits.length+4))

/-- One real TM2 writes the canonical number-of-selected-vertices prefix
and all selected self-delimited labels in order, on arbitrary labels and masks. -/
theorem machine_runs (l : List (Bool × List Bool)) :
    HMBinPacking.OutputsWithin machine (framed l)
      (enc (kept l).length.bits ++ payload (kept l)) (budget l) := by
  let z : S := {}
  let state (xs : List Bool) : S := {input:=xs}
  let w := (kept l).length.bits
  let data := payload (kept l)
  let s : S := {bits:=w,saved:=data.reverse}
  let t : S := {bits:=w,input:=data}
  have a : scan.Run (state (framed l)).mem (scanCost 0 l) s.mem := by
    simpa [z,state,w,s,data] using scan_run l 0 z
  have b : (transfer saved input).Run s.mem (2*data.length+1) t.mem := by
    simpa [s,t] using transfer_run saved input (by decide) s.mem data.reverse rfl
  have c : headerOut.Run t.mem (6*w.length+4) (state (enc w ++ data)).mem := by
    simpa [w,data,state,t] using headerOut_run w t
  have trace := Block.seq (p:=scan) (q:=transfer saved input >>> headerOut) a (Block.seq b c)
  have iso (xs : List Bool) : isolated (K:=R) input xs = (state xs).mem := by
    funext r; cases r <;> rfl
  have run : program.Within (isolated input (framed l)) (budget l) (isolated input (enc w ++ data)) := by
    rw [iso,iso]
    exact trace.within
  exact run.outputs _ _ _

end SingleExpBisect.MaskSelect


set_option autoImplicit false
namespace SingleExpBisect.FamilyRow
open SingleExpBisect.ShrinkMachine SingleExpBisect.MaskTable
open BitStacks Block R

abbrev Item := Bool × List Bool
def labels (l : List Item) := l.map Prod.snd
def flags (l : List Item) := pack (l.map fun p => some p.1)

private def markBody : Block R := atom (.peek input fun v => .drop input
  (.push count (v.getD false) (.push temp (v.getD false) (.stop none))))
private def markCopy := loop input present markBody
private def backup := markCopy >>> transfer temp input

private theorem markCopy_run (xs : List Bool) (s : S) :
    markCopy.Run ({s with input:=xs}:S).mem (2*xs.length+1)
      ({s with input:=[],count:=xs.reverse++s.count,temp:=xs.reverse++s.temp}:S).mem := by
  induction xs generalizing s with
  | nil =>
    simpa [markCopy] using (done (k:=input) (test:=present) (p:=markBody) (m:=({s with input:=[]}:S).mem) (by rfl))
  | cons b xs ih =>
    let u : S := {s with count:=b::s.count,temp:=b::s.temp}
    have st : markBody.Run ({s with input:=b::xs}:S).mem 1 ({u with input:=xs}:S).mem := by
      apply atom_run; simp [Action.run,u]
    have tr := more (k:=input) (test:=present) (m:=({s with input:=b::xs}:S).mem) (by rfl) st (ih u)
    have eq : 1+1+(2*xs.length+1) = 2*(b::xs).length+1 := by simp; omega
    rw [eq] at tr
    simpa [markCopy,u,List.reverse_cons,List.append_assoc] using tr

private theorem backup_run (xs : List Bool) (s : S) :
    backup.Run ({s with input:=xs,temp:=[],count:=[]}:S).mem (4*xs.length+2)
      ({s with input:=xs,temp:=[],count:=xs.reverse}:S).mem := by
  let mid : S := {s with input:=[],temp:=xs.reverse,count:=xs.reverse}
  have a : markCopy.Run ({s with input:=xs,temp:=[],count:=[]}:S).mem (2*xs.length+1) mid.mem := by
    simpa [mid] using markCopy_run xs ({s with temp:=[],count:=[]}:S)
  have b : (transfer temp input).Run mid.mem (2*xs.length+1)
      ({s with input:=xs,temp:=[],count:=xs.reverse}:S).mem := by
    simpa [mid] using transfer_run temp input (by decide) mid.mem xs.reverse rfl
  have tr := Block.seq (p:=markCopy) (q:=transfer temp input) a b
  have eq : (2*xs.length+1)+(2*xs.length+1) = 4*xs.length+2 := by omega
  rw [eq] at tr
  exact tr

private def pickBody := pop base >>> choice base marked
  (pop base >>> readWord true false >>> MaskSelect.increment) (pop base >>> readWord false false)
private def pick := loop base marked pickBody
private def pickCost : ℕ → List Item → ℕ
  | _,[] => 1
  | c,(false,w)::xs => 1+(1+(1+(1+(4*w.length+3)))) + pickCost c xs
  | c,(true,w)::xs => 1+(1+(1+(1+((4*w.length+3)+(4*MaskSelect.ones c.bits+3))))) + pickCost (c+1) xs

private theorem pick_run (l : List Item) (c : ℕ) (s : S) (rest : List Bool) (hr : marked rest.head?=false) :
    pick.Run ({s with input:=payload (labels l),base:=flags l ++rest,bits:=c.bits,width:=[],temp:=[]}:S).mem (pickCost c l)
      ({s with input:=[],base:=rest,bits:=(c+(MaskSelect.kept l).length).bits,width:=[],temp:=[],saved:=(payload (MaskSelect.kept l)).reverse++s.saved}:S).mem := by
  induction l generalizing c s with
  | nil =>
    simpa [pickCost,pick,flags,labels,pack,MaskSelect.kept,payload] using done (k:=base) (test:=marked) (p:=pickBody)
      (m:=({s with input:=[],base:=rest,bits:=c.bits,width:=[],temp:=[]}:S).mem) (by simpa using hr)
  | cons p xs ih =>
    obtain ⟨flag,w⟩ := p
    let sx : S := {s with bits:=c.bits,width:=[],temp:=[]}
    let bb := flags xs ++ rest
    let vv := payload (labels xs)
    let a : S := {sx with base:=true::flag::bb,input:=enc w ++ vv}
    let b : S := {a with base:=flag::bb}
    let d : S := {a with base:=bb}
    have first : (pop base).Run a.mem 1 b.mem := by simpa [a,b] using pop_run base a.mem
    have second : (pop base).Run b.mem 1 d.mem := by simpa [a,b,d] using pop_run base b.mem
    cases flag with
    | false =>
      have skip : (readWord false false).Run d.mem (4*w.length+3) ({sx with base:=bb,input:=vv}:S).mem := by
        simpa [d,a,sx,stash] using read_run false false w vv ({sx with base:=bb}:S) rfl
      have choose := no (k:=base) (test:=marked) (p:=pop base >>> readWord true false >>> MaskSelect.increment)
        (m:=b.mem) (by rfl) (Block.seq second skip)
      have body := Block.seq (p:=pop base) first choose
      have go := more (k:=base) (test:=marked) (m:=a.mem) (by rfl) body (ih c s)
      simpa [a,sx,bb,vv,pickBody,pick,pickCost,flags,labels,pack,token,MaskSelect.kept,payload] using go
    | true =>
      let saw := (enc w).reverse ++ s.saved
      let aft : S := {sx with base:=bb,input:=vv,saved:=saw}
      have keep : (readWord true false).Run d.mem (4*w.length+3) aft.mem := by
        simpa [d,a,sx,aft,saw,stash] using read_run true false w vv ({sx with base:=bb}:S) rfl
      have bump : MaskSelect.increment.Run aft.mem (4*MaskSelect.ones c.bits+3) ({aft with bits:=(c+1).bits}:S).mem := by
        simpa [aft,sx,MaskSelect.inc_bits] using MaskSelect.increment_run c.bits aft
      have choose := yes (k:=base) (test:=marked) (q:=pop base >>> readWord false false)
        (m:=b.mem) (by rfl) (Block.seq second (Block.seq keep bump))
      have body := Block.seq (p:=pop base) first choose
      have go := more (k:=base) (test:=marked) (m:=a.mem) (by rfl) body (ih (c+1) ({s with saved:=saw}:S))
      simpa [a,sx,bb,vv,pickBody,pick,pickCost,flags,labels,pack,token,MaskSelect.kept,payload,saw,List.append_assoc,
        List.reverse_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using go

theorem bits_bound (c : ℕ) : c.bits.length ≤ c := by
  rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self

private theorem pick_bound (B c : ℕ) (l : List Item) (h : c+l.length ≤ B) :
    pickCost c l ≤ (4*B+10)*l.length + 4*(payload (labels l)).length + 1 := by
  induction l generalizing c with
  | nil => simp [pickCost,labels,payload]
  | cons p xs ih =>
    obtain ⟨flag,w⟩ := p
    have h1 := ih c (by simp at h; omega)
    have h2 := ih (c+1) (by simp at h; omega)
    have ho := (MaskSelect.bounded_ones c.bits).trans (bits_bound c)
    have cB : c ≤ B := by simp at h; omega
    cases flag <;> simp only [pickCost,List.length_cons,Nat.mul_succ,labels,List.map_cons,payload,
      List.flatMap_cons,List.length_append,enc,List.length_replicate] at * <;> omega

private theorem kept_bounds (l : List Item) :
    (MaskSelect.kept l).length ≤ l.length ∧ (payload (MaskSelect.kept l)).length ≤ (payload (labels l)).length := by
  induction l with
  | nil => simp [MaskSelect.kept,labels,payload]
  | cons p xs ih =>
    obtain ⟨flag,w⟩ := p
    cases flag <;> simp only [MaskSelect.kept,labels,List.map_cons,payload,List.flatMap_cons,
      List.length_append,List.length_cons] at * <;> constructor <;> omega

def handle := pop base >>> backup >>> pick >>> transfer saved input >>> MaskSelect.headerOut >>> transfer input out >>> transfer count input

def rowWord (l : List Item) := enc (MaskSelect.kept l).length.bits ++ payload (MaskSelect.kept l)

theorem handle_run (l : List Item) (rest : List Bool) (hr : marked rest.head?=false) (s : S) :
    handle.Within ({s with input:=payload (labels l),base:=false :: (flags l ++ rest),bits:=[],temp:=[],width:=[],count:=[],saved:=[]}:S).mem
      (100*(l.length + (payload (labels l)).length + 1)^2)
      ({s with input:=payload (labels l),base:=rest,bits:=[],temp:=[],width:=[],count:=[],saved:=[],out:=(rowWord l).reverse++s.out}:S).mem := by
  let words := payload (labels l)
  let selected := payload (MaskSelect.kept l)
  let w := (MaskSelect.kept l).length.bits
  let sx : S := {s with bits:=[],temp:=[],width:=[],count:=[],saved:=[]}
  let a : S := {sx with input:=words,base:=false :: (flags l ++ rest)}
  let b : S := {a with base:=flags l ++ rest}
  let d : S := {b with count:=words.reverse}
  let e : S := {sx with base:=rest,input:=[],bits:=w,saved:=selected.reverse,count:=words.reverse}
  let f : S := {e with saved:=[],input:=selected}
  let h : S := {f with bits:=[],input:=rowWord l}
  let j : S := {h with input:=[],out:=(rowWord l).reverse++s.out}
  have ab : (pop base).Run a.mem 1 b.mem := by simpa [a,b] using pop_run base a.mem
  have bd : backup.Run b.mem (4*words.length+2) d.mem := by simpa [b,d,a,sx] using backup_run words b
  have de : pick.Run d.mem (pickCost 0 l) e.mem := by
    simpa [d,b,a,e,sx,words,selected,w] using pick_run l 0 ({sx with count:=words.reverse}:S) rest hr
  have ef : (transfer saved input).Run e.mem (2*selected.length+1) f.mem := by
    simpa [e,f] using transfer_run saved input (by decide) e.mem selected.reverse rfl
  have fh : MaskSelect.headerOut.Run f.mem (6*w.length+4) h.mem := by
    simpa [f,e,h,rowWord,w,selected,sx] using MaskSelect.headerOut_run w f
  have hj : (transfer input out).Run h.mem (2*(rowWord l).length+1) j.mem := by
    simpa [h,j,f,e,sx] using transfer_run input out (by decide) h.mem (rowWord l) rfl
  have endStep : (transfer count input).Run j.mem (2*words.length+1)
      ({sx with base:=rest,input:=words,out:=(rowWord l).reverse++s.out}:S).mem := by
    simpa [j,h,f,e,sx] using transfer_run count input (by decide) j.mem words.reverse rfl
  have trace := Block.seq (p:=pop base) (q:=backup >>> pick >>> transfer saved input >>> MaskSelect.headerOut >>> transfer input out >>> transfer count input)
    ab (Block.seq bd (Block.seq de (Block.seq ef (Block.seq fh (Block.seq hj endStep)))))
  refine ⟨_,?_,trace⟩
  have hc := pick_bound l.length 0 l (by simp)
  have hcount := (bits_bound (MaskSelect.kept l).length).trans (kept_bounds l).1
  have hsize := (kept_bounds l).2
  have outlen : (rowWord l).length = 2*w.length +1+selected.length := by
    simp [rowWord,enc,w,selected]; omega
  dsimp only [w,words,selected] at *
  rw [outlen]
  nlinarith [Nat.zero_le (l.length^2),Nat.zero_le ((payload (labels l)).length^2),
    Nat.zero_le (l.length*(payload (labels l)).length)]

end SingleExpBisect.FamilyRow


set_option autoImplicit false
namespace SingleExpBisect.FamilyTape
open SingleExpBisect.ShrinkMachine SingleExpBisect.MaskTable SingleExpBisect.FamilyRow
open BitStacks Block R

def table (rows : List (List Bool)) := pack (rows.flatMap MaskTable.row)
def wordsOut (ws rows : List (List Bool)) := rows.flatMap fun m => rowWord (m.zip ws)

theorem zip_parts {α β : Type} (xs : List α) (ys : List β) (h : xs.length=ys.length) :
    (xs.zip ys).map Prod.fst = xs ∧ (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih => cases ys <;> simp_all

private def projectRows := loop base present handle

theorem projectRows_run (ws rows : List (List Bool)) (h : ∀ m ∈ rows, m.length=ws.length) (s : S) :
    projectRows.Within ({s with base:=table rows,input:=payload ws,bits:=[],width:=[],temp:=[],count:=[],saved:=[]}:S).mem
      (rows.length*(100*(ws.length+(payload ws).length+1)^2+1)+1)
      ({s with base:=[],input:=payload ws,bits:=[],width:=[],temp:=[],count:=[],saved:=[],out:=(wordsOut ws rows).reverse++s.out}:S).mem := by
  induction rows generalizing s with
  | nil =>
    have stop := done (k:=base) (test:=present) (p:=handle)
      (m:=({s with base:=[],input:=payload ws,bits:=[],width:=[],temp:=[],count:=[],saved:=[]}:S).mem) (by rfl)
    exact ⟨1,by simp,by simpa [projectRows,table,pack,wordsOut] using stop⟩
  | cons x xs ih =>
    let items := x.zip ws
    have hx := h x (by simp)
    obtain ⟨hf,hl⟩ := zip_parts x ws hx
    have length : items.length=ws.length := by simp [items,hx]
    have head (ys : List (List Bool)) : marked (table ys).head? = false := by
      cases ys <;> simp [table,pack,MaskTable.row,token,marked]
    obtain ⟨t,ht,trace⟩ := handle_run items (table xs) (head xs) s
    have flag : flags items = pack (x.map some) := by
      unfold flags
      change pack (items.map (some ∘ Prod.fst)) = _
      rw [←List.map_map,hf]
    have input (y : List Bool) (ys : List (List Bool)) :
        table (y::ys) = false :: (pack (y.map some) ++ table ys) := by
      simp [table,MaskTable.row,pack,token,List.flatMap_append]
    let u : S := {s with out:=(rowWord items).reverse++s.out}
    have start : handle.Run ({s with base:=table (x::xs),input:=payload ws,bits:=[],width:=[],temp:=[],count:=[],saved:=[]}:S).mem t
        ({u with base:=table xs,input:=payload ws,bits:=[],width:=[],temp:=[],count:=[],saved:=[]}:S).mem := by
      simpa [u,input,flag,labels,items,hl] using trace
    obtain ⟨v,hv,rest⟩ := ih (fun m hm => h m (by simp [hm])) u
    have go := more (k:=base) (test:=present)
      (m:=({s with base:=table (x::xs),input:=payload ws,bits:=[],width:=[],temp:=[],count:=[],saved:=[]}:S).mem)
      (by simp [input,present]) start rest
    refine ⟨1+t+v,?_,?_⟩
    · change t ≤ 100*(items.length + (payload (labels items)).length+1)^2 at ht
      rw [length,show labels items=ws from hl] at ht
      rw [List.length_cons,Nat.succ_mul]
      omega
    · simpa [projectRows,u,wordsOut,items,List.reverse_append,List.append_assoc] using go

private def remember := duplicateUnary units mark temp >>> transfer temp units

private theorem remember_run (b : ℕ) (s : S) :
    remember.Run ({s with units:=marks b,mark:=[],temp:=[]}:S).mem (4*b+2)
      ({s with units:=marks b,mark:=marks b,temp:=[]}:S).mem := by
  let a : S := {s with units:=marks b,mark:=[],temp:=[]}
  let d : S := {s with units:=[],mark:=marks b,temp:=marks b}
  have t : (duplicateUnary units mark temp).Run a.mem (2*b+1) d.mem := by
    simpa [a,d,marks] using duplicate_run units mark temp (by decide) (by decide) (by decide) b a.mem rfl
  have f : (transfer temp units).Run d.mem (2*b+1) ({s with units:=marks b,mark:=marks b,temp:=[]}:S).mem := by
    simpa [d,marks] using transfer_run temp units (by decide) d.mem (marks b) rfl
  have tr := Block.seq t f
  have eq : (2*b+1)+(2*b+1)=4*b+2 := by omega
  rw [eq] at tr; exact tr

private def prefixStep : Block R := atom (.drop mark (.push temp true (.push input false (.stop none))))
private def prefixLoop := loop mark present prefixStep
private def powerHeader := push input true >>> prefixLoop >>> push input false >>> transfer temp input >>> push input true

private theorem prefixLoop_run (b : ℕ) (s : S) :
    prefixLoop.Run ({s with mark:=marks b}:S).mem (2*b+1)
      ({s with mark:=[],temp:=marks b++s.temp,input:=List.replicate b false++s.input}:S).mem := by
  induction b generalizing s with
  | zero =>
    simpa [prefixLoop,marks] using (done (k:=mark) (test:=present) (p:=prefixStep) (m:=({s with mark:=[]}:S).mem) (by rfl))
  | succ b ih =>
    let u : S := {s with temp:=true::s.temp,input:=false::s.input}
    have st : prefixStep.Run ({s with mark:=marks (b+1)}:S).mem 1 ({u with mark:=marks b}:S).mem := by
      apply atom_run; simp [Action.run,u,marks,List.replicate_succ]
    have go := more (k:=mark) (test:=present) (m:=({s with mark:=marks (b+1)}:S).mem)
      (by simp [marks,present,List.replicate_succ]) st (ih u)
    have ext (val : Bool) (tail : List Bool) : List.replicate b val ++val::tail = List.replicate (b+1) val ++tail := by
      rw [List.replicate_add]; simp [List.append_assoc]
    have eq : 1+1+(2*b+1)=2*(b+1)+1 := by omega
    rw [eq] at go
    simpa [u,marks,ext,prefixLoop] using go

theorem power_bits (b : ℕ) : (2^b).bits = List.replicate b false ++ [true] := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [pow_succ,Nat.mul_comm,Nat.bit0_bits _ (by positivity),ih,List.replicate_succ,List.cons_append]

private theorem powerHeader_run (b : ℕ) (s : S) :
    powerHeader.Run ({s with mark:=marks b,temp:=[]}:S).mem (4*b+5)
      ({s with mark:=[],temp:=[],input:=enc (2^b).bits ++s.input}:S).mem := by
  let a : S := {s with mark:=marks b,temp:=[]}
  let c : S := {a with input:=true::s.input}
  let d : S := {s with mark:=[],temp:=marks b,input:=List.replicate b false++true::s.input}
  let e : S := {d with input:=false::d.input}
  let f : S := {e with input:=marks b++e.input,temp:=[]}
  have ac : (push input true).Run a.mem 1 c.mem := by simpa [a,c] using push_run input true a.mem
  have cd : prefixLoop.Run c.mem (2*b+1) d.mem := by simpa [a,c,d] using prefixLoop_run b c
  have de : (push input false).Run d.mem 1 e.mem := by simpa [e] using push_run input false d.mem
  have ef : (transfer temp input).Run e.mem (2*b+1) f.mem := by
    simpa [d,e,f,marks] using transfer_run temp input (by decide) e.mem (marks b) rfl
  have fh : (push input true).Run f.mem 1 ({s with mark:=[],temp:=[],input:=enc (2^b).bits++s.input}:S).mem := by
    simpa [d,e,f,enc,marks,power_bits,List.replicate_succ,List.append_assoc] using push_run input true f.mem
  have go := Block.seq (p:=push input true) (q:=prefixLoop >>> push input false >>> transfer temp input >>> push input true) ac
    (Block.seq cd (Block.seq de (Block.seq ef fh)))
  have eq : 1+((2*b+1)+(1+((2*b+1)+1)))=4*b+5 := by omega
  rw [eq] at go; exact go

def powerProgram := readNumber false >>> remember >>> push base false >>> MaskTable.build >>> projectRows >>>
  drain input >>> transfer out input >>> powerHeader
def machine := BitStacks.machine powerProgram.entry input powerProgram.code
def familyBits (ws : List (List Bool)) := enc (2^ws.length).bits ++ wordsOut ws (masks ws.length)

def powerBudget (b data rows : ℕ) :=
  wordCost b + ((4*b+2) + (1 + ((b*(20*((b+1)*2^b)+6)+1) +
    (2^b*(100*(b+data+1)^2+1)+1 + ((2*data+1) + ((2*rows+1)+(4*b+5)))))))

theorem power_within (ws : List (List Bool)) :
    powerProgram.Within (isolated input (enc ws.length.bits ++ payload ws))
      (powerBudget ws.length (payload ws).length (wordsOut ws (masks ws.length)).length)
      (isolated input (familyBits ws)) := by
  let z : S := {}
  let state (v : List Bool) : S := {input:=v}
  let b := ws.length
  let data := payload ws
  let rows := wordsOut ws (masks b)
  let a : S := {input:=data,units:=marks b}
  let c : S := {a with mark:=marks b}
  let d : S := {c with base:=[false]}
  let e : S := {c with base:=table (masks b),units:=[]}
  let f : S := {input:=data,mark:=marks b,out:=rows.reverse}
  let i : S := {f with input:=[]}
  let j : S := {i with input:=rows,out:=[]}
  have st : (readNumber false).Within (state (enc b.bits ++data)).mem (wordCost b) a.mem := by
    simpa [z,state,a,stash] using number_run false b data z rfl rfl rfl rfl
  have ac : remember.Run a.mem (4*b+2) c.mem := by simpa [a,c] using remember_run b a
  have cd : (push base false).Run c.mem 1 d.mem := by simpa [c,d] using push_run base false c.mem
  have de : MaskTable.build.Within d.mem (b*(20*((b+1)*2^b)+6)+1) e.mem := by
    have tr := MaskTable.build_run b b 0 (by omega) c
    rw [tokens_rows b] at tr
    simpa [d,e,table,tokens,pack,token] using tr
  have ef : projectRows.Within e.mem (2^b*(100*(b+data.length+1)^2+1)+1) f.mem := by
    simpa [e,c,a,b,f,data,rows,masks_length,z] using projectRows_run ws (masks b)
      (fun m hm => (masks_mem b m).mp hm) ({z with mark:=marks b}:S)
  have fi : (drain input).Run f.mem (2*data.length+1) i.mem := by
    simpa [i] using drain_run input f.mem data rfl
  have ij : (transfer out input).Run i.mem (2*rows.length+1) j.mem := by
    simpa [j,i,f] using transfer_run out input (by decide) i.mem rows.reverse rfl
  have jend : powerHeader.Run j.mem (4*b+5) (state (familyBits ws)).mem := by
    simpa [j,i,f,state,familyBits,b,rows] using powerHeader_run b j
  have tr := st.seq (ac.within.seq (cd.within.seq (de.seq (ef.seq (fi.within.seq (ij.within.seq jend.within))))))
  have iso (v : List Bool) : isolated (K:=R) input v = (state v).mem := by funext r; cases r <;> rfl
  have run : powerProgram.Within (isolated input (enc b.bits ++data)) (powerBudget b data.length rows.length)
      (isolated input (familyBits ws)) := by rw [iso,iso]; exact tr
  exact run

theorem power_run (ws : List (List Bool)) :
    HMBinPacking.OutputsWithin machine (enc ws.length.bits ++ payload ws) (familyBits ws)
      (powerBudget ws.length (payload ws).length (wordsOut ws (masks ws.length)).length) :=
  (power_within ws).outputs _ _ _

end SingleExpBisect.FamilyTape


set_option autoImplicit false
open SingleExpBisect.ShrinkMachine SingleExpBisect.MaskTable SingleExpBisect.FamilyRow SingleExpBisect.FamilyTape
open MinBisectFPT SingleExpBisect.Main
namespace SingleExpBisect.BagPowerset

def pick {α : Type} : List Bool → List α → List α
  | false::xs,_::ys => pick xs ys
  | true::xs,y::ys => y::pick xs ys
  | _,_ => []

private theorem pick_sublist {α : Type} (ms : List Bool) (ys : List α) : (pick ms ys).Sublist ys := by
  induction ms generalizing ys with
  | nil => simp [pick]
  | cons m ms ih =>
    cases ys with
    | nil => simp [pick]
    | cons y ys =>
      cases m with
      | false => exact (ih ys).cons _
      | true => exact (ih ys).cons_cons _

private theorem filter_sub {α : Type} [DecidableEq α] {ys xs : List α} (nd : xs.Nodup) (hs : ys.Sublist xs) :
    xs.filter (fun v => decide (v ∈ ys)) = ys := by
  induction hs with
  | slnil => rfl
  | @cons ys xs a h ih =>
    obtain ⟨hne,nd'⟩ := List.nodup_cons.mp nd
    have he : a ∉ ys := fun ha => hne (h.subset ha)
    simp [he,ih nd']
  | @cons_cons ys xs a h ih =>
    obtain ⟨hne,nd'⟩ := List.nodup_cons.mp nd
    have eq : xs.filter (fun v => decide (v ∈ a::ys)) = xs.filter (fun v => decide (v∈ys)) := by
      apply List.filter_congr
      intro v hv
      have hne' : v ≠ a := fun e => hne (e ▸ hv)
      simp [hne']
    change List.filter (fun x => decide (x ∈ a::ys)) (a::xs) = a::ys
    rw [List.filter_cons]
    simp only [List.mem_cons_self,decide_true,if_true,eq,ih nd']

noncomputable def member {n : ℕ} (B : Finset (Fin n)) (m : List Bool) : Finset (Fin n) :=
  (pick m (elts B)).toFinset

noncomputable def family {n : ℕ} (B : Finset (Fin n)) :=
  (masks B.card).map (member B)

private theorem member_elts {n : ℕ} (B : Finset (Fin n)) (m : List Bool) :
    elts (member B m) = pick m (elts B) := by
  classical
  have sub := (pick_sublist m (elts B)).trans (show (elts B).Sublist (List.finRange n) from List.filter_sublist)
  calc
    _ = (List.finRange n).filter (fun v => decide (v ∈ pick m (elts B))) := by
      apply List.filter_congr
      intro v _
      simp [member]
    _ = _ := filter_sub (List.nodup_finRange n) sub

private theorem picked_words {α : Type} (f : α → List Bool) (m : List Bool) (xs : List α) :
    MaskSelect.kept (m.zip (xs.map f)) = (pick m xs).map f := by
  induction m generalizing xs with
  | nil => simp [MaskSelect.kept,pick]
  | cons m ms ih =>
    cases xs <;> cases m <;> simp [MaskSelect.kept,pick,ih]

theorem member_word {n : ℕ} (B : Finset (Fin n)) (m : List Bool) :
    rowWord (m.zip (words B)) = encodeSet (member B m) := by
  classical
  have eq : MaskSelect.kept (m.zip (words B)) = words (member B m) := by
    simp only [words,picked_words,member_elts]
  rw [←set_code,rowWord,eq,setCode]
  rw [show (words (member B m)).length = (member B m).card by simp [words,elts_size]]

theorem family_bits {n : ℕ} (B : Finset (Fin n)) :
    familyBits (words B) = encodeFamily (family B) := by
  classical
  have len : (words B).length = B.card := by simp [words,elts_size]
  unfold familyBits encodeFamily family wordsOut
  simp only [len,List.length_map,masks_length,List.flatMap_map]
  have natEq (a : ℕ) : enc a.bits = ExponomialAssortment.FPTAS.encodeNat a := by
    simp [enc,ExponomialAssortment.FPTAS.encodeNat,List.append_assoc]
  rw [natEq]
  congr 1
  apply List.flatMap_congr
  intro m _
  exact member_word B m

private theorem pick_filter {α : Type} (f : α → Bool) (xs : List α) :
    pick (xs.map f) xs = xs.filter f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h,pick,ih]

theorem mem_family {n : ℕ} (B D : Finset (Fin n)) : D ∈ family B ↔ D ⊆ B := by
  classical
  constructor
  · intro h
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp h
    intro v hv
    have hy := (pick_sublist m (elts B)).subset (List.mem_toFinset.mp hv)
    exact (List.mem_filter.mp hy).2 |> of_decide_eq_true
  · intro h
    let m := (elts B).map (fun v => decide (v∈D))
    apply List.mem_map.mpr
    refine ⟨m,(masks_mem _ _).mpr (by simp [m,elts_size]),?_⟩
    ext v
    simp [member,m,pick_filter,elts]
    tauto

theorem family_len {n : ℕ} (B : Finset (Fin n)) : (family B).length = 2^B.card := by
  simp [family,masks_length]

end SingleExpBisect.BagPowerset

namespace BitStacks.Block
variable {K : Type} [DecidableEq K]

def withStack (p : Block K) : Block (Option K) where
  L := p.L
  entry := p.entry
  code l := (p.code l).rename ⟨some,Option.some_injective _⟩ id

def frame (m : Mem K) (keep : List Bool) : Mem (Option K) := fun o => o.elim keep m

theorem Run.frame {p : Block K} {m n t} (hp : p.Run m t n) (keep : List Bool) :
    p.withStack.Run (Block.frame m keep) t (Block.frame n keep) := by
  let r : K ↪ Option K := ⟨some,Option.some_injective _⟩
  have impl (l : p.L) : p.withStack.code l = (p.code l).rename r (fun q => q.elim none some) := by
    have hid : (fun q : Option p.L => q.elim none some) = id := by funext q; cases q <;> rfl
    rw [hid]; rfl
  obtain ⟨v,trace,ag,out⟩ := hp.rename r id none p.withStack.code impl (Block.frame m keep) (fun _ => rfl)
  have eqn : v=Block.frame n keep := by
    funext q; cases q with
    | none => exact out none (fun k => by simp [r])
    | some j => exact ag j
  rw [eqn] at trace; exact trace

theorem Within.frame {p : Block K} {m n t} (hp : p.Within m t n) (keep : List Bool) :
    p.withStack.Within (Block.frame m keep) t (Block.frame n keep) := by
  obtain ⟨s,hs,run⟩ := hp
  exact ⟨s,hs,run.frame keep⟩

theorem frame_set_here (m : Mem K) (v old : List Bool) :
    setWord (frame m old) none v = frame m v := by funext q; cases q <;> simp [setWord,frame]
theorem frame_set_there (m : Mem K) (k : K) (v old : List Bool) :
    setWord (frame m old) (some k) v = frame (setWord m k v) old := by
  funext q; cases q with
  | none => simp [setWord,frame]
  | some i =>
    by_cases eqn : i = k
    · subst i; simp [setWord,frame]
    · simp [setWord,frame,Function.update_of_ne eqn,Function.update_of_ne (show some i ≠ some k by simpa)]
end BitStacks.Block

set_option autoImplicit false
namespace SingleExpBisect.LimitRows
open SingleExpBisect.ShrinkMachine
open BitStacks Block R

/-- Compare in unary, recording all consumed units and all consumed capacity
for restoration. A mark is left for each unit beyond the cap. -/
private def debit : Block R := atom (.peek base fun a =>
  .drop units (.push temp true (if present a then .drop base (.push width true (.stop none))
                              else .push mark true (.stop none))))
private def examine := loop units present debit
def compareCap := examine >>> transfer width base >>> transfer temp units

private theorem examine_run (j c : ℕ) (s : S) :
    examine.Run ({s with units:=marks j,base:=marks c}:S).mem (2*j+1)
      ({s with units:=[],base:=marks (c-j),width:=marks (min j c)++s.width,temp:=marks j++s.temp,mark:=marks (j-c)++s.mark}:S).mem := by
  induction j generalizing c s with
  | zero =>
    simpa [examine,marks] using done (k:=units) (test:=present) (p:=debit)
      (m:=({s with units:=[],base:=marks c}:S).mem) (by rfl)
  | succ j ih =>
    cases c with
    | zero =>
      let z : S := {s with mark:=true::s.mark,temp:=true::s.temp}
      let a : S := {s with units:=marks (j+1),base:=[]}
      have step : debit.Run a.mem 1 ({z with units:=marks j,base:=[]}:S).mem := by
        apply atom_run; simp [debit,Action.run,z,a,marks,List.replicate_succ,present]
      have go := more (k:=units) (test:=present) (m:=a.mem) (by simp [a,marks,List.replicate_succ,present]) step (ih 0 z)
      have rep (l : List Bool) : marks j ++true::l = marks (j+1)++l := by
        simp [marks,List.replicate_add,List.append_assoc]
      have time : 1+1+(2*j+1)=2*(j+1)+1 := by omega
      rw [time] at go
      simpa [examine,a,z,rep,show marks 0=[] from rfl] using go
    | succ c =>
      let z : S := {s with width:=true::s.width,temp:=true::s.temp}
      let a : S := {s with units:=marks (j+1),base:=marks (c+1)}
      have step : debit.Run a.mem 1 ({z with units:=marks j,base:=marks c}:S).mem := by
        apply atom_run; simp [debit,Action.run,z,a,marks,List.replicate_succ,present]
      have go := more (k:=units) (test:=present) (m:=a.mem) (by simp [a,marks,List.replicate_succ,present]) step (ih c z)
      have rep (v : ℕ) (l : List Bool) : marks v ++true::l = marks (v+1)++l := by
        simp [marks,List.replicate_add,List.append_assoc]
      have time : 1+1+(2*j+1)=2*(j+1)+1 := by omega
      rw [time] at go
      simpa [examine,a,z,rep,Nat.succ_min_succ] using go

theorem compare_run (j c : ℕ) (s : S) :
    compareCap.Within ({s with units:=marks j,base:=marks c,width:=[],temp:=[],mark:=[]}:S).mem (6*j+3)
      ({s with units:=marks j,base:=marks c,width:=[],temp:=[],mark:=marks (j-c)}:S).mem := by
  let z : S := {s with width:=[],temp:=[],mark:=[]}
  let a : S := {z with units:=[],base:=marks (c-j),width:=marks (min j c),temp:=marks j,mark:=marks (j-c)}
  let b : S := {a with width:=[],base:=marks c}
  have ex : examine.Run ({z with units:=marks j,base:=marks c}:S).mem (2*j+1) a.mem := by
    simpa [z,a] using examine_run j c z
  have restore : marks (min j c) ++ marks (c-j) = marks c := by
    rw [marks,marks,marks,←List.replicate_add]; congr 1; omega
  have br : (transfer width base).Run a.mem (2*(min j c)+1) b.mem := by
    simpa [a,b,marks,←List.replicate_add,show min j c+(c-j)=c by omega] using
      transfer_run width base (by decide) a.mem (marks (min j c)) rfl
  have ur : (transfer temp units).Run b.mem (2*j+1)
      ({s with units:=marks j,base:=marks c,width:=[],temp:=[],mark:=marks (j-c)}:S).mem := by
    simpa [a,b,z,marks] using transfer_run temp units (by decide) b.mem (marks j) rfl
  exact (Block.seq ex (Block.seq br ur)).within.mono (by omega)

end SingleExpBisect.LimitRows

set_option autoImplicit false
namespace SingleExpBisect.LimitRows
open SingleExpBisect.ShrinkMachine SingleExpBisect.MaskSelect
open BitStacks Block R

def rowBits (ws : List (List Bool)) := enc ws.length.bits ++ payload ws

private def accept := transfer saved temp >>> transfer temp out >>> transfer count bits >>> increment >>> transfer bits count
private def reject := drain saved >>> drain mark
private def process := choice mark present reject accept
def rowLimit := readNumber true >>> compareCap >>> capture >>> process

private theorem accept_run (row : List Bool) (i : ℕ) (s : S) :
    accept.Within ({s with saved:=row.reverse,temp:=[],count:=i.bits.reverse,bits:=[]}:S).mem
      (4*row.length + 10*(i+1) + 8)
      ({s with saved:=[],temp:=[],count:=(i+1).bits.reverse,bits:=[],out:=row.reverse++s.out}:S).mem := by
  let a : S := {s with saved:=row.reverse,temp:=[],count:=i.bits.reverse,bits:=[]}
  let b : S := {a with saved:=[],temp:=row}
  let c : S := {b with temp:=[],out:=row.reverse++s.out}
  let d : S := {c with count:=[],bits:=i.bits}
  let e : S := {d with bits:=(i+1).bits}
  have ab : (transfer saved temp).Run a.mem (2*row.length+1) b.mem := by
    simpa [a,b] using transfer_run saved temp (by decide) a.mem row.reverse rfl
  have bc : (transfer temp out).Run b.mem (2*row.length+1) c.mem := by
    simpa [b,c] using transfer_run temp out (by decide) b.mem row rfl
  have cd : (transfer count bits).Run c.mem (2*i.bits.length+1) d.mem := by
    simpa [a,b,c,d] using transfer_run count bits (by decide) c.mem i.bits.reverse rfl
  have de : increment.Run d.mem (4*ones i.bits+3) e.mem := by
    simpa [a,b,c,d,e,inc_bits] using increment_run i.bits d
  have ef : (transfer bits count).Run e.mem (2*(i+1).bits.length+1)
      ({s with saved:=[],temp:=[],count:=(i+1).bits.reverse,bits:=[],out:=row.reverse++s.out}:S).mem := by
    simpa [a,b,c,d,e] using transfer_run bits count (by decide) e.mem (i+1).bits rfl
  have _ := bounded_ones i.bits
  have _ := SingleExpBisect.FamilyRow.bits_bound i
  have _ := SingleExpBisect.FamilyRow.bits_bound (i+1)
  exact (Block.seq ab (Block.seq bc (Block.seq cd (Block.seq de ef)))).within.mono (by omega)

def rowBudget (ws : List (List Bool)) (i : ℕ) := wordCost ws.length + (6*ws.length+3) +
  (1+5*(payload ws).length) + (4*(rowBits ws).length+10*(i+1)+2*ws.length+12)

theorem row_run (ws : List (List Bool)) (tail : List Bool) (cap i : ℕ) (s : S) :
    rowLimit.Within ({s with input:=rowBits ws++tail,base:=marks cap,count:=i.bits.reverse,saved:=[],width:=[],bits:=[],temp:=[],units:=[],mark:=[]}:S).mem
      (rowBudget ws i)
      ({s with input:=tail,base:=marks cap,count:=(if ws.length ≤ cap then (i+1).bits else i.bits).reverse,saved:=[],width:=[],bits:=[],temp:=[],units:=[],mark:=[],out:=(if ws.length ≤ cap then (rowBits ws).reverse++s.out else s.out)}:S).mem := by
  let z : S := {s with input:=tail,base:=marks cap,count:=i.bits.reverse,saved:=[],width:=[],bits:=[],temp:=[],units:=[],mark:=[]}
  let data := payload ws
  let header := enc ws.length.bits
  let a : S := {z with input:=header++(data++tail)}
  let b : S := {z with input:=data++tail,units:=marks ws.length,saved:=header.reverse}
  let c : S := {b with mark:=marks (ws.length-cap)}
  let d : S := {c with input:=tail,units:=[],saved:=(rowBits ws).reverse}
  have ab : (readNumber true).Within a.mem (wordCost ws.length) b.mem := by
    simpa [a,b,z,header,stash] using number_run true ws.length (data++tail) z rfl rfl rfl rfl
  have bc : compareCap.Within b.mem (6*ws.length+3) c.mem := by
    exact compare_run ws.length cap b
  have cd : capture.Within c.mem (1+5*data.length) d.mem := by
    simpa [a,b,c,d,z,header,data,rowBits,List.reverse_append] using capture_run ws tail c
  suffices dd : process.Within d.mem (4*(rowBits ws).length+10*(i+1)+2*ws.length+12)
      ({z with count:=(if ws.length ≤ cap then (i+1).bits else i.bits).reverse,out:=(if ws.length ≤ cap then (rowBits ws).reverse++s.out else s.out)}:S).mem by
    simpa [rowLimit,rowBudget,rowBits,a,z,header,data,List.append_assoc,Nat.add_assoc] using ab.seq (bc.seq (cd.seq dd))
  by_cases h : ws.length ≤ cap
  · have ok : ws.length-cap=0 := by omega
    obtain ⟨t,ht,trace⟩ := accept_run (rowBits ws) i d
    have go := no (k:=mark) (test:=present) (p:=reject) (m:=d.mem) (by simp [d,c,b,z,ok,marks,present]) trace
    exact ⟨1+t,by omega,by simpa [process,d,c,b,z,h,ok,marks] using go⟩
  · let e : S := {d with saved:=[]}
    have save : (drain saved).Run d.mem (2*(rowBits ws).length+1) e.mem := by
      simpa [d,e] using drain_run saved d.mem (rowBits ws).reverse rfl
    have markr : (drain mark).Run e.mem (2*(ws.length-cap)+1) ({z with out:=s.out}:S).mem := by
      simpa [e,d,c,b,z,marks] using drain_run mark e.mem (marks (ws.length-cap)) rfl
    have pos : ∃ u, ws.length-cap=u+1 := ⟨ws.length-cap-1,by omega⟩
    obtain ⟨u,hu⟩ := pos
    have go := yes (k:=mark) (test:=present) (q:=accept) (m:=d.mem) (by simp [d,c,hu,marks,List.replicate_succ,present])
      (Block.seq save markr)
    exact ⟨1+((2*(rowBits ws).length+1)+(2*(ws.length-cap)+1)),by omega,by simpa [process,reject,h] using go⟩
end SingleExpBisect.LimitRows

namespace SingleExpBisect.LimitRows
open SingleExpBisect.ShrinkMachine SingleExpBisect.MaskSelect
open BitStacks Block R

abbrev Rows := List (List (List Bool))
def body (xs : Rows) := xs.flatMap rowBits
def familyWord (xs : Rows) := enc xs.length.bits ++ body xs
def keptRows (cap : ℕ) (xs : Rows) := xs.filter fun ws => ws.length ≤ cap
private def eachRow := loop input present rowLimit
def scanBudget (cap : ℕ) : Rows → ℕ → ℕ
  | [],_ => 1
  | w::ws,i => 1+rowBudget w i+scanBudget cap ws (if w.length ≤ cap then i+1 else i)

private theorem each_run (xs : Rows) (cap i : ℕ) (s : S) :
    eachRow.Within ({s with input:=body xs,base:=marks cap,count:=i.bits.reverse,saved:=[],width:=[],bits:=[],temp:=[],units:=[],mark:=[]}:S).mem
      (scanBudget cap xs i)
      ({s with input:=[],base:=marks cap,count:=(i+(keptRows cap xs).length).bits.reverse,saved:=[],width:=[],bits:=[],temp:=[],units:=[],mark:=[],out:=(body (keptRows cap xs)).reverse++s.out}:S).mem := by
  induction xs generalizing i s with
  | nil =>
    simpa [eachRow,scanBudget,keptRows,body] using (done (k:=input) (test:=present) (p:=rowLimit)
      (m:=({s with input:=[],base:=marks cap,count:=i.bits.reverse,saved:=[],width:=[],bits:=[],temp:=[],units:=[],mark:=[]}:S).mem) rfl).within
  | cons w ws ih =>
    let cur : S := {s with input:=rowBits w++body ws,base:=marks cap,count:=i.bits.reverse,saved:=[],width:=[],bits:=[],temp:=[],units:=[],mark:=[]}
    have nonempty : present (cur.mem input).head? = true := by
      change present ((enc w.length.bits ++ payload w) ++ body ws).head? = true
      unfold enc
      cases h : List.replicate w.length.bits.length true <;> simp [present]
    obtain ⟨t,ht,tr⟩ := row_run w (body ws) cap i s
    by_cases ok : w.length ≤ cap
    · let z : S := {s with out:=(rowBits w).reverse ++ s.out}
      obtain ⟨v,hv,rest⟩ := ih (i+1) z
      simp only [if_pos ok] at tr
      have go := more (k:=input) (test:=present) (m:=cur.mem) nonempty tr rest
      have countEq : i+1+(keptRows cap ws).length = i+((keptRows cap ws).length+1) := by omega
      refine ⟨1+t+v,by simp [scanBudget,ok]; omega,?_⟩
      simpa [cur,eachRow,keptRows,body,z,ok,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using go
    · obtain ⟨v,hv,rest⟩ := ih i s
      simp only [if_neg ok] at tr
      have go := more (k:=input) (test:=present) (m:=cur.mem) nonempty tr rest
      exact ⟨1+t+v,by simp [scanBudget,ok]; omega,by simpa [cur,eachRow,keptRows,body,ok] using go⟩

def filterProgram := readNumber false >>> transfer units base >>> readWord false false >>> eachRow >>>
  drain base >>> transfer out input >>> transfer count bits >>> headerOut
def filterMachine := BitStacks.machine filterProgram.entry input filterProgram.code
def filterBudget (cap : ℕ) (xs : Rows) :=
  wordCost cap+((2*cap+1)+((4*xs.length.bits.length+3)+(scanBudget cap xs 0 +((2*cap+1)+
    ((2*(body (keptRows cap xs)).length+1)+((2*(keptRows cap xs).length.bits.length+1)+(6*(keptRows cap xs).length.bits.length+4)))))))

theorem filter_within (cap : ℕ) (xs : Rows) :
    filterProgram.Within (isolated input (enc cap.bits++familyWord xs)) (filterBudget cap xs)
      (isolated input (familyWord (keptRows cap xs))) := by
  let z : S := {}
  let a : S := {input:=familyWord xs,units:=marks cap}
  let b : S := {input:=familyWord xs,base:=marks cap}
  let c : S := {input:=body xs,base:=marks cap}
  let result := keptRows cap xs
  let num := result.length.bits
  let data := body result
  let d : S := {base:=marks cap,count:=num.reverse,out:=data.reverse}
  let e : S := {count:=num.reverse,out:=data.reverse}
  let f : S := {input:=data,count:=num.reverse}
  let g : S := {input:=data,bits:=num}
  let mem (x : List Bool) : S := {input:=x}
  have ab : (readNumber false).Within (mem (enc cap.bits++familyWord xs)).mem (wordCost cap) a.mem := by
    simpa [z,mem,a,stash] using number_run false cap (familyWord xs) z rfl rfl rfl rfl
  have bc : (transfer units base).Run a.mem (2*cap+1) b.mem := by
    simpa [a,b,marks] using transfer_run units base (by decide) a.mem (marks cap) rfl
  have cc : (readWord false false).Run b.mem (4*xs.length.bits.length+3) c.mem := by
    simpa [b,c,stash,familyWord] using read_run false false xs.length.bits (body xs) b rfl
  have dd : eachRow.Within c.mem (scanBudget cap xs 0) d.mem := by
    simpa [c,d,result,num,data,z] using each_run xs cap 0 z
  have ee : (drain base).Run d.mem (2*cap+1) e.mem := by
    simpa [d,e,marks] using drain_run base d.mem (marks cap) rfl
  have ff : (transfer out input).Run e.mem (2*data.length+1) f.mem := by
    simpa [e,f] using transfer_run out input (by decide) e.mem data.reverse rfl
  have gg : (transfer count bits).Run f.mem (2*num.length+1) g.mem := by
    simpa [f,g] using transfer_run count bits (by decide) f.mem num.reverse rfl
  have hh : headerOut.Run g.mem (6*num.length+4) (mem (familyWord result)).mem := by
    simpa [g,mem,data,num,familyWord] using headerOut_run num g
  have tr := ab.seq (bc.within.seq (cc.within.seq (dd.seq (ee.within.seq (ff.within.seq (gg.within.seq hh.within))))))
  have iso (w : List Bool) : isolated (K:=R) input w = (mem w).mem := by funext r; cases r <;> rfl
  rw [iso,iso]; exact tr

theorem filter_run (cap : ℕ) (xs : Rows) :
    HMBinPacking.OutputsWithin filterMachine (enc cap.bits++familyWord xs)
      (familyWord (keptRows cap xs)) (filterBudget cap xs) :=
  (filter_within cap xs).outputs _ _ _

def cappedProgram := readWord false false >>> eachRow >>> drain base >>> transfer out input >>> transfer count bits >>> headerOut
def cappedBudget (cap : ℕ) (xs : Rows) :=
  (4*xs.length.bits.length+3)+(scanBudget cap xs 0+((2*cap+1)+
    ((2*(body (keptRows cap xs)).length+1)+((2*(keptRows cap xs).length.bits.length+1)+(6*(keptRows cap xs).length.bits.length+4)))))

theorem capped_within (cap : ℕ) (xs : Rows) :
    cappedProgram.Within ({input:=familyWord xs,base:=marks cap}:S).mem (cappedBudget cap xs)
      ({input:=familyWord (keptRows cap xs)}:S).mem := by
  let z : S := {}
  let b : S := {input:=familyWord xs,base:=marks cap}
  let c : S := {input:=body xs,base:=marks cap}
  let result := keptRows cap xs
  let num := result.length.bits
  let data := body result
  let d : S := {base:=marks cap,count:=num.reverse,out:=data.reverse}
  let e : S := {count:=num.reverse,out:=data.reverse}
  let f : S := {input:=data,count:=num.reverse}
  let g : S := {input:=data,bits:=num}
  let mem (x : List Bool) : S := {input:=x}
  have cc : (readWord false false).Run b.mem (4*xs.length.bits.length+3) c.mem := by
    simpa [b,c,stash,familyWord] using read_run false false xs.length.bits (body xs) b rfl
  have dd : eachRow.Within c.mem (scanBudget cap xs 0) d.mem := by
    simpa [c,d,result,num,data,z] using each_run xs cap 0 z
  have ee : (drain base).Run d.mem (2*cap+1) e.mem := by
    simpa [d,e,marks] using drain_run base d.mem (marks cap) rfl
  have ff : (transfer out input).Run e.mem (2*data.length+1) f.mem := by
    simpa [e,f] using transfer_run out input (by decide) e.mem data.reverse rfl
  have gg : (transfer count bits).Run f.mem (2*num.length+1) g.mem := by
    simpa [f,g] using transfer_run count bits (by decide) f.mem num.reverse rfl
  have hh : headerOut.Run g.mem (6*num.length+4) (mem (familyWord result)).mem := by
    simpa [g,mem,data,num,familyWord] using headerOut_run num g
  exact cc.within.seq (dd.seq (ee.within.seq (ff.within.seq (gg.within.seq hh.within))))

end SingleExpBisect.LimitRows

namespace SingleExpBisect.LimitRows
open SingleExpBisect.ShrinkMachine
open BitStacks Block R
private def doubleAtom : Block (Option R) := atom (.drop (some units) (.push none true (.push none true (.stop none))))
def rememberTwice := loop (some units) present doubleAtom

theorem rememberTwice_run (k t : ℕ) (s : S) : rememberTwice.Run
    (frame ({s with units:=marks k}:S).mem (marks t)) (2*k+1)
    (frame ({s with units:=[]}:S).mem (marks (2*k+t))) := by
  induction k generalizing t with
  | zero =>
    simpa [rememberTwice,marks] using done (k:=some units) (test:=present) (p:=doubleAtom)
      (m:=frame ({s with units:=[]}:S).mem (marks t)) rfl
  | succ k ih =>
    let a := frame ({s with units:=marks (k+1)}:S).mem (marks t)
    have one : doubleAtom.Run a 1 (frame ({s with units:=marks k}:S).mem (marks (t+2))) := by
      apply atom_run
      change (none, setWord (setWord (setWord a (some units) (marks (k+1)).tail) none (true::marks t)) none (true::true::marks t)) = _
      simp [a,frame_set_here,frame_set_there,marks,List.replicate_succ]
    have go := more (k:=some units) (test:=present) (m:=a) (by simp [a,frame,present,marks,List.replicate_succ]) one (ih (t+2))
    have tm : 1+1+(2*k+1)=2*(k+1)+1 := by omega
    have rr : 2*k+(t+2)=2*(k+1)+t := by omega
    simpa [rememberTwice,a,tm,rr] using go
end SingleExpBisect.LimitRows

namespace SingleExpBisect.LimitRows
open SingleExpBisect.ShrinkMachine SingleExpBisect.FamilyRow
open BitStacks Block R
set_option autoImplicit false

private theorem row_wordCost (v : ℕ) {u : ℕ} (h : v ≤ u) : wordCost v ≤ 10*(u+1)^2 := by
  have hbits := (bits_bound v).trans h
  unfold wordCost
  calc
    _ ≤ 4*u+3+(1+u*(6*u+6)) := by gcongr
    _ ≤ _ := by nlinarith

private theorem row_bound (ws : List (List Bool)) (i u r : ℕ) (hc : ws.length ≤ u)
    (hw : (rowBits ws).length ≤ u) (hi : i≤r) :
    rowBudget ws i ≤ 100*(u+1)^2 + 10*(r+1) := by
  have hp : (payload ws).length ≤ u := by
    apply le_trans _ hw
    simp [rowBits]
  unfold rowBudget
  calc
    _ ≤ 10*(u+1)^2 + (6*u+3)+(1+5*u)+(4*u+10*(r+1)+2*u+12) := by
      gcongr; exact row_wordCost _ hc
    _ ≤ _ := by nlinarith

private theorem scan_bound (xs : Rows) (cap i u r : ℕ) (hi : i+xs.length≤r)
    (h : ∀ ws ∈xs, ws.length ≤ u ∧ (rowBits ws).length ≤ u) :
    scanBudget cap xs i ≤ xs.length*(101*(u+1)^2+10*(r+1))+1 := by
  induction xs generalizing i with
  | nil => simp [scanBudget]
  | cons w xs ih =>
    have hr := row_bound w i u r (h w (by simp)).1 (h w (by simp)).2 (by simp at hi; omega)
    have htail : (if w.length ≤ cap then i+1 else i)+xs.length ≤ r := by
      simp at hi; split <;> omega
    have rest := ih _ htail (fun v hv => h v (by simp [hv]))
    let K := 101*(u+1)^2+10*(r+1)
    change 1+rowBudget w i+scanBudget cap xs _ ≤ (xs.length+1)*K+1
    rw [Nat.succ_mul]
    change _ ≤ xs.length*K+1 at rest
    have pos : 0 < (u+1)^2 := by positivity
    have lt : 1+rowBudget w i ≤ K := by dsimp only [K]; omega
    omega

private theorem body_bound (xs : Rows) (u : ℕ) (h : ∀ ws ∈ xs, (rowBits ws).length ≤ u) :
    (body xs).length ≤ xs.length * u := by
  induction xs with
  | nil => simp [body]
  | cons w xs ih =>
    have hd := h w (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    change (rowBits w ++ body xs).length ≤ _
    simp only [List.length_append,List.length_cons,Nat.succ_mul]; omega

theorem capped_bound (cap u : ℕ) (xs : Rows) (h : ∀ ws∈xs, ws.length ≤ u ∧ (rowBits ws).length ≤ u) :
    cappedBudget cap xs ≤ 256*(xs.length+1)^2*(u+1)^2 + 2*cap + 32 := by
  let r := xs.length
  have s := scan_bound xs cap 0 u r (by simp [r]) h
  have count : (keptRows cap xs).length≤r := List.length_filter_le _ _
  have bodylen := body_bound (keptRows cap xs) u
    (fun ws hw => (h ws (List.mem_filter.mp hw).1).2)
  have ll := (bits_bound _).trans count
  have ll₀ : xs.length.bits.length ≤ r := bits_bound _
  unfold cappedBudget
  calc
    _ ≤ 4*r+3 + ((r*(101*(u+1)^2+10*(r+1))+1)+((2*cap+1)+
      ((2*(r*u)+1)+((2*r+1)+(6*r+4))))) := by
      gcongr; exact bodylen.trans (Nat.mul_le_mul_right _ count)
    _ ≤ _ := by dsimp only [r]; nlinarith [Nat.zero_le (xs.length^2*u),Nat.zero_le (xs.length^2*u^2),
                       Nat.zero_le (xs.length*u^2),Nat.zero_le (xs.length*u)]
end SingleExpBisect.LimitRows


set_option autoImplicit false
open scoped Classical
namespace SingleExpBisect.BagPowerset
open SingleExpBisect.Main MinBisectFPT ExponomialAssortment.FPTAS
open SingleExpBisect.ShrinkMachine SingleExpBisect.FamilyTape SingleExpBisect.LimitRows SingleExpBisect.MaskTable
open BitStacks Block R

def limited {n : ℕ} (c : ℕ) (xs : List (Finset (Fin n))) := xs.filter fun X => X.card ≤ c
theorem words_len {n : ℕ} (X : Finset (Fin n)) : (words X).length = X.card := by simp [words,elts_size]
theorem row_bits_code {n : ℕ} (X : Finset (Fin n)) : rowBits (words X) = encodeSet X := by
  rw [rowBits,words_len]; exact set_code X
theorem family_words {n : ℕ} (xs : List (Finset (Fin n))) : familyWord (xs.map words) = encodeFamily xs := by
  simp [familyWord,body,encodeFamily,encodeNat,enc,List.flatMap_map,Function.comp_def,row_bits_code]
theorem filtered_words {n : ℕ} (c : ℕ) (xs : List (Finset (Fin n))) :
    keptRows c (xs.map words)=(limited c xs).map words := by
  induction xs with
  | nil => simp [keptRows,limited]
  | cons x xs ih => by_cases h : x.card ≤ c <;> simp_all [keptRows,limited,words_len]

def graphFilter := (readNumber false).withStack >>> matrix.withStack >>> (readNumber false).withStack >>>
  rememberTwice >>> powerProgram.withStack >>> transfer none (some base) >>> cappedProgram.withStack
def graphFilterMachine := BitStacks.machine graphFilter.entry (some input) graphFilter.code

noncomputable def filterTime {n : ℕ} (k : ℕ) (B : Finset (Fin n)) :=
  wordCost n+((6*n^2+9*n+3)+(wordCost k+((2*k+1)+
    (powerBudget B.card (payload (words B)).length (wordsOut (words B) (masks (words B).length)).length+
    ((2*(2*k)+1)+cappedBudget (2*k) ((family B).map words))))))

theorem complete_within {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)) :
    graphFilter.Within (isolated (some input) (encodeInput G k ++ encodeSet B)) (filterTime k B)
      (isolated (some input) (encodeFamily (limited (2*k) (family B)))) := by
  let rs := rows G
  let ws := words B
  let L := family B
  let Rw := L.map words
  let rest := encodeSet B
  let kr := enc k.bits++rest
  let nr := rs.flatten++kr
  let z : S := {}
  let st (v : List Bool) : S := {input:=v}
  have eq : enc n.bits++nr = encodeInput G k ++ encodeSet B := by
    simp [nr,kr,rest,rs,rows,encodeInput,enc,encodeNat,List.flatMap_def,List.append_assoc]
  have nrows : rs.length=n := by simp [rs,rows]
  have valid : ∀ l∈rs,l.length=n := by intro l h; obtain ⟨_,_,rfl⟩ := List.mem_map.mp h; simp
  have a : (readNumber false).Within (st (enc n.bits++nr)).mem (wordCost n) ({input:=nr,units:=marks n}:S).mem := by
    simpa [st,z,stash] using number_run false n nr z rfl rfl rfl rfl
  have b : matrix.Within ({input:=nr,units:=marks n}:S).mem (6*n^2+9*n+3) (st kr).mem := by
    simpa [z,st,nr] using (matrix_run n rs nrows valid kr z).within
  have c : (readNumber false).Within (st kr).mem (wordCost k) ({input:=rest,units:=marks k}:S).mem := by
    simpa [z,st,kr,stash] using number_run false k rest z rfl rfl rfl rfl
  have d : rememberTwice.Within (frame ({input:=rest,units:=marks k}:S).mem []) (2*k+1)
      (frame (st rest).mem (marks (2*k))) := by
    simpa [st,marks] using (rememberTwice_run k 0 (st rest)).within
  have iso (w : List Bool) : isolated (K:=R) input w = (st w).mem := by funext r; cases r <;> rfl
  have p := power_within ws
  rw [iso,iso] at p
  have seteq : enc ws.length.bits ++ payload ws = rest := row_bits_code B
  have e : powerProgram.Within (st rest).mem
      (powerBudget B.card (payload ws).length (wordsOut ws (masks ws.length)).length) (st (familyWord Rw)).mem := by
    rw [seteq,family_bits,words_len] at p
    simpa [Rw,L,family_words,ws,words_len] using p
  let mid : S := {input:=familyWord Rw,base:=marks (2*k)}
  have f : (transfer none (some base)).Within (frame (st (familyWord Rw)).mem (marks (2*k)))
      (2*(2*k)+1) (frame mid.mem []) := by
    simpa [mid,st,frame_set_here,frame_set_there,marks,frame] using
      (transfer_run none (some base) (by decide) (frame (st (familyWord Rw)).mem (marks (2*k))) (marks (2*k)) rfl).within
  have g : cappedProgram.Within mid.mem (cappedBudget (2*k) Rw) (st (encodeFamily (limited (2*k) L))).mem := by
    simpa [mid,st,Rw,filtered_words,family_words] using capped_within (2*k) Rw
  have tr := (a.frame []).seq ((b.frame []).seq ((c.frame []).seq (d.seq ((e.frame (marks (2*k))).seq (f.seq (g.frame []))))))
  have iso' (w : List Bool) : isolated (K:=Option R) (some input) w = frame (st w).mem [] := by
    funext r; cases r with
    | none => rfl
    | some i => cases i <;> rfl
  have run : graphFilter.Within (isolated (some input) (encodeInput G k ++ encodeSet B)) (filterTime k B)
      (isolated (some input) (encodeFamily (limited (2*k) L))) := by
    rw [iso',iso',←eq]; exact tr
  exact run

end SingleExpBisect.BagPowerset

namespace SingleExpBisect.BagPowerset
open SingleExpBisect.ShrinkMachine SingleExpBisect.MaskTable SingleExpBisect.FamilyRow SingleExpBisect.FamilyTape SingleExpBisect.LimitRows
open MinBisectFPT SingleExpBisect.Main
open BitStacks Block R

private theorem nat_word_bound {v u : ℕ} (h : v ≤ u) : wordCost v ≤ 10*(u+1)^2 := by
  have hb := (bits_bound v).trans h
  unfold wordCost
  calc
    _ ≤ 4*u+3+(1+u*(6*u+6)) := by gcongr
    _ ≤ _ := by nlinarith

private theorem all_rows_bound {n : ℕ} (B : Finset (Fin n)) :
    (wordsOut (words B) (masks (words B).length)).length ≤ 2^B.card*((n+1)*(2*n+1)) := by
  rw [words_len]
  have run (ws : List (List Bool)) : (wordsOut (words B) ws).length ≤ ws.length*((n+1)*(2*n+1)) := by
    induction ws with
    | nil => simp [wordsOut]
    | cons m xs ih =>
      have row := setLength (member B m)
      rw [←member_word B m] at row
      change (rowWord (m.zip (words B)) ++ wordsOut (words B) xs).length ≤ _
      rw [List.length_append,List.length_cons,Nat.succ_mul]; omega
  exact (run _).trans_eq (by rw [masks_length])

def enumerationTime (b n k : ℕ) := 65536*4^b*(n+k+1)^4

theorem upper_time {n : ℕ} (B : Finset (Fin n)) (k : ℕ) : filterTime k B ≤ enumerationTime B.card n k := by
  let p := n+k+1
  let e := 2^B.card
  let u := 3*p^2
  have pne : 0<p := by dsimp [p]; omega
  have ene : 0<e := by dsimp [e]; positivity
  have bn : B.card≤n := by simpa using Finset.card_le_univ B
  have np : n≤p := by dsimp [p]; omega
  have kp : k≤p := by dsimp [p]; omega
  have bp : B.card≤p := bn.trans np
  have ca : (n+1)*(2*n+1) ≤ u := by dsimp [u,p]; nlinarith [Nat.zero_le (n*k)]
  have du : (payload (words B)).length ≤ u := by
    apply le_trans _ ((setLength B).trans ca)
    rw [←set_code]; simp [setCode]
  have rows := (all_rows_bound B).trans (Nat.mul_le_mul_left e ca)
  have nw := nat_word_bound np
  have kw := nat_word_bound kp
  have bw := nat_word_bound bp
  have length : ((family B).map words).length=e := by simp [family_len,e]
  have posu : n ≤ u := by dsimp [u,p]; nlinarith [Nat.zero_le (n*k)]
  have cb := capped_bound (2*k) u ((family B).map words) (by
    intro w hw; obtain ⟨X,_,rfl⟩ := List.mem_map.mp hw
    rw [words_len,row_bits_code]; exact ⟨(show X.card≤n by simpa using Finset.card_le_univ X).trans posu,(setLength X).trans ca⟩)
  rw [length] at cb
  have upper : filterTime k B ≤
    10*(p+1)^2+((6*p^2+9*p+3)+(10*(p+1)^2+((2*p+1)+
    ((10*(p+1)^2+((4*p+2)+(1+((p*(20*((p+1)*e)+6)+1)+
      (e*(100*(p+u+1)^2+1)+1+((2*u+1)+((2*(e*u)+1)+(4*p+5))))))))+
    ((2*(2*p)+1)+(256*(e+1)^2*(u+1)^2+2*(2*p)+32)))))) := by
    unfold filterTime powerBudget
    gcongr <;> first
      | exact cb.trans (by gcongr)
      | exact nw
      | exact kw
      | exact bw
      | exact np
      | exact kp
      | exact bp
      | exact du
      | exact rows
  have e4 : e^2 = 4^B.card := by dsimp [e]; rw [←Nat.pow_mul,Nat.mul_comm, Nat.pow_mul]
  calc
    _ ≤ _ := upper
    _ ≤ 65536*e^2*p^4 := by
      dsimp only [u]
      obtain ⟨x,hx⟩ := Nat.exists_eq_succ_of_ne_zero (show p≠0 by omega)
      obtain ⟨y,hy⟩ := Nat.exists_eq_succ_of_ne_zero (show e≠0 by omega)
      rw [hx,hy]
      nlinarith only [Nat.zero_le x,Nat.zero_le y,Nat.zero_le (x^2),Nat.zero_le (x^3),Nat.zero_le (x^4),Nat.zero_le (y^2),
        Nat.zero_le (x*y),Nat.zero_le (x^2*y),Nat.zero_le (x^3*y),Nat.zero_le (x^4*y),
        Nat.zero_le (x*y^2),Nat.zero_le (x^2*y^2),Nat.zero_le (x^3*y^2),Nat.zero_le (x^4*y^2)]
    _ = _ := by rw [e4]; rfl
end SingleExpBisect.BagPowerset


set_option autoImplicit false
open scoped Classical
namespace SingleExpBisect.BagPowerset
open SingleExpBisect.Main MinBisectFPT SingleExpBisect.ShrinkMachine
open BitStacks Block R

private theorem qualified_time (b n k q : ℕ) (qual : 2^b ≤ 2^(q*k)*(n+1)^q) :
    enumerationTime b n k ≤ stepBound (65536+(2*q+4)) k n := by
  let z := 2*q+4
  have kbound : k+1 ≤ 2^k := Nat.lt_two_pow_self
  have pbound : n+k+1 ≤ (n+1)*2^k := by
    calc
      _ ≤ (n+1)*(k+1) := by nlinarith [Nat.zero_le (n*k)]
      _ ≤ _ := Nat.mul_le_mul_left _ kbound
  have e4 : 4^b = (2^b)^2 := by rw [←Nat.pow_mul,Nat.mul_comm,Nat.pow_mul]
  have collapsed : (2^(q*k)*(n+1)^q)^2*((n+1)*2^k)^4 = 2^(z*k)*(n+1)^z := by
    rw [Nat.mul_pow,Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul,←Nat.pow_mul]
    dsimp [z]
    rw [show (2*q+4)*k=q*k*2+k*4 by ring,Nat.pow_add,Nat.pow_add,
      show 2*q=q*2 by omega]
    ring
  unfold enumerationTime
  rw [e4]
  calc
    _ ≤ 65536*(2^(q*k)*(n+1)^q)^2*((n+1)*2^k)^4 := by gcongr
    _ = 65536*2^(z*k)*(n+1)^z := by rw [Nat.mul_assoc,collapsed,Nat.mul_assoc]
    _ ≤ _ := by
      unfold stepBound
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul (by omega)
        exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by dsimp [z]; omega))
      · exact Nat.pow_le_pow_right (by omega) (by dsimp [z]; omega)

private theorem satisfies {n : ℕ} (B : Finset (Fin n)) (k : ℕ) (D : Finset (Fin n)) :
    D ∈ limited (2*k) (family B) ↔ D ⊆ B ∧ D.card ≤ 2*k := by
  simp [limited,mem_family]

private theorem limited_len {n : ℕ} (B : Finset (Fin n)) (k : ℕ) :
    (limited (2*k) (family B)).length ≤ 2^B.card :=
  (List.length_filter_le _ _).trans_eq (family_len B)

/-- On every registered encoding, one finite TM2 enumerates the exact bounded-size
powerset. Its bit-step estimate is exponential only in the bag size and polynomial
in n+k. Specializing the same machine to b=O(k+log(n+1)) gives all four clauses
and the parameterized time in the platform's original model. -/
theorem bounded_power_machine :
    ∃ M : Turing.TM2ComputableAux Bool Bool,
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)),
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (encodeInput G k ++ encodeSet B) (encodeFamily L)
            (65536 * 4^B.card * (n+k+1)^4) ∧
          (∀ D : Finset (Fin n), D ∈ L ↔ D ⊆ B ∧ D.card ≤ 2*k) ∧ L.length ≤ 2^B.card) ∧
      ∀ q : ℕ, ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)),
        2^B.card ≤ 2^(q*k)*(n+1)^q →
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (encodeInput G k ++ encodeSet B) (encodeFamily L) (stepBound C k n) ∧
          (∀ D ∈ L, D ⊆ B ∧ D.card ≤ 2*k) ∧
          (∀ D ∈ L, ∀ D' : Finset (Fin n), D' ⊆ D → D' ∈ L) ∧ L.toFinset.card ≤ stepBound C k n ∧
          ∀ A : Finset (Fin n), (A = ∅ ∨ (G.induce (A : Set _)).Connected) →
            cutSize G A ≤ k → (A ∩ B).card ≤ 2*k → A ∩ B ∈ L := by
  refine ⟨graphFilterMachine,?_,?_⟩
  · intro n G k B
    exact ⟨limited (2*k) (family B),((complete_within G k B).mono (upper_time B k)).outputs _ _ _,satisfies B k,limited_len B k⟩
  · intro q
    refine ⟨65536+(2*q+4),?_⟩
    intro n G k B admissible
    have cost := qualified_time _ _ _ _ admissible
    refine ⟨limited (2*k) (family B),((complete_within G k B).mono ((upper_time B k).trans cost)).outputs _ _ _,?_,?_,?_,?_⟩
    · intro D hD; exact (satisfies B k D).mp hD
    · intro D hD D' sub
      obtain ⟨hb,hsize⟩ := (satisfies B k D).mp hD
      exact (satisfies B k D').mpr ⟨sub.trans hb,(Finset.card_le_card sub).trans hsize⟩
    · apply (List.toFinset_card_le _).trans ((limited_len B k).trans _)
      apply le_trans _ cost
      unfold enumerationTime
      calc
        2^B.card ≤ 4^B.card := Nat.pow_le_pow_left (by decide) _
        _ = 1*4^B.card*1 := by rw [one_mul,mul_one]
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide : 1 ≤ 65536))
          (Nat.succ_le_of_lt (pow_pos (by omega) _))
    · intro A _ _ size; exact (satisfies B k _).mpr ⟨Finset.inter_subset_right,size⟩

end SingleExpBisect.BagPowerset

open scoped Classical
open SingleExpBisect.Main MinBisectFPT

theorem solution :
    ∃ M : Turing.TM2ComputableAux Bool Bool,
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)),
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (encodeInput G k ++ encodeSet B) (encodeFamily L)
            (65536 * 4^B.card * (n+k+1)^4) ∧
          (∀ D : Finset (Fin n), D ∈ L ↔ D ⊆ B ∧ D.card ≤ 2*k) ∧ L.length ≤ 2^B.card) ∧
      ∀ q : ℕ, ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)),
        2^B.card ≤ 2^(q*k)*(n+1)^q →
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (encodeInput G k ++ encodeSet B) (encodeFamily L) (stepBound C k n) ∧
          (∀ D ∈ L, D ⊆ B ∧ D.card ≤ 2*k) ∧
          (∀ D ∈ L, ∀ D' : Finset (Fin n), D' ⊆ D → D' ∈ L) ∧ L.toFinset.card ≤ stepBound C k n ∧
          ∀ A : Finset (Fin n), (A = ∅ ∨ (G.induce (A : Set _)).Connected) →
            cutSize G A ≤ k → (A ∩ B).card ≤ 2*k → A ∩ B ∈ L := SingleExpBisect.BagPowerset.bounded_power_machine
