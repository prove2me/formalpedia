-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorKeys.name_key_from_tables
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T05:42:35.197351+00:00
-- url     : https://prove2.me/submissions/4f3fc5b1-5c87-41ae-a376-b48dd5720431

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

section
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option linter.all false
set_option maxRecDepth 35000
set_option maxHeartbeats 4100000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
theorem source_loop {N:ℕ} {input:ℤ → ℤ} (ix last n cap:ℕ) (body:Program) (P:ℕ→State→Prop) (ne:ix≠last)
    (step:∀i<n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k≤1+rem*(cap+5) ∧ P n t :=by
  induction rem generalizing i s with
  | zero=>
    have eq:i=n:=by omega
    exact ⟨s,1,.stop (by rw [idx,lim];omega),by omega,eq ▸ start⟩
  | succ r ih=>
    have lt:i<n:=by omega
    obtain ⟨u,k,ex,tim,idx',lim',next⟩:=step i lt s start idx lim
    let v:=u.assign ix (u.reg ix+1)
    have vi:v.reg ix=((i+1:ℕ):ℤ):=by simp [v,State.assign,idx',idx]
    have vl:v.reg last=(n:ℤ)-1:=by simp [v,State.assign,Ne.symm ne,lim',lim]
    obtain ⟨t,z,more,tm,out⟩:=ih (i+1) (by omega) v next vi vl
    have full:Executes N input (chain [body,.op (.regular (.inc ix))]) s v (1+k+(1+1+1)):=.seq ex (.seq (.op rfl) (.skip _))
    exact ⟨t,_,.more (by rw [idx,lim];omega) full more,by rw [Nat.succ_mul];omega,out⟩

def forSetup (ix last len:ℕ) (s:State) := let u:=s.assign ix 0; let v:=u.assign last (u.reg len);v.assign last (v.reg last-1)
theorem source_for {N:ℕ} {input:ℤ → ℤ} (ix last len n cap:ℕ) (body:Program) (P:ℕ→State→Prop)
    (ne:ix≠last) (dis:len≠ix) (s:State) (size:s.reg len=(n:ℤ))
    (start:P 0 (forSetup ix last len s))
    (step:∀i<n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k≤9+n*(cap+5) ∧ P n t :=by
  let u:=forSetup ix last len s
  have fi:u.reg ix=0:=by simp [u,forSetup,State.assign,ne]
  have last':u.reg last=(n:ℤ)-1:=by simp [u,forSetup,State.assign,dis,size]
  obtain ⟨t,z,loop,tm,out⟩:=source_loop ix last n cap body P ne step 0 n (by omega) u start fi last'
  refine ⟨t,_,.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq loop (.skip _)))),by omega,out⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
inductive PrefixRun (N:ℕ) (input:ℤ → ℤ) : List Program → State → State → ℕ → Prop where
  | nil (s:State) : PrefixRun N input [] s s 0
  | cons {p ps s u t a z} : Executes N input p s u a → PrefixRun N input ps u t z →
    PrefixRun N input (p::ps) s t (1+a+z)
theorem PrefixRun.continue {N input ps s t z} (h:PrefixRun N input ps s t z)
    (q:Program) {u k} (tail:Executes N input q t u k):
    Executes N input (ps.foldr Program.seq q) s u (z+k):=by
  induction h with
  | nil=>simpa using tail
  | cons run _ ih=>
    simpa [Nat.add_assoc] using Executes.seq run (ih tail)
theorem PrefixRun.finish {N input ps s t z} (h:PrefixRun N input ps s t z):
    Executes N input (chain ps) s t (z+1):=h.continue .skip (.skip t)
end Logical
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def evalLine (n:ℕ) (m:ℤ → ℤ) : Program → State → Option (State×ℕ)
  | .skip,s=>some (s,1)
  | .op o,s=>o.next n m s
  | .seq p q,s=>do
    let (u,a)←evalLine n m p s
    let (t,b)←evalLine n m q u
    pure (t,1+a+b)
  | .cond i j p q,s=>do
    let (t,b)←if s.reg i ≤ s.reg j then evalLine n m p s else evalLine n m q s
    pure (t,1+b)
  | .loop _ _ _,_=>none
theorem evalLine_sound {n m} (p:Program) (s t:State) (k:ℕ) (ex:evalLine n m p s=some (t,k)):
    Executes n m p s t k:=by
  induction p generalizing s t k with
  | skip=>obtain ⟨rfl,rfl⟩:=Option.some.inj ex;exact .skip _
  | op=>exact .op ex
  | loop=>contradiction
  | seq p q a b=>
    cases h:evalLine n m p s with
    | none=>simp [evalLine,h] at ex
    | some z=>
      obtain ⟨u,au⟩:=z
      cases j:evalLine n m q u with
      | none=>simp [evalLine,h,j] at ex
      | some v=>obtain ⟨v,bu⟩:=v;simp [evalLine,h,j] at ex;obtain ⟨rfl,rfl⟩:=ex
                exact .seq (a _ _ _ h) (b _ _ _ j)
  | cond i j p q a b=>
    by_cases g:s.reg i ≤ s.reg j
    · cases h:evalLine n m p s with
      | none=>simp [evalLine,g,h] at ex
      | some z=>obtain ⟨u,au⟩:=z;simp [evalLine,g,h] at ex;obtain ⟨rfl,rfl⟩:=ex;exact .yes g (a _ _ _ h)
    · cases h:evalLine n m q s with
      | none=>simp [evalLine,g,h] at ex
      | some z=>obtain ⟨u,au⟩:=z;simp [evalLine,g,h] at ex;obtain ⟨rfl,rfl⟩:=ex;exact .no g (b _ _ _ h)

def writesOp (j:ℕ) : Operation → Bool
  | .regular (.store _ _)|.save _ _ _=>false
  | .regular (.set d _)|.regular (.copy d _)|.regular (.add d _ _)|.regular (.sub d _ _)|
    .regular (.inc d)|.regular (.dec d)|.regular (.load d _)|.multiply d _ _|.divide _ d _ _|
    .fetch d _ _|.shift d _ _=>j==d
  | .alloc d _=>j==d || j==8
  | .output=>j==82
def writesReg (j:ℕ) : Program → Bool
  | .skip=>false | .op o=>writesOp j o | .seq p q|.cond _ _ p q=>writesReg j p || writesReg j q
  | .loop _ _ p=>writesReg j p
theorem op_preserves {n input s t k} (o:Operation) (j:ℕ) (frame:writesOp j o=false)
    (ex:o.next n input s=some (t,k)):t.reg j=s.reg j:=by
  cases o with
  | regular o=>
    cases o <;> simp [writesOp] at frame <;> simp only [Operation.next,regularNext] at ex <;>
      (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;> simp [State.assign,frame]
  | multiply|divide|shift|fetch|save|alloc|output=>
    simp [writesOp] at frame
    simp only [Operation.next] at ex
    (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;>
      simp_all [State.assign,State.clear,State.save]
theorem Executes.preserves {n input p s t k} (ex:Executes n input p s t k) (j:ℕ) (off:writesReg j p=false):
    t.reg j=s.reg j:=by
  induction ex with
  | skip|stop=>rfl
  | op h=>exact op_preserves _ _ off h
  | seq _ _ ih jh=>obtain ⟨a,b⟩:=Bool.or_eq_false_iff.mp off;exact (jh b).trans (ih a)
  | yes _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).1
  | no _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).2
  | more _ _ _ ih jh=>exact (jh off).trans (ih off)
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open scoped Classical
theorem splitChain {N input} (ps:List Program) {s t:State} {k:ℕ} (ex:Executes N input (chain ps) s t k) :
    ∃z,PrefixRun N input ps s t z ∧ k=z+1:=by
  induction ps generalizing s t k with
  | nil=>cases ex;exact ⟨0,.nil _,rfl⟩
  | cons p ps ih=>
    change Executes N input (.seq p (chain ps)) s t k at ex
    cases ex with
    | seq left right=>
      obtain ⟨z,e,h⟩:=ih right
      exact ⟨_,.cons left e,by omega⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM



end
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option linter.all false
set_option maxRecDepth 35000
set_option maxHeartbeats 4100000
set_option autoImplicit false

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
/-- Registers outside the write set retain the values with which the loop started. -/
lemma outside_for {ix last len r : ℕ} {body : Program}
    (off : writesReg r (forCount ix last len body) = false) :
    r ≠ ix ∧ r ≠ last ∧ writesReg r body = false := by
  simpa [forCount,chain,writesReg,writesOp,and_assoc,and_left_comm,and_comm] using off

lemma counted {n : ℕ} {m : ℤ → ℤ} (ix last len count cap : ℕ) (body : Program)
    (s : State) (P : ℕ → State → Prop) (ne : ix ≠ last) (dis : len ≠ ix)
    (ixSafe : writesReg ix body = false) (lastSafe : writesReg last body = false)
    (size : s.reg len = (count : ℤ)) (init : P 0 s)
    (ignores : ∀ j u a v, a = ix ∨ a = last → P j u → P j (u.assign a v))
    (step : ∀ i < count, ∀ u, P i u →
      (∀ r, writesReg r (forCount ix last len body) = false → u.reg r = s.reg r) →
      u.reg ix = (i : ℤ) → ∃ t k, Executes n m body u t k ∧ k ≤ cap ∧ P (i+1) t) :
    ∃ t k, Executes n m (forCount ix last len body) s t k ∧
      k ≤ 9+count*(cap+5) ∧ P count t := by
  let Q := fun j u => P j u ∧ ∀ r, writesReg r (forCount ix last len body) = false → u.reg r = s.reg r
  have start : Q 0 (forSetup ix last len s) := by
    refine ⟨ignores _ _ _ _ (.inr rfl) (ignores _ _ _ _ (.inr rfl) (ignores _ _ _ _ (.inl rfl) init)),?_⟩
    intro r off
    obtain ⟨a,b,_⟩ := outside_for off
    simp [forSetup,State.assign,a,b]
  obtain ⟨t,k,run,tm,res,_⟩ := source_for (N:=n) (input:=m) ix last len count cap body Q ne dis s size start (by
    intro i hi u good idx _
    obtain ⟨t,k,ex,tm,next⟩ := step i hi u good.1 good.2 idx
    refine ⟨t,k,ex,tm,ex.preserves _ ixSafe,ex.preserves _ lastSafe,ignores _ _ _ _ (.inl rfl) next,?_⟩
    intro r off
    obtain ⟨a,_,b⟩ := outside_for off
    simpa [State.assign,a] using (ex.preserves r b).trans (good.2 r off))
  exact ⟨t,k,run,tm,res⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables

set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorKeys
private def pushStart : List Program := [
  .op (.shift 275 128 1),
  .op (.regular (.set 277 1)),
  .op (.regular (.add 274 275 277)),
  .op (.regular (.copy 128 274))
]
private def pushBody : List Program := [
  .op (.regular (.add 280 128 128)),
  .op (.regular (.copy 128 280))
]
private def pushEnd : List Program := [
  .op (.regular (.copy 131 128))
]
private def pointPrep : List Program := [
  .op (.regular (.set 384 1)),
  .op (.regular (.add 382 157 384)),
  .op (.regular (.copy 128 156)),
  .op (.regular (.copy 129 382))
]
private def acceptResult : List Program := [
  .op (.regular (.copy 380 131)),
  .op (.regular (.copy 156 380))
]
private def pairPrep : List Program := [
  .op (.regular (.copy 128 156)),
  .op (.regular (.copy 129 157))
]
private def secondPrep : List Program := [
  .op (.regular (.copy 393 131)),
  .op (.regular (.copy 156 393)),
  .op (.fetch 400 155 157),
  .op (.fetch 398 76 400),
  .op (.regular (.copy 128 156)),
  .op (.regular (.copy 129 398))
]
private def pairEnd : List Program := [
  .op (.regular (.copy 396 131)),
  .op (.regular (.copy 156 396))
]
private def startName : List Program := [
  .op (.regular (.set 374 0)),
  .op (.regular (.copy 156 374))
]
private def zeroPrep : List Program := [
  .op (.regular (.set 387 0)),
  .op (.regular (.copy 128 156)),
  .op (.regular (.copy 129 387))
]
private def zeroEnd : List Program := [
  .op (.regular (.copy 385 131)),
  .op (.regular (.copy 156 385))
]
private def endName : List Program := [
  .op (.regular (.copy 158 156))
]
private def pointAction := chain (pointPrep++[src_code_name_push]++acceptResult)
private def pairAction := chain (pairPrep++[src_code_name_push]++secondPrep++[src_code_name_push]++pairEnd)
private def pointBody := chain [.op (.fetch 377 153 157),.cond 6 377 pointAction .skip]
private def pairBody := chain [.op (.fetch 390 154 157),.cond 6 390 pairAction .skip]
private def pointLoop := forCount 157 376 64 pointBody
private def pairLoop := forCount 157 389 64 pairBody
private lemma pushCode : src_code_name_push=chain (pushStart++[forCount 130 279 129 (chain pushBody)]++pushEnd) := rfl
private lemma keyCode : src_name_key=chain (startName++[pointLoop]++zeroPrep++[src_code_name_push]++zeroEnd++[pairLoop]++endName) := rfl

private structure Intact (s t : State) : Prop where
  heap : t.heap=s.heap
  output : t.output=s.output
  closed : t.closed=s.closed
private lemma Intact.same (s : State) : Intact s s := ⟨rfl,rfl,rfl⟩
private lemma Intact.comp {s t u : State} (a : Intact s t) (b : Intact t u) : Intact s u :=
  ⟨b.heap.trans a.heap,b.output.trans a.output,b.closed.trans a.closed⟩
private def readsOp : Operation → Bool
  | .regular (.set ..) | .regular (.copy ..) | .regular (.inc ..) | .regular (.dec ..)
  | .regular (.add ..) | .regular (.sub ..) | .shift .. | .fetch .. => true
  | _ => false
private def reads : Program → Bool
  | .skip => true | .op a => readsOp a
  | .seq p q | .cond _ _ p q => reads p && reads q
  | .loop _ _ p => reads p
private lemma op_frame {n : ℕ} {m : ℤ→ℤ} {o : Operation} {s t : State} {k : ℕ}
    (r : readsOp o=true) (e : o.next n m s=some (t,k)) : Intact s t := by
  cases o <;> simp only [readsOp,Bool.false_eq_true] at r <;> try contradiction
  case regular o =>
    cases o <;> simp only [readsOp,Bool.false_eq_true] at r <;> try contradiction
    all_goals simp [Operation.next,regularNext] at e
    all_goals obtain ⟨rfl,rfl⟩ := e;exact ⟨rfl,rfl,rfl⟩
  case shift d a k =>
    simp [Operation.next] at e
    obtain ⟨rfl,rfl⟩ := e;exact ⟨rfl,rfl,rfl⟩
  case fetch d a i =>
    simp only [Operation.next] at e
    split at e <;> simp at e
    obtain ⟨rfl,rfl⟩ := e;exact ⟨rfl,rfl,rfl⟩
private lemma intact {n : ℕ} {m : ℤ→ℤ} {p : Program} {s t : State} {k : ℕ}
    (ex : Executes n m p s t k) (ok : reads p=true) : Intact s t := by
  induction ex with
  | skip => exact .same _
  | op e => exact op_frame ok e
  | seq _ _ ih jh => exact (ih (Bool.and_eq_true_iff.mp ok).1).comp (jh (Bool.and_eq_true_iff.mp ok).2)
  | yes _ _ ih => exact ih (Bool.and_eq_true_iff.mp ok).1
  | no _ _ ih => exact ih (Bool.and_eq_true_iff.mp ok).2
  | stop => exact .same _
  | more _ _ _ ih jh => exact (ih ok).comp (jh ok)

private def acc (ls : List ℕ) := Naming.code ls.reverse
private lemma snoc (ls : List ℕ) (v : ℕ) : acc (ls++[v])=Naming.push (acc ls) v := by simp [acc,Naming.code]

private lemma push_value (n a d : ℕ) (m : ℤ→ℤ) (s : State) (base : s.reg 128=(a:ℤ)) (digit : s.reg 129=(d:ℤ)) :
    ∃ t k,Executes n m src_code_name_push s t k ∧ k≤32+10*d ∧ t.reg 131=(Naming.push a d:ℤ) := by
  have first : ∃ t,evalLine n m (chain pushStart) s=some (t,13) ∧ t.reg 128=(Naming.push a 0:ℤ) := by
    simp [pushStart,chain,evalLine,Operation.next,regularNext,State.assign,base,Naming.push]
  obtain ⟨u,e,initial⟩ := first
  have start := evalLine_sound _ _ _ _ e
  let P := fun j (t : State) => t.reg 128=(Naming.push a j:ℤ)
  obtain ⟨v,k,loop,kt,finalVal⟩ := GeometryTables.counted (n:=n) (m:=m) 130 279 129 d 5 (chain pushBody) u P
    (by decide) (by decide) (by decide) (by decide) ((start.preserves _ (by decide)).trans digit) initial
    (by intro j w r x h p;rcases h with rfl|rfl <;> simpa [P,State.assign] using p) (by
      intro j hj w good _ _
      change w.reg 128=(Naming.push a j:ℤ) at good
      have step : ∃t,evalLine n m (chain pushBody) w=some (t,5) ∧ t.reg 128=(Naming.push a (j+1):ℤ) := by
        simp [pushBody,chain,evalLine,Operation.next,regularNext,State.assign,good,Naming.push,two_mul]
      obtain ⟨t,e,b⟩ := step
      exact ⟨t,_,evalLine_sound _ _ _ _ e,le_rfl,b⟩)
  let t := v.assign 131 (v.reg 128)
  have finish : Executes n m (chain pushEnd) v t 3 := evalLine_sound _ _ _ _ rfl
  obtain ⟨q,pr,cost⟩ := splitChain pushStart start
  rw [pushCode]
  exact ⟨t,_,pr.continue _ (.seq loop finish),by omega,by simpa [t,State.assign,P] using finalVal⟩

private lemma point_action (n a j : ℕ) (m : ℤ→ℤ) (s : State) (v : s.reg 156=(a:ℤ)) (ix : s.reg 157=(j:ℤ)) :
    ∃t k,Executes n m pointAction s t k ∧ k≤70+10*j ∧ t.reg 156=(Naming.push a (j+1):ℤ) := by
  have prepare : ∃t,evalLine n m (chain pointPrep) s=some (t,9) ∧ t.reg 128=(a:ℤ) ∧ t.reg 129=((j+1:ℕ):ℤ) := by
    simp [pointPrep,chain,evalLine,Operation.next,regularNext,State.assign,v,ix]
  obtain ⟨t,e,base,digit⟩ := prepare
  obtain ⟨u,k,run,kt,newVal⟩ := push_value n a (j+1) m t base digit
  have endResult : ∃z,evalLine n m (chain acceptResult) u=some (z,5) ∧ z.reg 156=(Naming.push a (j+1):ℤ) := by
    simp [acceptResult,chain,evalLine,Operation.next,regularNext,State.assign,newVal]
  obtain ⟨z,fin,ans⟩ := endResult
  obtain ⟨q,p,qt⟩ := splitChain pointPrep (evalLine_sound _ _ _ _ e)
  exact ⟨z,_,p.continue _ (.seq run (evalLine_sound _ _ _ _ fin)),by omega,ans⟩

private lemma pair_action (n a j v c table words : ℕ) (m : ℤ→ℤ) (s : State)
    (base : s.reg 156=(a:ℤ)) (ix : s.reg 157=(j:ℤ)) (ptr : s.reg 155=(table:ℤ)) (wp : s.reg 76=(words:ℤ))
    (selected : s.heap (table+j)=(v:ℤ)) (word : s.heap (words+v)=(c:ℤ)) :
    ∃t k,Executes n m pairAction s t k ∧ k≤240+10*(j+c) ∧ t.reg 156=(Naming.push (Naming.push a j) c:ℤ) := by
  have prepare : ∃t,evalLine n m (chain pairPrep) s=some (t,5) ∧ t.reg 128=(a:ℤ) ∧ t.reg 129=(j:ℤ) := by
    simp [pairPrep,chain,evalLine,Operation.next,regularNext,State.assign,base,ix]
  obtain ⟨t,e,val,dig⟩ := prepare
  have beginRun := evalLine_sound _ _ _ _ e
  obtain ⟨u,k,first,kt,output⟩ := push_value n a j m t val dig
  have fr (r : ℕ) (p : writesReg r src_code_name_push=false) (q : writesReg r (chain pairPrep)=false) :=
    (first.preserves r p).trans (beginRun.preserves _ q)
  have heap := ((intact beginRun (by decide)).comp (intact first (by decide))).heap
  have secondPrepOK : ∃y,evalLine n m (chain secondPrep) u=some (y,139) ∧
      y.reg 128=(Naming.push a j:ℤ) ∧ y.reg 129=(c:ℤ) := by
    have f155 := (fr 155 (by decide) (by decide)).trans ptr
    have f76 := (fr 76 (by decide) (by decide)).trans wp
    have f157 := (fr 157 (by decide) (by decide)).trans ix
    simp [secondPrep,chain,evalLine,Operation.next,regularNext,State.assign,output,f155,f76,f157,heap,
      show 0 ≤ (table:ℤ)+j by omega,show 0 ≤ (words:ℤ)+v by omega,
      show ((table:ℤ)+j).toNat=table+j by omega,show ((words:ℤ)+v).toNat=words+v by omega,selected,word]
  obtain ⟨y,p,b,d⟩ := secondPrepOK
  obtain ⟨u',l,second,lt,output'⟩ := push_value n (Naming.push a j) c m y b d
  have endResult : ∃z,evalLine n m (chain pairEnd) u'=some (z,5) ∧ z.reg 156=(Naming.push (Naming.push a j) c:ℤ) := by
    simp [pairEnd,chain,evalLine,Operation.next,regularNext,State.assign,output']
  obtain ⟨z,fin,ans⟩ := endResult
  obtain ⟨q,pr,qt⟩ := splitChain pairPrep beginRun
  obtain ⟨q',pr',qt'⟩ := splitChain secondPrep (evalLine_sound _ _ _ _ p)
  exact ⟨z,_,pr.continue _ (.seq first (pr'.continue _ (.seq second (evalLine_sound _ _ _ _ fin)))),by omega,ans⟩

private lemma fetch_word {n : ℕ} {m : ℤ→ℤ} (d ptr ix b j : ℕ) (s : State)
    (whereAt : s.reg ptr=(b:ℤ)) (idx : s.reg ix=(j:ℤ)) :
    Executes n m (.op (.fetch d ptr ix)) s (s.assign d (s.heap (b+j))) 64 := by
  apply Executes.op
  simp [Operation.next,whereAt,idx,show 0≤(b:ℤ)+j by omega,show ((b:ℤ)+j).toNat=b+j by omega]
private def pointDigits (a : ℕ→Bool) (j : ℕ) := ((List.range j).filter a).map Nat.succ
private def pairDigits (a : ℕ→Bool) (v : ℕ→ℕ) (j : ℕ) := Naming.pairs (((List.range j).filter a).map fun b => (b,v b))
private lemma next_points (a : ℕ→Bool) (j : ℕ) :
    pointDigits a (j+1)=pointDigits a j++(if a j then [j+1] else []) := by
  cases e : a j <;> simp [pointDigits,List.range_succ,List.filter_append,e]
private lemma next_pairs (a : ℕ→Bool) (v : ℕ→ℕ) (j : ℕ) :
    pairDigits a v (j+1)=pairDigits a v j++(if a j then [j,v j] else []) := by
  cases e : a j <;> simp [pairDigits,Naming.pairs,List.range_succ,List.filter_append,e]

private def markBody (d ptr : ℕ) (action : Program) := chain [.op (.fetch d ptr 157),.cond 6 d action .skip]
private def markLoop (last d ptr : ℕ) (action : Program) := forCount 157 last 64 (markBody d ptr action)
private lemma run_marks {n : ℕ} {m : ℤ→ℤ} (last d ptr b cap : ℕ) (action : Program) (s : State)
    (mark : ℕ→Bool) (result : ℕ→ℕ)
    (idxNe : 157≠last) (accNe : 156≠last) (readOne : 6≠d) (readAcc : 156≠d) (readIdx : 157≠d)
    (ixSafe : writesReg 157 (markBody d ptr action)=false) (lastSafe : writesReg last (markBody d ptr action)=false)
    (oneSafe : writesReg 6 (markLoop last d ptr action)=false) (ptrSafe : writesReg ptr (markLoop last d ptr action)=false)
    (readOnly : reads action=true)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (ptrAt : s.reg ptr=(b:ℤ)) (start : s.reg 156=(result 0:ℤ))
    (bits : ∀ j < n,1 ≤ s.heap (b+j) ↔ mark j=true)
    (skipValue : ∀ j < n,mark j≠true → result (j+1)=result j)
    (step : ∀ j < n,mark j=true → ∀ y : State,y.reg 156=(result j:ℤ) → y.reg 157=(j:ℤ) → y.heap=s.heap →
      (∀r,writesReg r (markLoop last d ptr action)=false → r≠d → y.reg r=s.reg r) →
      ∃t k,Executes n m action y t k ∧ k≤cap ∧ t.reg 156=(result (j+1):ℤ)) :
    ∃t k,Executes n m (markLoop last d ptr action) s t k ∧ k≤9+n*(cap+75) ∧ t.reg 156=(result n:ℤ) := by
  let P := fun j (t : State) => t.reg 156=(result j:ℤ) ∧ t.heap=s.heap
  obtain ⟨t,k,run,kt,ans⟩ := GeometryTables.counted (n:=n) (m:=m) 157 last 64 n (cap+70) (markBody d ptr action) s P
    idxNe (by decide) ixSafe lastSafe size ⟨start,rfl⟩ (by
      intro j z r x eq p
      rcases eq with rfl|rfl <;> exact ⟨by simpa [State.assign,accNe] using p.1,p.2⟩) (by
      intro j hj z pr fr idx
      let y := z.assign d (z.heap (b+j))
      have rd : Executes n m (.op (.fetch d ptr 157)) z y 64 := fetch_word d ptr 157 b j z ((fr _ ptrSafe).trans ptrAt) idx
      have keep (r : ℕ) (h : writesReg r (markLoop last d ptr action)=false) (off : r≠d) : y.reg r=s.reg r := by
        simpa [y,State.assign,off] using fr r h
      have accY : y.reg 156=(result j:ℤ) := by simpa [y,State.assign,readAcc] using pr.1
      have idxY : y.reg 157=(j:ℤ) := by simpa [y,State.assign,readIdx] using idx
      have test : y.reg 6 ≤ y.reg d ↔ mark j=true := by
        rw [(keep 6 oneSafe readOne).trans one,show y.reg d=z.heap (b+j) by simp [y,State.assign],pr.2]
        exact bits j hj
      by_cases yes : mark j=true
      · obtain ⟨v,k,act,kt,rv⟩ := step j hj yes y accY idxY pr.2 keep
        exact ⟨v,_,.seq rd (.seq (.yes (test.mpr yes) act) (.skip _)),by omega,rv,(intact act readOnly).heap.trans pr.2⟩
      · exact ⟨y,_,.seq rd (.seq (.no (mt test.mp yes) (.skip _)) (.skip _)),by omega,
          by simpa only [skipValue j hj yes] using accY,pr.2⟩)
  exact ⟨t,k,run,by simpa only [Nat.add_assoc] using kt,ans.1⟩

private lemma mark_points (n b : ℕ) (m : ℤ→ℤ) (s : State) (A : ℕ→Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (ptr : s.reg 153=(b:ℤ)) (start : s.reg 156=0)
    (bits : ∀j < n, 1 ≤ s.heap (b+j) ↔ A j=true) :
    ∃t k,Executes n m pointLoop s t k ∧ k≤9+n*(70+10*n+75) ∧ t.reg 156=(acc (pointDigits A n):ℤ) := by
  let f := fun j => acc (pointDigits A j)
  apply run_marks 376 377 153 b (70+10*n) pointAction s A f (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) one size ptr start bits
  · intro j _ no;simp [f,next_points,no]
  · intro j hj on y base ix _ _
    obtain ⟨t,k,e,kt,bv⟩ := point_action n (f j) j m y base ix
    exact ⟨t,k,e,by omega,by simpa [f,next_points,on,snoc] using bv⟩

private lemma mark_pairs (n b table words M : ℕ) (m : ℤ→ℤ) (s : State) (A : ℕ→Bool) (sl val : ℕ→ℕ) (digits : List ℕ)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (ptr : s.reg 154=(b:ℤ)) (tableAt : s.reg 155=(table:ℤ))
    (wordAt : s.reg 76=(words:ℤ)) (start : s.reg 156=(acc digits:ℤ))
    (bits : ∀j < n,1 ≤ s.heap (b+j) ↔ A j=true)
    (slots : ∀j < n,A j=true → s.heap (table+j)=(sl j:ℤ))
    (labels : ∀j < n,A j=true → s.heap (words+sl j)=(val j:ℤ))
    (bound : ∀j < n,A j=true → val j≤M) :
    ∃t k,Executes n m pairLoop s t k ∧ k≤9+n*(240+10*(n+M)+75) ∧
      t.reg 156=(acc (digits++pairDigits A val n):ℤ) := by
  let f := fun j => acc (digits++pairDigits A val j)
  apply run_marks 389 390 154 b (240+10*(n+M)) pairAction s A f (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) one size ptr
    (by simpa [f,pairDigits,Naming.pairs] using start) bits
  · intro j _ no;simp [f,next_pairs,no]
  · intro j hj on y base ix heap reg
    obtain ⟨t,k,e,kt,bv⟩ := pair_action n (f j) j (sl j) (val j) table words m y base ix
      ((reg 155 (by decide) (by decide)).trans tableAt) ((reg 76 (by decide) (by decide)).trans wordAt)
      (by rw [heap];exact slots j hj on) (by rw [heap];exact labels j hj on)
    have bb := bound j hj on
    have step : f (j+1)=Naming.push (Naming.push (f j) j) (val j) := by
      simp only [f,next_pairs,on,if_true]
      rw [show digits++(pairDigits A val j++[j,val j])=((digits++pairDigits A val j)++[j])++[val j] by simp]
      rw [snoc,snoc]
    exact ⟨t,k,e,by omega,by simpa only [step] using bv⟩

private lemma name_program
    (n points boundary table words maxWord : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (isPoint isBoundary : ℕ → Bool) (slot label : ℕ → ℕ)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ))
    (pointsAt : s.reg 153=(points:ℤ)) (boundaryAt : s.reg 154=(boundary:ℤ))
    (valuesAt : s.reg 155=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ))
    (pointBits : ∀ j < n, 1 ≤ s.heap (points+j) ↔ isPoint j=true)
    (boundaryBits : ∀ j < n, 1 ≤ s.heap (boundary+j) ↔ isBoundary j=true)
    (slots : ∀ j < n,isBoundary j=true → s.heap (table+j)=(slot j:ℤ))
    (labels : ∀ j < n,isBoundary j=true → s.heap (words+slot j)=(label j:ℤ))
    (bounded : ∀ j < n,isBoundary j=true → label j ≤ maxWord) :
    let ps := (List.range n).filter isPoint
    let bs := ((List.range n).filter isBoundary).map (fun j => (j,label j))
    ∃ t k, Logical.Executes n m Logical.src_name_key s t k ∧
      k ≤ 600*(n+1)*(n+maxWord+1) ∧ t.reg 158=(Naming.name (ps,bs):ℤ) ∧
      t.heap=s.heap ∧ t.reg 8=s.reg 8 ∧ t.output=s.output ∧ t.closed=s.closed
    := by
  have begin : ∃u,evalLine n m (chain startName) s=some (u,5) ∧ u.reg 156=0 := by
    simp [startName,chain,evalLine,Operation.next,regularNext,State.assign]
  obtain ⟨u,start,uz⟩ := begin
  have init := evalLine_sound _ _ _ _ start
  have fresh := intact init (by decide)
  obtain ⟨y,k,pointsRun,kt,pointName⟩ := mark_points n points m u isPoint
    ((init.preserves _ (by decide)).trans one) ((init.preserves _ (by decide)).trans size)
    ((init.preserves _ (by decide)).trans pointsAt) uz (by intro j hj;rw [fresh.heap];exact pointBits _ hj)
  let pd := pointDigits isPoint n
  have zeroReady : ∃v,evalLine n m (chain zeroPrep) y=some (v,7) ∧ v.reg 128=(acc pd:ℤ) ∧ v.reg 129=0 := by
    simp [zeroPrep,chain,evalLine,Operation.next,regularNext,State.assign,pd,pointName]
  obtain ⟨v,prep,zeroBase,zeroValue⟩ := zeroReady
  have zeroRun := evalLine_sound _ _ _ _ prep
  obtain ⟨v',l,delimiter,lt,delimVal⟩ := push_value n (acc pd) 0 m v zeroBase zeroValue
  have install : ∃w,evalLine n m (chain zeroEnd) v'=some (w,5) ∧ w.reg 156=(acc (pd++[0]):ℤ) := by
    simp [zeroEnd,chain,evalLine,Operation.next,regularNext,State.assign,delimVal,snoc]
  obtain ⟨w,copy,beginPairs⟩ := install
  have save := evalLine_sound _ _ _ _ copy
  have frames := (((fresh.comp (intact pointsRun (by decide))).comp (intact zeroRun (by decide))).comp
    (intact delimiter (by decide))).comp (intact save (by decide))
  have regs (r : ℕ) (a : writesReg r (chain startName)=false) (b : writesReg r pointLoop=false)
      (c : writesReg r (chain zeroPrep)=false) (d : writesReg r src_code_name_push=false)
      (e : writesReg r (chain zeroEnd)=false) : w.reg r=s.reg r :=
    (save.preserves r e).trans ((delimiter.preserves r d).trans ((zeroRun.preserves r c).trans
      ((pointsRun.preserves r b).trans (init.preserves r a))))
  obtain ⟨t,q,pairsRun,qt,pairName⟩ := mark_pairs n boundary table words maxWord m w isBoundary slot label (pd++[0])
    ((regs 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans one)
    ((regs 64 (by decide) (by decide) (by decide) (by decide) (by decide)).trans size)
    ((regs 154 (by decide) (by decide) (by decide) (by decide) (by decide)).trans boundaryAt)
    ((regs 155 (by decide) (by decide) (by decide) (by decide) (by decide)).trans valuesAt)
    ((regs 76 (by decide) (by decide) (by decide) (by decide) (by decide)).trans wordsAt) beginPairs
    (by intro j hj;rw [frames.heap];exact boundaryBits j hj)
    (by intro j hj ok;rw [frames.heap];exact slots j hj ok)
    (by intro j hj ok;rw [frames.heap];exact labels j hj ok) bounded
  let z := t.assign 158 (t.reg 156)
  have ret : Executes n m (chain endName) t z 3 := evalLine_sound _ _ _ _ rfl
  obtain ⟨a,p,pt⟩ := splitChain startName init
  obtain ⟨b,q',qt'⟩ := splitChain zeroPrep zeroRun
  obtain ⟨c,w',wt⟩ := splitChain zeroEnd save
  have run : Executes n m src_name_key s z (a+(1+k+(b+(1+l+(c+(1+q+3)))))) := by
    rw [keyCode]
    exact p.continue _ (.seq pointsRun (q'.continue _ (.seq delimiter (w'.continue _ (.seq pairsRun ret)))))
  have same := intact run (by decide)
  exact ⟨z,_,run,by ring_nf at kt lt qt ⊢ <;> omega,by simpa [z,State.assign,acc,pd,pointDigits,pairDigits,
    Naming.name,Naming.digits] using pairName,same.heap,run.preserves _ (by decide),same.output,same.closed⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorKeys

theorem solution
    (n points boundary table words maxWord : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (isPoint isBoundary : ℕ → Bool) (slot label : ℕ → ℕ)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ))
    (pointsAt : s.reg 153=(points:ℤ)) (boundaryAt : s.reg 154=(boundary:ℤ))
    (valuesAt : s.reg 155=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ))
    (pointBits : ∀ j < n, 1 ≤ s.heap (points+j) ↔ isPoint j=true)
    (boundaryBits : ∀ j < n, 1 ≤ s.heap (boundary+j) ↔ isBoundary j=true)
    (slots : ∀ j < n,isBoundary j=true → s.heap (table+j)=(slot j:ℤ))
    (labels : ∀ j < n,isBoundary j=true → s.heap (words+slot j)=(label j:ℤ))
    (bounded : ∀ j < n,isBoundary j=true → label j ≤ maxWord) :
    let ps := (List.range n).filter isPoint
    let bs := ((List.range n).filter isBoundary).map (fun j => (j,label j))
    ∃ t k, Logical.Executes n m Logical.src_name_key s t k ∧
      k ≤ 600*(n+1)*(n+maxWord+1) ∧ t.reg 158=(Naming.name (ps,bs):ℤ) ∧
      t.heap=s.heap ∧ t.reg 8=s.reg 8 ∧ t.output=s.output ∧ t.closed=s.closed
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorKeys.name_program n points boundary table words maxWord m s isPoint isBoundary slot label one size pointsAt boundaryAt valuesAt wordsAt pointBits boundaryBits slots labels bounded
