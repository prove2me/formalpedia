-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorRows.component_rim_bitmap
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T05:55:09.678125+00:00
-- url     : https://prove2.me/submissions/9c7dde0d-5e46-49b9-b60e-a8379c438f63

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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorRows
private def allocateRim : List Program := [
  .op (.alloc 320 64),
  .op (.regular (.copy 140 320))
]
private def guardRim : List Program := [
  .op (.fetch 325 71 141),
  .op (.regular (.copy 324 325)),
  .cond 6 324 (chain [.op (.fetch 329 139 141),
          .cond 6 329 (.op (.regular (.set 328 0))) (.op (.regular (.set 328 1))),
          .op (.regular (.copy 324 328))]) (.skip)
]
private def scanOne : List Program := [
  .op (.fetch 335 139 142),
  .op (.regular (.copy 334 335)),
  .cond 6 334 (chain [.op (.multiply 341 142 64),
                .op (.regular (.add 340 341 141)),
                .op (.fetch 338 75 340),
                .op (.regular (.copy 334 338))]) (.skip),
  .cond 6 334 (chain [.op (.regular (.set 348 1)),
                .op (.save 140 141 348)]) (.skip)
]
private def returnRim : List Program := [
  .op (.regular (.copy 143 140))
]
private def inner := forCount 142 333 64 (chain scanOne)
private def vertex := chain (guardRim++[.cond 6 324 inner .skip])
private def outer := forCount 141 323 64 vertex
private lemma rimCode : src_rim=chain (allocateRim++[outer]++returnRim) := rfl

private lemma scan_step (n q p base points edge : ℕ) (m : ℤ→ℤ) (s : State) (inPart linked : Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (index : s.reg 142=(q:ℤ)) (target : s.reg 141=(p:ℤ))
    (result : s.reg 140=(base:ℤ)) (input : s.reg 139=(points:ℤ)) (matrixAt : s.reg 75=(edge:ℤ))
    (pointVal : s.heap (points+q)=if inPart then 1 else 0)
    (edgeVal : s.heap (edge+(q*n+p))=if linked then 1 else 0) :
    ∃t k,Executes n m (chain scanOne) s t k ∧ k≤320+6*n ∧
      t.heap=(if inPart=true ∧ linked=true then Function.update s.heap (base+p) 1 else s.heap) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  have pos (x y : ℕ) : 0 ≤ (x:ℤ)+y := by omega
  have addr (x y : ℕ) : ((x:ℤ)+y).toNat=x+y := by omega
  have ed : (edge:ℤ)+((q:ℤ)*n+p)=((edge+(q*n+p):ℕ):ℤ) := by push_cast;rfl
  have posE : 0≤(edge:ℤ)+((q:ℤ)*n+p) := ed.symm ▸ Int.natCast_nonneg _
  have addrE : ((edge:ℤ)+((q:ℤ)*n+p)).toNat=edge+(q*n+p) := by rw [ed];rfl
  have ev : ∃t k,evalLine n m (chain scanOne) s=some (t,k) ∧ k≤320+6*n ∧
      t.heap=(if inPart=true ∧ linked=true then Function.update s.heap (base+p) 1 else s.heap) ∧
      t.output=s.output ∧ t.closed=s.closed := by
    cases inPart <;> cases linked <;>
      simp [scanOne,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,size,index,target,result,
        input,matrixAt,posE,addrE,pos,addr,pointVal,edgeVal] at pointVal edgeVal ⊢ <;> omega
  obtain ⟨t,k,e,b,fr⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,b,fr⟩

private lemma can_scan (n p active points : ℕ) (m : ℤ→ℤ) (s : State) (enabled member : Bool)
    (one : s.reg 6=1) (atP : s.reg 141=(p:ℤ)) (activeAt : s.reg 71=(active:ℤ)) (pointsAt : s.reg 139=(points:ℤ))
    (activeBit : s.heap (active+p)=if enabled then 1 else 0) (partBit : s.heap (points+p)=if member then 1 else 0) :
    ∃t k,Executes n m (chain guardRim) s t k ∧ k≤150 ∧ t.reg 324=(if enabled=true ∧ member=false then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have pos (x y : ℕ) : 0≤(x:ℤ)+y := by omega
  have addr (x y : ℕ) : ((x:ℤ)+y).toNat=x+y := by omega
  have ev : ∃t k,evalLine n m (chain guardRim) s=some (t,k) ∧ k≤150 ∧
      t.reg 324=(if enabled=true ∧ member=false then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    cases enabled <;> cases member <;> simp [guardRim,chain,evalLine,Operation.next,regularNext,State.assign,one,atP,
      activeAt,pointsAt,activeBit,partBit,pos,addr] at activeBit partBit ⊢
  obtain ⟨t,k,e,b,ans⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,b,ans⟩

private def Found (member : ℕ→Bool) (adj : ℕ→ℕ→Bool) (p j : ℕ) :=
  ∃ q < j,member q=true ∧ adj q p=true
private lemma found_next (member : ℕ→Bool) (adj : ℕ→ℕ→Bool) (p j : ℕ) :
    Found member adj p (j+1) ↔ Found member adj p j ∨ (member j=true ∧ adj j p=true) := by
  constructor
  · rintro ⟨q,h,a,b⟩
    by_cases eq : q=j
    · subst q;exact .inr ⟨a,b⟩
    · exact .inl ⟨q,by omega,a,b⟩
  · rintro (⟨q,h,a,b⟩|⟨a,b⟩)
    · exact ⟨q,by omega,a,b⟩
    · exact ⟨j,by omega,a,b⟩
private lemma scan_component (n p base points edge : ℕ) (m : ℤ→ℤ) (s : State) (part : ℕ→Bool) (adj : ℕ→ℕ→Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (target : s.reg 141=(p:ℤ)) (dest : s.reg 140=(base:ℤ))
    (input : s.reg 139=(points:ℤ)) (matrixAt : s.reg 75=(edge:ℤ))
    (partBelow : ∀q < n,points+q < base) (edgeBelow : ∀q < n,edge+(q*n+p) < base)
    (partBits : ∀q < n,s.heap (points+q)=if part q then 1 else 0)
    (edges : ∀q < n,s.heap (edge+(q*n+p))=if adj q p then 1 else 0) :
    ∃t k,Executes n m inner s t k ∧ k≤9+n*(325+6*n) ∧
      t.heap (base+p)=(if Found part adj p n then 1 else s.heap (base+p)) ∧
      (∀z,z≠base+p → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed := by
  classical
  let P := fun j (t : State) => t.heap (base+p)=(if Found part adj p j then 1 else s.heap (base+p)) ∧
    (∀z,z≠base+p → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed
  obtain ⟨t,k,run,kt,img⟩ := GeometryTables.counted (n:=n) (m:=m) 142 333 64 n (320+6*n) (chain scanOne) s P
    (by decide) (by decide) (by decide) (by decide) size ⟨by simp [Found],fun _ _=>rfl,rfl,rfl⟩
    (by intro j z r x _ pr;exact pr) (by
      intro q hq z pr fr ix
      obtain ⟨old,kept,out,cl⟩ := pr
      obtain ⟨y,l,step,lt,heap,oy,cy⟩ := scan_step n q p base points edge m z (part q) (adj q p)
        ((fr 6 (by decide)).trans one) ((fr 64 (by decide)).trans size) ix ((fr 141 (by decide)).trans target)
        ((fr 140 (by decide)).trans dest) ((fr 139 (by decide)).trans input) ((fr 75 (by decide)).trans matrixAt)
        ((kept _ (by have := partBelow q hq;omega)).trans (partBits q hq))
        ((kept _ (by have := edgeBelow q hq;omega)).trans (edges q hq))
      refine ⟨y,l,step,lt,?_,?_,oy.trans out,cy.trans cl⟩
      · rw [heap]
        by_cases yes : part q=true ∧ adj q p=true
        · rw [if_pos yes,Function.update_self,if_pos ((found_next ..).mpr (.inr yes))]
        · rw [if_neg yes,old]
          by_cases prior : Found part adj p q
          · rw [if_pos prior,if_pos ((found_next ..).mpr (.inl prior))]
          · rw [if_neg prior,if_neg (fun e => ((found_next ..).mp e).elim prior yes)]
      · intro j ne;rw [heap];split
        · rw [Function.update_of_ne ne];exact kept j ne
        · exact kept j ne)
  exact ⟨t,k,run,by ring_nf at kt ⊢ <;> omega,img⟩

private def isRim (active part : ℕ→Bool) (adj : ℕ→ℕ→Bool) (p n : ℕ) :=
  active p=true ∧ part p=false ∧ Found part adj p n
private lemma run_vertex (n p base active points edge : ℕ) (m : ℤ→ℤ) (s : State)
    (enable part : ℕ→Bool) (adj : ℕ→ℕ→Bool) (hp : p < n)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (target : s.reg 141=(p:ℤ)) (dest : s.reg 140=(base:ℤ))
    (activeAt : s.reg 71=(active:ℤ)) (input : s.reg 139=(points:ℤ)) (matrixAt : s.reg 75=(edge:ℤ))
    (partBelow : ∀q < n,points+q < base) (edgeBelow : ∀q < n,edge+(q*n+p) < base)
    (activeBit : s.heap (active+p)=if enable p then 1 else 0)
    (partBits : ∀q < n,s.heap (points+q)=if part q then 1 else 0)
    (edges : ∀q < n,s.heap (edge+(q*n+p))=if adj q p then 1 else 0) (blank : s.heap (base+p)=0) :
    ∃t k,Executes n m vertex s t k ∧ k≤165+n*(325+6*n) ∧
      t.heap (base+p)=(if isRim enable part adj p n then 1 else 0) ∧
      (∀z,z≠base+p → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed := by
  classical
  obtain ⟨z,k,test,kt,bit,heap,out,cl⟩ := can_scan n p active points m s (enable p) (part p)
    one target activeAt input activeBit (partBits p hp)
  have unit := (test.preserves 6 (by decide)).trans one
  have passes : z.reg 6 ≤ z.reg 324 ↔ enable p=true ∧ part p=false := by
    rw [unit,bit];by_cases yes : enable p=true ∧ part p=false <;> simp [yes]
  obtain ⟨q,pr,cost⟩ := splitChain guardRim test
  by_cases eligible : enable p=true ∧ part p=false
  · obtain ⟨t,l,run,lt,result,kept,ot,ct⟩ := scan_component n p base points edge m z part adj unit
      ((test.preserves _ (by decide)).trans size) ((test.preserves _ (by decide)).trans target)
      ((test.preserves _ (by decide)).trans dest) ((test.preserves _ (by decide)).trans input)
      ((test.preserves _ (by decide)).trans matrixAt) partBelow edgeBelow
      (by intro j hj;rw [heap];exact partBits j hj) (by intro j hj;rw [heap];exact edges j hj)
    refine ⟨t,_,pr.continue _ (.seq (.yes (passes.mpr eligible) run) (.skip _)),by omega,?_,
      fun j ne=> (kept j ne).trans (congrFun heap j),ot.trans out,ct.trans cl⟩
    by_cases yes : Found part adj p n
    · exact (result.trans (if_pos yes)).trans (if_pos ⟨eligible.1,eligible.2,yes⟩).symm
    · exact ((result.trans (if_neg yes)).trans ((congrFun heap _).trans blank)).trans (if_neg (fun e => yes e.2.2)).symm
  · exact ⟨z,_,pr.continue _ (.seq (.no (mt passes.mp eligible) (.skip _)) (.skip _)),by omega,
      ((congrFun heap _).trans blank).trans (if_neg (fun e => eligible ⟨e.1,e.2.1⟩)).symm,fun j _=>congrFun heap j,out,cl⟩

private lemma rim_program
    (n cursor active points edge : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (enabled member : ℕ → Bool) (adj : ℕ → ℕ → Bool)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(n:ℤ)) (allocation : s.reg 8=(cursor:ℤ))
    (activeAt : s.reg 71=(active:ℤ)) (pointsAt : s.reg 139=(points:ℤ)) (edgeAt : s.reg 75=(edge:ℤ))
    (vertices : ∀ p < n,s.heap (active+p)=if enabled p then 1 else 0)
    (component : ∀ p < n,s.heap (points+p)=if member p then 1 else 0)
    (graph : ∀ q < n,∀ p < n,s.heap (edge+(q*n+p))=if adj q p then 1 else 0)
    (below : ∀ p < n,active+p < cursor ∧ points+p < cursor)
    (graphBelow : ∀ q < n,∀ p < n,edge+(q*n+p) < cursor) :
    ∃ t k, Logical.Executes n m Logical.src_rim s t k ∧ k ≤ 700*(n+1)^3 ∧
      t.reg 143=(cursor:ℤ) ∧ t.reg 8=((cursor+n:ℕ):ℤ) ∧
      (∀ p < n,t.heap (cursor+p)=
        if enabled p=true ∧ member p=false ∧ ∃ q < n,member q=true ∧ adj q p=true then 1 else 0) ∧
      (∀ z,z < cursor ∨ cursor+n ≤ z → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed
    := by
  classical
  have start : ∃u k,evalLine n m (chain allocateRim) s=some (u,k) ∧ k≤72+64*n ∧ u.reg 140=(cursor:ℤ) ∧
      u.reg 8=((cursor+n:ℕ):ℤ) ∧ (∀p < n,u.heap (cursor+p)=0) ∧
      (∀j,j < cursor ∨ cursor+n ≤ j → u.heap j=s.heap j) ∧ u.output=s.output ∧ u.closed=s.closed := by
    simp [allocateRim,chain,evalLine,Operation.next,regularNext,State.clear,State.assign,one,zero,size,allocation,
      Nat.cast_add,Nat.mul_add,Nat.add_mul] <;> (repeat' apply And.intro) <;> intros <;> omega
  obtain ⟨u,k,e,kt,base,next,empty,frame,uo,uc⟩ := start
  have alloc := evalLine_sound _ _ _ _ e
  let P := fun i (w : State) => (∀p < n,w.heap (cursor+p)=(if p < i ∧ isRim enabled member adj p n then 1 else 0)) ∧
    (∀j,j < cursor ∨ cursor+n ≤ j → w.heap j=s.heap j) ∧ w.output=s.output ∧ w.closed=s.closed
  have init : P 0 u := ⟨by intro p hp;simpa using empty p hp,frame,uo,uc⟩
  obtain ⟨v,l,loop,lt,done⟩ := GeometryTables.counted (n:=n) (m:=m) 141 323 64 n (165+n*(325+6*n)) vertex u P
    (by decide) (by decide) (by decide) (by decide) ((alloc.preserves _ (by decide)).trans size)
    init (by intro j z r x _ pr;exact pr) (by
      intro p hp z pr fr idx
      obtain ⟨cells,old,zo,zc⟩ := pr
      have keep (r : ℕ) (h : writesReg r outer=false) (h' : writesReg r (chain allocateRim)=false) :=
        (fr r h).trans (alloc.preserves _ h')
      obtain ⟨t,b,run,bt,res,off,ot,ct⟩ := run_vertex n p cursor active points edge m z enabled member adj hp
        ((keep 6 (by decide) (by decide)).trans one) ((keep 64 (by decide) (by decide)).trans size) idx
        ((fr 140 (by decide)).trans base) ((keep 71 (by decide) (by decide)).trans activeAt)
        ((keep 139 (by decide) (by decide)).trans pointsAt) ((keep 75 (by decide) (by decide)).trans edgeAt)
        (fun q hq => (below q hq).2) (fun q hq => graphBelow q hq p hp)
        ((old _ (.inl (below p hp).1)).trans (vertices p hp))
        (fun q hq => (old _ (.inl (below q hq).2)).trans (component q hq))
        (fun q hq => (old _ (.inl (graphBelow q hq p hp))).trans (graph q hq p hp))
        ((cells p hp).trans (if_neg (fun e => (Nat.lt_irrefl _) e.1)))
      refine ⟨t,b,run,bt,?_,fun j hj => (off j (by omega)).trans (old j hj),ot.trans zo,ct.trans zc⟩
      intro j hj
      by_cases eq : j=p
      · subst j;simpa only [Nat.lt_succ_self,true_and] using res
      · rw [off _ (by omega),cells j hj]
        by_cases earlier : j < p
        · by_cases yes : isRim enabled member adj j n
          · rw [if_pos ⟨earlier,yes⟩,if_pos ⟨by omega,yes⟩]
          · rw [if_neg (fun h=>yes h.2),if_neg (fun h=>yes h.2)]
        · rw [if_neg (fun h=>earlier h.1),if_neg (fun h=>by have := h.1;omega)])
  let t := v.assign 143 (v.reg 140)
  have last : Executes n m (chain returnRim) v t 3 := evalLine_sound _ _ _ _ rfl
  obtain ⟨a,p,pt⟩ := splitChain allocateRim alloc
  rw [rimCode]
  refine ⟨t,_,p.continue _ (.seq loop last),by ring_nf at kt lt ⊢ <;> omega,?_,?_,?_,done.2.1,done.2.2⟩
  · simpa [t,State.assign] using (loop.preserves 140 (by decide)).trans base
  · exact (last.preserves 8 (by decide)).trans ((loop.preserves 8 (by decide)).trans next)
  · intro j hj
    have img := done.1 j hj
    by_cases yes : isRim enabled member adj j n
    · exact (img.trans (if_pos ⟨hj,yes⟩)).trans (if_pos yes).symm
    · exact (img.trans (if_neg (fun e=>yes e.2))).trans (if_neg (fun e => yes e)).symm

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorRows

theorem solution
    (n cursor active points edge : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (enabled member : ℕ → Bool) (adj : ℕ → ℕ → Bool)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(n:ℤ)) (allocation : s.reg 8=(cursor:ℤ))
    (activeAt : s.reg 71=(active:ℤ)) (pointsAt : s.reg 139=(points:ℤ)) (edgeAt : s.reg 75=(edge:ℤ))
    (vertices : ∀ p < n,s.heap (active+p)=if enabled p then 1 else 0)
    (component : ∀ p < n,s.heap (points+p)=if member p then 1 else 0)
    (graph : ∀ q < n,∀ p < n,s.heap (edge+(q*n+p))=if adj q p then 1 else 0)
    (below : ∀ p < n,active+p < cursor ∧ points+p < cursor)
    (graphBelow : ∀ q < n,∀ p < n,edge+(q*n+p) < cursor) :
    ∃ t k, Logical.Executes n m Logical.src_rim s t k ∧ k ≤ 700*(n+1)^3 ∧
      t.reg 143=(cursor:ℤ) ∧ t.reg 8=((cursor+n:ℕ):ℤ) ∧
      (∀ p < n,t.heap (cursor+p)=
        if enabled p=true ∧ member p=false ∧ ∃ q < n,member q=true ∧ adj q p=true then 1 else 0) ∧
      (∀ z,z < cursor ∨ cursor+n ≤ z → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorRows.rim_program n cursor active points edge m s enabled member adj one zero size allocation activeAt pointsAt edgeAt vertices component graph below graphBelow
