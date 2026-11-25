-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.ComponentScan.connected_component_bitmap
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T12:27:24.002587+00:00
-- url     : https://prove2.me/submissions/883e15ab-10e0-4b71-b2d3-068736bc8afe

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Enumeration_component_and_literal_scans
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.ComponentScan
open StableMSR.Recovery.SingleCircuit
private def seedComponent : List Program := [
  .op (.alloc 284 64),
  .op (.regular (.copy 134 284)), .op (.regular (.set 289 1)), .op (.save 134 133 289)
]
private def guardPoint : List Program := [
  .op (.fetch 295 132 136),
  .op (.regular (.copy 294 295)),
  .cond 6 294 (chain [.op (.fetch 299 134 136),
          .cond 6 299 (.op (.regular (.set 298 0))) (.op (.regular (.set 298 1))),
          .op (.regular (.copy 294 298))]) (.skip)
]
private def scanOne : List Program := [
  .op (.fetch 305 134 137),
  .op (.regular (.copy 304 305)),
  .cond 6 304 (chain [.op (.multiply 311 137 64),
                .op (.regular (.add 310 311 136)),
                .op (.fetch 308 75 310),
                .op (.regular (.copy 304 308))]) (.skip),
  .cond 6 304 (chain [.op (.regular (.set 318 1)),
                .op (.save 134 136 318)]) (.skip)
]
private def returnComponent : List Program := [
  .op (.regular (.copy 138 134))
]
private def inner := forCount 137 303 64 (chain scanOne)
private def vertex := chain (guardPoint++[.cond 6 294 inner .skip])
private def pass := forCount 136 293 64 vertex
private def passes := forCount 135 291 64 pass
private lemma componentCode : src_component=chain (seedComponent++[passes]++returnComponent) := rfl
private lemma scan_step (n q p base edge : ℕ) (m : ℤ→ℤ) (s : State) (inPart linked : Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (index : s.reg 137=(q:ℤ)) (target : s.reg 136=(p:ℤ))
    (result : s.reg 134=(base:ℤ)) (matrixAt : s.reg 75=(edge:ℤ))
    (pointVal : s.heap (base+q)=if inPart then 1 else 0)
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
        matrixAt,posE,addrE,pos,addr,pointVal,edgeVal] at pointVal edgeVal ⊢ <;> omega
  obtain ⟨t,k,e,b,fr⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,b,fr⟩

private lemma can_scan (n p active points : ℕ) (m : ℤ→ℤ) (s : State) (enabled member : Bool)
    (one : s.reg 6=1) (atP : s.reg 136=(p:ℤ)) (activeAt : s.reg 132=(active:ℤ)) (pointsAt : s.reg 134=(points:ℤ))
    (activeBit : s.heap (active+p)=if enabled then 1 else 0) (partBit : s.heap (points+p)=if member then 1 else 0) :
    ∃t k,Executes n m (chain guardPoint) s t k ∧ k≤150 ∧ t.reg 294=(if enabled=true ∧ member=false then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have pos (x y : ℕ) : 0≤(x:ℤ)+y := by omega
  have addr (x y : ℕ) : ((x:ℤ)+y).toNat=x+y := by omega
  have ev : ∃t k,evalLine n m (chain guardPoint) s=some (t,k) ∧ k≤150 ∧
      t.reg 294=(if enabled=true ∧ member=false then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    cases enabled <;> cases member <;> simp [guardPoint,chain,evalLine,Operation.next,regularNext,State.assign,one,atP,
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
private lemma scan_component (n p base edge : ℕ) (m : ℤ→ℤ) (s : State) (part : ℕ→Bool) (adj : ℕ→ℕ→Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (target : s.reg 136=(p:ℤ)) (dest : s.reg 134=(base:ℤ))
    (matrixAt : s.reg 75=(edge:ℤ))
    (edgeBelow : ∀q < n,edge+(q*n+p) < base)
    (partBits : ∀q < n,s.heap (base+q)=if part q then 1 else 0)
    (edges : ∀q < n,s.heap (edge+(q*n+p))=if adj q p then 1 else 0) :
    ∃t k,Executes n m inner s t k ∧ k≤9+n*(325+6*n) ∧
      t.heap (base+p)=(if Found part adj p n then 1 else s.heap (base+p)) ∧
      (∀z,z≠base+p → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed := by
  classical
  let P := fun j (t : State) => t.heap (base+p)=(if Found part adj p j then 1 else s.heap (base+p)) ∧
    (∀z,z≠base+p → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed
  obtain ⟨t,k,run,kt,img⟩ := GeometryTables.counted (n:=n) (m:=m) 137 303 64 n (320+6*n) (chain scanOne) s P
    (by decide) (by decide) (by decide) (by decide) size ⟨by simp [Found],fun _ _=>rfl,rfl,rfl⟩
    (by intro j z r x _ pr;exact pr) (by
      intro q hq z pr fr ix
      obtain ⟨old,kept,out,cl⟩ := pr
      let live := decide (z.heap (base+q)=1)
      have bit : z.heap (base+q) = if live then 1 else 0 := by
        by_cases eq : q=p
        · subst q
          by_cases prior : Found part adj p p
          · simp [live,old,prior]
          · cases h : part p <;> simp [live,old,prior,partBits p hq,h]
        · cases h : part q <;> simp [live,kept _ (by omega : base+q≠base+p),partBits q hq,h]
      have actual : ¬ Found part adj p q → live=part q := by
        intro no
        by_cases eq : q=p
        · subst q;simp [live,old,no,partBits p hq]
        · simp [live,kept _ (by omega : base+q ≠ base+p),partBits q hq]
      obtain ⟨y,l,step,lt,heap,oy,cy⟩ := scan_step n q p base edge m z live (adj q p)
        ((fr 6 (by decide)).trans one) ((fr 64 (by decide)).trans size) ix ((fr 136 (by decide)).trans target)
        ((fr 134 (by decide)).trans dest) ((fr 75 (by decide)).trans matrixAt) bit
        ((kept _ (by have := edgeBelow q hq;omega)).trans (edges q hq))
      refine ⟨y,l,step,lt,?_,?_,oy.trans out,cy.trans cl⟩
      · rw [heap]
        by_cases prior : Found part adj p q
        · rw [if_pos ((found_next ..).mpr (.inl prior))]
          split
          · exact Function.update_self ..
          · exact old.trans (if_pos prior)
        · rw [actual prior]
          by_cases yes : part q=true ∧ adj q p=true
          · rw [if_pos yes,Function.update_self,if_pos ((found_next ..).mpr (.inr yes))]
          · rw [if_neg yes,old,if_neg prior,if_neg (fun e=>((found_next ..).mp e).elim prior yes)]
      · intro j ne;rw [heap];split
        · rw [Function.update_of_ne ne];exact kept j ne
        · exact kept j ne)
  exact ⟨t,k,run,by ring_nf at kt ⊢ <;> omega,img⟩


private noncomputable def mark (d : Instance) (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  if ∃ q ∈ S, d.edge q p=true then insert p S else S

private noncomputable def prefixSet (d : Instance) (allow : ℕ → Bool) (S : Finset ℕ) (i : ℕ) :=
  ((List.range i).filter allow).foldl (mark d) S

private lemma prefix_next (d : Instance) (allow : ℕ → Bool) (S : Finset ℕ) (i : ℕ) :
    prefixSet d allow S (i+1) =
      if allow i then mark d (prefixSet d allow S i) i else prefixSet d allow S i := by
  cases h : allow i <;> simp [prefixSet,List.range_succ,List.filter_append,List.foldl_append,h]

private structure Image (n base : ℕ) (allow : ℕ → Bool) (original t : State) (S : Finset ℕ) : Prop where
  good : ∀ q ∈ S, q<n ∧ allow q=true
  bits : ∀ q<n, t.heap (base+q)=if q∈S then 1 else 0
  outside : ∀ j, j<base ∨ base+n≤j → t.heap j=original.heap j
  output : t.output=original.output
  closed : t.closed=original.closed

private lemma image_assign {n base allow orig t S} (old : Image n base allow orig t S) (r : ℕ) (x : ℤ) :
    Image n base allow orig (t.assign r x) S := ⟨old.good,old.bits,old.outside,old.output,old.closed⟩

private lemma vertex_image (d : Instance) (allow : ℕ→Bool) (p base active edge : ℕ) (m : ℤ→ℤ)
    (orig s : State) (S : Finset ℕ) (hp : p<d.n) (img : Image d.n base allow orig s S)
    (one : s.reg 6=1) (size : s.reg 64=(d.n:ℤ)) (index : s.reg 136=(p:ℤ))
    (dest : s.reg 134=(base:ℤ)) (allowedAt : s.reg 132=(active:ℤ)) (mat : s.reg 75=(edge:ℤ))
    (activeBelow : active+p<base) (activeBit : orig.heap (active+p)=if allow p then 1 else 0)
    (edgeBelow : ∀q<d.n, edge+(q*d.n+p)<base)
    (edges : ∀q<d.n,orig.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0) :
    ∃t k, Executes d.n m vertex s t k ∧ k≤165+d.n*(325+6*d.n) ∧
      Image d.n base allow orig t (if allow p then mark d S p else S) := by
  classical
  let part := fun q => decide (q∈S)
  have bits (q : ℕ) (hq:q<d.n) : s.heap (base+q)=if part q then 1 else 0 := by
    simpa [part] using img.bits q hq
  obtain ⟨z,k,test,kt,flag,heap,out,cl⟩ := can_scan d.n p active base m s (allow p) (part p)
    one index allowedAt dest ((img.outside _ (.inl activeBelow)).trans activeBit) (bits p hp)
  have unit := (test.preserves 6 (by decide)).trans one
  have passesGuard : z.reg 6≤z.reg 294 ↔ allow p=true ∧ p∉S := by
    rw [unit,flag]
    simp only [part,decide_eq_false_iff_not]; split <;> simp_all
  obtain ⟨a,pre,atime⟩ := splitChain guardPoint test
  by_cases eligible : allow p=true ∧ p∉S
  · obtain ⟨t,l,run,lt,res,off,to',tc⟩ := scan_component d.n p base edge m z part d.edge
      unit ((test.preserves _ (by decide)).trans size) ((test.preserves _ (by decide)).trans index)
      ((test.preserves _ (by decide)).trans dest) ((test.preserves _ (by decide)).trans mat) edgeBelow
      (by intro q hq;rw [heap];exact bits q hq)
      (by intro q hq;rw [heap,img.outside _ (.inl (edgeBelow q hq))];exact edges q hq)
    refine ⟨t,_,pre.continue _ (.seq (.yes (passesGuard.mpr eligible) run) (.skip _)),by omega,?_⟩
    rw [if_pos eligible.1]
    have equiv : Found part d.edge p d.n ↔ ∃q∈S,d.edge q p=true := by
      constructor
      · rintro ⟨q,_,member,ad⟩;exact ⟨q,of_decide_eq_true member,ad⟩
      · rintro ⟨q,member,ad⟩;exact ⟨q,(img.good q member).1,decide_eq_true member,ad⟩
    have old : z.heap (base+p)=0 := by rw [heap,img.bits p hp,if_neg eligible.2]
    refine ⟨?_,?_,fun j hj=>(off j (by omega)).trans ((congrFun heap _).trans (img.outside j hj)),
      to'.trans (out.trans img.output),tc.trans (cl.trans img.closed)⟩
    · intro q hq
      by_cases found : ∃q∈S,d.edge q p=true
      · rw [mark,if_pos found,Finset.mem_insert] at hq
        rcases hq with rfl|mem
        · exact ⟨hp,eligible.1⟩
        · exact img.good q mem
      · exact img.good q (by simpa [mark,found] using hq)
    · intro q hq
      by_cases same : q=p
      · subst q
        by_cases yes : ∃q∈S,d.edge q p=true
        · simpa [mark,yes,equiv.mpr yes] using res
        · simpa [mark,yes,mt equiv.mp yes,old,eligible.2] using res
      · rw [off _ (by omega),heap,img.bits q hq]
        by_cases yes : ∃q∈S,d.edge q p=true <;> simp [mark,yes,same]
  · have unchanged : (if allow p then mark d S p else S)=S := by
      by_cases active : allow p=true
      · have inSet : p∈S := by by_contra h;exact eligible ⟨active,h⟩
        rw [if_pos active];simp [mark,Finset.insert_eq_of_mem inSet]
      · rw [if_neg active]
    refine ⟨z,_,pre.continue _ (.seq (.no (mt passesGuard.mp eligible) (.skip _)) (.skip _)),by omega,?_⟩
    rw [unchanged]
    exact ⟨img.good,fun q hq=>(congrFun heap _).trans (img.bits q hq),
      fun j hj=>(congrFun heap _).trans (img.outside j hj),out.trans img.output,cl.trans img.closed⟩

private lemma run_pass (d : Instance) (allow : ℕ→Bool) (base active edge : ℕ) (m : ℤ→ℤ)
    (orig s : State) (S : Finset ℕ) (img : Image d.n base allow orig s S)
    (one : s.reg 6=1) (size : s.reg 64=(d.n:ℤ)) (dest : s.reg 134=(base:ℤ))
    (allowedAt : s.reg 132=(active:ℤ)) (mat : s.reg 75=(edge:ℤ))
    (activeBelow : ∀p<d.n,active+p<base) (activeBit : ∀p<d.n,orig.heap (active+p)=if allow p then 1 else 0)
    (edgeBelow : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<base)
    (edges : ∀q<d.n,∀p<d.n,orig.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0) :
    ∃t k, Executes d.n m pass s t k ∧ k≤9+d.n*(170+d.n*(325+6*d.n)) ∧
      Image d.n base allow orig t (prefixSet d allow S d.n) := by
  let P := fun i t => Image d.n base allow orig t (prefixSet d allow S i)
  obtain ⟨t,k,run,tm,res⟩ := GeometryTables.counted (n:=d.n) (m:=m) 136 293 64 d.n (165+d.n*(325+6*d.n)) vertex s P
    (by decide) (by decide) (by decide) (by decide) size (by simpa [P,prefixSet] using img)
    (fun _ _ r v _ h=>image_assign h r v) (by
      intro p hp z hz fr idx
      obtain ⟨t,k,run,kt,im⟩ := vertex_image d allow p base active edge m orig z _ hp hz
        ((fr 6 (by decide)).trans one) ((fr 64 (by decide)).trans size) idx
        ((fr 134 (by decide)).trans dest) ((fr 132 (by decide)).trans allowedAt) ((fr 75 (by decide)).trans mat)
        (activeBelow p hp) (activeBit p hp) (fun q h=>edgeBelow q h p hp) (fun q h=>edges q h p hp)
      exact ⟨t,k,run,kt,by simpa [P,prefix_next] using im⟩)
  exact ⟨t,k,run,by ring_nf at tm ⊢ <;> omega,res⟩

private noncomputable def after (d : Instance) (allow : ℕ→Bool) (seed i : ℕ) :=
  (List.range i).foldl (fun S _=>prefixSet d allow S d.n) ({seed}:Finset ℕ)

private lemma after_succ (d : Instance) (allow : ℕ→Bool) (seed i : ℕ) :
    after d allow seed (i+1) = prefixSet d allow (after d allow seed i) d.n := by
  simp [after,List.range_succ,List.foldl_append]

private lemma whole_program (d : Instance) (allow : ℕ→Bool) (base active edge seed : ℕ) (m : ℤ→ℤ)
    (s : State) (hs : seed<d.n) (enabled : allow seed=true)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(d.n:ℤ))
    (allocation : s.reg 8=(base:ℤ)) (seedAt : s.reg 133=(seed:ℤ))
    (allowedAt : s.reg 132=(active:ℤ)) (mat : s.reg 75=(edge:ℤ))
    (activeBelow : ∀p<d.n,active+p<base) (activeBit : ∀p<d.n,s.heap (active+p)=if allow p then 1 else 0)
    (edgeBelow : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<base)
    (edges : ∀q<d.n,∀p<d.n,s.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0) :
    ∃t k, Executes d.n m src_component s t k ∧ k≤800*(d.n+1)^4 ∧
      t.reg 138=(base:ℤ) ∧ t.reg 8=((base+d.n:ℕ):ℤ) ∧
      (∀p<d.n,t.heap (base+p)=if p∈TightLanguage.pieceAt d ((List.range d.n).filter allow) seed then 1 else 0) ∧
      (∀j,j<base ∨ base+d.n≤j → t.heap j=s.heap j) ∧ t.output=s.output ∧ t.closed=s.closed := by
  classical
  have addr : ((base:ℤ)+seed).toNat=base+seed := by omega
  have pos : 0≤(base:ℤ)+seed := by omega
  have start : ∃u k,evalLine d.n m (chain seedComponent) s=some (u,k) ∧ k≤150+64*d.n ∧
      u.reg 134=(base:ℤ) ∧ u.reg 8=((base+d.n:ℕ):ℤ) ∧ Image d.n base allow s u {seed} := by
    simp [seedComponent,chain,evalLine,Operation.next,regularNext,State.assign,State.save,State.clear,zero,one,
      size,allocation,seedAt,pos,addr]
    refine ⟨by omega,?_,?_,?_,rfl,rfl⟩
    · simpa using And.intro hs enabled
    · intro q hq
      by_cases eq : q=seed
      · subst q;simp
      · simp [Function.update_of_ne (by omega : base+q≠base+seed),eq,hq]
    · intro j hj
      simp [Function.update_of_ne (by omega : j≠base+seed),show ¬(base≤j ∧ j<base+d.n) by omega]
  obtain ⟨u,k,ev,kt,b,nxt,initial⟩ := start
  have alloc := evalLine_sound _ _ _ _ ev
  let P := fun i t=>Image d.n base allow s t (after d allow seed i)
  obtain ⟨v,l,loop,lt,done⟩ := GeometryTables.counted (n:=d.n) (m:=m) 135 291 64 d.n
    (9+d.n*(170+d.n*(325+6*d.n))) pass u P (by decide) (by decide) (by decide) (by decide)
    ((alloc.preserves 64 (by decide)).trans size) (by simpa [P,after] using initial)
    (fun _ _ r v _ h=>image_assign h r v) (by
      intro i hi z im fr _
      obtain ⟨t,j,run,jt,new⟩ := run_pass d allow base active edge m s z _ im
        ((fr 6 (by decide)).trans ((alloc.preserves 6 (by decide)).trans one))
        ((fr 64 (by decide)).trans ((alloc.preserves 64 (by decide)).trans size)) ((fr 134 (by decide)).trans b)
        ((fr 132 (by decide)).trans ((alloc.preserves 132 (by decide)).trans allowedAt))
        ((fr 75 (by decide)).trans ((alloc.preserves 75 (by decide)).trans mat)) activeBelow activeBit edgeBelow edges
      exact ⟨t,j,run,jt,by simpa [P,after_succ] using new⟩)
  let t := v.assign 138 (v.reg 134)
  have last : Executes d.n m (chain returnComponent) v t 3 := evalLine_sound _ _ _ _ rfl
  obtain ⟨a,p,pt⟩ := splitChain seedComponent alloc
  rw [componentCode]
  refine ⟨t,_,p.continue _ (.seq loop last),by ring_nf at kt lt ⊢ <;> omega,?_,?_,?_,done.outside,done.output,done.closed⟩
  · simpa [t,State.assign] using (loop.preserves 134 (by decide)).trans b
  · exact (last.preserves 8 (by decide)).trans ((loop.preserves 8 (by decide)).trans nxt)
  · let xs := (List.range d.n).filter allow
    have card : xs.toFinset.card≤d.n := by
      exact (List.toFinset_card_le xs).trans (by simpa using List.length_filter_le allow (List.range d.n))
    have seedIn : seed∈xs := by simp [xs,hs,enabled]
    have eq := Enumeration.component_and_literal_scans.1 d xs seed card seedIn (by omega)
    change xs.filter (fun q=>decide (q∈after d allow seed d.n))=TightLanguage.pieceAt d xs seed at eq
    intro q hq
    have mem : q∈after d allow seed d.n → q∈xs := by
      intro h
      obtain ⟨bound,allowed⟩ := done.good q h
      simp [xs,bound,allowed]
    have equiv : q∈TightLanguage.pieceAt d xs seed ↔ q∈after d allow seed d.n := by
      rw [←eq];simp [and_iff_right_of_imp mem]
    change v.heap (base+q) = if q∈TightLanguage.pieceAt d xs seed then 1 else 0
    simpa only [equiv] using done.bits q hq

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.ComponentScan

theorem solution (d : Instance) (allow : ℕ→Bool) (base active edge seed : ℕ) (m : ℤ→ℤ)
    (s : Logical.State) (hs : seed<d.n) (enabled : allow seed=true)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(d.n:ℤ))
    (allocation : s.reg 8=(base:ℤ)) (seedAt : s.reg 133=(seed:ℤ))
    (allowedAt : s.reg 132=(active:ℤ)) (mat : s.reg 75=(edge:ℤ))
    (activeBelow : ∀p<d.n,active+p<base) (activeBit : ∀p<d.n,s.heap (active+p)=if allow p then 1 else 0)
    (edgeBelow : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<base)
    (edges : ∀q<d.n,∀p<d.n,s.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0) :
    ∃t k, Logical.Executes d.n m src_component s t k ∧ k≤800*(d.n+1)^4 ∧
      t.reg 138=(base:ℤ) ∧ t.reg 8=((base+d.n:ℕ):ℤ) ∧
      (∀p<d.n,t.heap (base+p)=if p∈TightLanguage.pieceAt d ((List.range d.n).filter allow) seed then 1 else 0) ∧
      (∀j,j<base ∨ base+d.n≤j → t.heap j=s.heap j) ∧ t.output=s.output ∧ t.closed=s.closed := Scene.ComponentScan.whole_program d allow base active edge seed m s hs enabled one zero size allocation seedAt allowedAt mat activeBelow activeBit edgeBelow edges

#print axioms solution
