-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.bounded_stream_of_initialized_traversal
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:37:51.961278+00:00
-- url     : https://prove2.me/submissions/f1c131cf-4dd0-42b5-815c-023a5e5a1b14

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_initialized_separator_tables
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
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
def zeroed (s t:State) (k:ℕ) :=
    (∀i,t.heap i=if i<k then 0 else s.heap i) ∧ t.output=s.output ∧ t.closed=s.closed
theorem zeroed_init (s:State) : zeroed s s 0:=by simp [zeroed]
theorem zeroed_assign {s t:State} {k:ℕ} (h:zeroed s t k) (d:ℕ) (v:ℤ):zeroed s (t.assign d v) k:=h
theorem zeroed_expand {s t:State} {k:ℕ} (h:zeroed s t k) (l:ℕ):zeroed s (t.clear k l) (k+l):=by
  refine ⟨?_,h.2⟩
  intro i;change (if k ≤ i ∧ i<k+l then 0 else t.heap i)=_
  rw [h.1];split_ifs <;> omega
theorem op_set {N input} (s:State) (d:ℕ) (v:ℤ):Executes N input (.op (.regular (.set d v))) s (s.assign d v) 1:=
  .op rfl
theorem op_copy {N input} (s:State) (d a:ℕ) (v:ℤ) (eq:s.reg a=v):
    Executes N input (.op (.regular (.copy d a))) s (s.assign d v) 1:=by subst v;exact .op rfl
theorem op_add {N input} (s:State) (d a b:ℕ) (A B:ℕ) (ha:s.reg a=(A:ℤ)) (hb:s.reg b=(B:ℤ)):
    Executes N input (.op (.regular (.add d a b))) s (s.assign d ((A+B:ℕ):ℤ)) 1:=by
  apply Executes.op;simp [Operation.next,regularNext,ha,hb]
theorem op_mul {N input} (s:State) (d a b A B:ℕ) (one:s.reg 6=1) (ha:s.reg a=(A:ℤ)) (hb:s.reg b=(B:ℤ)):
    Executes N input (.op (.multiply d a b)) s (s.assign d ((A*B:ℕ):ℤ)) (8+6*B):=by
  apply Executes.op;simp [Operation.next,one,ha,hb]
theorem op_shift {N input} (s:State) (d a k A:ℕ) (ha:s.reg a=(A:ℤ)):
    Executes N input (.op (.shift d a k)) s (s.assign d ((2^k*A:ℕ):ℤ)) (3+2*k):=by
  apply Executes.op;simp [Operation.next,ha]
theorem op_alloc {N input} (s:State) (d l top L:ℕ) (one:s.reg 6=1) (zero:s.reg 7=0)
    (ht:s.reg 8=(top:ℤ)) (hl:s.reg l=(L:ℤ)) :
    Executes N input (.op (.alloc d l)) s (((s.clear top L).assign d (top:ℤ)).assign 8 ((top+L:ℕ):ℤ)) (64*(1+L)):=by
  apply Executes.op;simp [Operation.next,one,zero,ht,hl]

def powerBody:=chain [.op (.multiply 1240 69 64),.op (.regular (.copy 69 1240))]
def powerLoop:=forCount 268 1239 1237 powerBody
theorem run_power {input:ℤ → ℤ} (N n L:ℕ) (s:State) (one:s.reg 6=1) (base:s.reg 64=(n:ℤ))
    (len:s.reg 1237=(L:ℤ)) (v:s.reg 69=1) :
    ∃t k,Executes N input powerLoop s t k ∧ k ≤ 9+L*(17+6*n) ∧ t.reg 69=((n^L:ℕ):ℤ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed ∧
    ∀j,j≠69 → j≠268 → j≠1239 → j≠1240 → t.reg j=s.reg j:=by
  let P:=fun i (u:State)=>u.reg 69=((n^i:ℕ):ℤ) ∧ u.heap=s.heap ∧ u.output=s.output ∧ u.closed=s.closed ∧
    ∀j,j≠69 → j≠268 → j≠1239 → j≠1240 → u.reg j=s.reg j
  have start:P 0 (forSetup 268 1239 1237 s):=by
    refine ⟨by simpa [forSetup,State.assign] using v,rfl,rfl,rfl,?_⟩
    intro j _ a b _;simp [forSetup,State.assign,a,b]
  have step (i:ℕ) (_:i<L) (u:State) (good:P i u) (_:u.reg 268=(i:ℤ)) (_:u.reg 1239=(L:ℤ)-1) :
      ∃t k,Executes N input powerBody u t k ∧ k ≤ 12+6*n ∧ t.reg 268=u.reg 268 ∧ t.reg 1239=u.reg 1239 ∧
        P (i+1) (t.assign 268 (t.reg 268+1)):=by
    obtain ⟨before,uh,uo,uc,frame⟩:=good
    let a:=u.assign 1240 (((n^i)*n:ℕ):ℤ)
    let t:=a.assign 69 (((n^i)*n:ℕ):ℤ)
    have x:Executes N input (.op (.multiply 1240 69 64)) u a (8+6*n):=
      op_mul u 1240 69 64 _ _ ((frame 6 (by decide) (by decide) (by decide) (by decide)).trans one)
        before ((frame 64 (by decide) (by decide) (by decide) (by decide)).trans base)
    have y:Executes N input (.op (.regular (.copy 69 1240))) a t 1:=op_copy _ _ _ _ (by simp [a,State.assign])
    exact ⟨t,_,.seq x (.seq y (.skip _)),by omega,rfl,rfl,by simp [t,a,State.assign,pow_succ],
      uh,uo,uc,by intro j p q r g;simpa [t,a,State.assign,p,q,g] using frame j p q r g⟩
  obtain ⟨t,k,run,tm,h⟩:=source_for (N:=N) (input:=input) 268 1239 1237 L (12+6*n) powerBody P
    (by decide) (by decide) s len start step
  exact ⟨t,k,run,by simpa only [show 12+6*n+5=17+6*n by omega] using tm,h⟩
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

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
/-- The middle segment starts with geometry construction and ends with the
loop that emits requests for the connected components at the empty boundary. -/
def closingList:List Program:=(listOf src_generate).drop 51
def protocol (s:State):Prop:=s.reg 82=(s.output.length:ℤ) ∧ s.closed=false
def opRespects : Operation → Bool
  | .regular (.store _ _)=>false | .output=>true | o=>!(writesOp 82 o)
def respects : Program → Bool
  | .skip=>true | .op o=>opRespects o | .seq p q|.cond _ _ p q=>respects p && respects q
  | .loop _ _ p=>respects p
theorem op_protocol {n input s t k} (o:Operation) (h:protocol s) (ok:opRespects o=true)
    (ex:o.next n input s=some (t,k)):protocol t:=by
  obtain ⟨idx,open'⟩:=h
  cases o with
  | regular o=>
    cases o <;> simp [opRespects,writesOp] at ok <;> simp only [Operation.next,regularNext] at ex <;>
      (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;>
      simp [protocol,State.assign,ok,idx,open']
  | multiply|divide|shift|fetch|save|alloc|output=>
    simp [opRespects,writesOp] at ok
    simp only [Operation.next] at ex
    (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;>
      simp_all [protocol,State.assign,State.clear,State.save]
theorem Executes.protocol {n input p s t k} (ex:Executes n input p s t k) (ok:respects p=true)
    (h:protocol s):protocol t:=by
  induction ex with
  | op step=>exact op_protocol _ h ok step
  | skip|stop=>exact h
  | yes _ _ ih=>exact ih (Bool.and_eq_true_iff.mp ok).1 h
  | no _ _ ih=>exact ih (Bool.and_eq_true_iff.mp ok).2 h
  | seq _ _ ih jh=>exact jh (Bool.and_eq_true_iff.mp ok).2 (ih (Bool.and_eq_true_iff.mp ok).1 h)
  | more _ _ _ ih jh=>exact jh ok (ih ok h)

theorem middle_frame {n input s t k} (ex:Executes n input (chain middleList) s t k) (h:protocol s) :
    protocol t ∧ t.reg 6=s.reg 6 ∧ t.reg 64=s.reg 64:=
  ⟨ex.protocol (by decide) h,ex.preserves 6 (by decide),ex.preserves 64 (by decide)⟩

def finishOps:List Program:=[.op (.regular (.set 1320 4)),.op (.regular (.set 1321 0)),
  .op (.regular (.set 1322 0)),.op (.regular (.copy 218 1320)),.op (.regular (.copy 219 1321)),
  .op (.regular (.copy 220 1322)),.op .output,.op (.regular (.copy 1319 222)),
  .op (.regular (.set 1325 0)),.op (.regular (.set 1326 79)),.op (.regular (.sub 1324 1325 1326)),
  .op (.regular (.store 1324 82))]
theorem finish_stream (n:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (good:protocol s):
    ∃t k,Executes n input (chain closingList) s t k ∧ k ≤ 230+n*(165+6*n) ∧
      t.output=s.output++[.finish] ∧ t.closed=true:=by
  change ∃t k,Executes n input (chain finishOps) s t k ∧ _
  obtain ⟨idx,flag⟩:=good
  have h:∃t k,evalLine n input (chain finishOps) s=some (t,k) ∧ k ≤ 230+n*(165+6*n) ∧
      t.output=s.output++[.finish] ∧ t.closed=true:=by
    have adr:inputCell 0 0= -79:=rfl
    simp [finishOps,chain,evalLine,Operation.next,regularNext,State.assign,record,Instr.tag,Instr.arg,
      State.bitsOK,idx,flag,one,sz,adr] <;> omega
  obtain ⟨t,k,ex,tm,stream,closed⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,stream,closed⟩
theorem opening_correct (n h w:ℕ) (input:ℤ → ℤ) (s:State) (sz:s.reg 0=(n:ℤ)):
    ∃t,Executes n input (opening h w) s t 15 ∧ t.reg 6=1 ∧ t.reg 7=0 ∧ t.reg 8=0 ∧
      t.reg 64=(n:ℤ) ∧ t.reg 65=s.reg 3 ∧ t.reg 66=(h:ℤ) ∧ t.reg 67=(w:ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let t0:=((s.assign 6 1).assign 7 0).assign 8 0
  let t1:=(t0.assign 64 (n:ℤ)).assign 65 (s.reg 3)
  let t:=(t1.assign 66 (h:ℤ)).assign 67 (w:ℤ)
  refine ⟨t,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  apply evalLine_sound
  simp [opening,candidate,listOf,chain,evalLine,Operation.next,regularNext,State.assign,t,t1,t0,sz]
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem startup (n h:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1) (zero:s.reg 7=0)
    (start:s.reg 8=0) (sz:s.reg 64=(n:ℤ)) (budget:s.reg 66=(h:ℤ)) :
    let H:=h+1
    let rows:=n^(2*H)
    let M:=H*rows
    let layout:=offsets n M
    ∃t z,Executes n input arena s t z ∧ z ≤ 4000*(h+2)*(n+1)^3*(M+1) ∧
      t.reg 68=(H:ℤ) ∧ t.reg 69=(rows:ℤ) ∧ t.reg 70=(M:ℤ) ∧ t.reg 82=0 ∧
      t.reg 8=(cursorAt layout 11:ℤ) ∧
      (∀j:Fin 11,t.reg (71+j.val)=(cursorAt layout j.val:ℤ)) ∧
      zeroed s t (cursorAt layout 11) ∧ (∀j<68,j≠8 → t.reg j=s.reg j) := initialized_separator_tables n h input s one zero start sz budget
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open WindowCSP
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Count all size, cut, seed, boundary-radix, pivot and pivot-label trials.
This bound includes boundary tuples eventually rejected by a menu test. -/
theorem all_trials (n H t:ℕ) (hn:2≤n) (hH:1≤H) :
    let M:=H*n^(2*H)
    n*((n+1)^t*(n*(M^t*(n*M))))≤n^(6*(H*(t+1))) :=by
  let M:=H*n^(2*H)
  have nn:1≤n:=by omega
  have PH:H≤n^H:=(Nat.le_of_lt (Nat.lt_two_pow_self (n:=H))).trans (Nat.pow_le_pow_left hn _)
  have m:M≤n^(3*H):=calc
    M ≤ n^H*n^(2*H) := Nat.mul_le_mul_right _ PH
    _ = _ := by rw [←pow_add];congr 1;omega
  have plus:n+1≤n^2:=by nlinarith [Nat.mul_le_mul_right n hn]
  have c:(n+1)^t≤n^(2*t):=by simpa [pow_mul] using Nat.pow_le_pow_left plus t
  have ht:t+1≤H*(t+1):=Nat.le_mul_of_pos_left _ hH
  change n*((n+1)^t*(n*(M^t*(n*M))))≤_
  calc
    _ = n^3*(n+1)^t*M^(t+1) := by rw [pow_succ M];ring
    _ ≤ n^3*n^(2*t)*(n^(3*H))^(t+1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ c) (Nat.pow_le_pow_left m _)
    _ = n^(3+2*t+3*H*(t+1)) := by rw [←pow_mul,←pow_add,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right nn (by nlinarith)

theorem mission_trials (n:ℕ) (e:ℚ) (hn:2≤n) (he:0<e) (hl:e<1) :
    let H:=budget (e:ℝ)+1
    let t:=min (widthBound (e:ℝ)) n
    let M:=H*n^(2*H)
    n*((n+1)^t*(n*(M^t*(n*M))))≤n^(30*parameterEnvelope (e:ℝ)):=by
  let H:=budget (e:ℝ)+1
  let t:=min (widthBound (e:ℝ)) n
  have er:0<(e:ℝ):=by exact_mod_cast he
  have el:(e:ℝ)<1:=by exact_mod_cast hl
  have ow:1≤ownerBound (e:ℝ):=by
    unfold ownerBound
    apply Nat.le_floor
    push_cast
    exact (le_div_iff₀ er).2 (by linarith)
  have h:H≤5*ownerBound (e:ℝ):=by dsimp [H,budget];omega
  have w:t+1≤widthBound (e:ℝ)+1:=Nat.succ_le_succ (Nat.min_le_left ..)
  have hwt:=Nat.mul_le_mul h w
  apply (all_trials n H t hn (by dsimp [H];omega)).trans
  apply Nat.pow_le_pow_right (by omega)
  unfold parameterEnvelope
  nlinarith

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open WindowCSP
theorem overhead_arith (R n h M:ℕ) (rn:0<R) (pn:n ≤ R) (pH:h+1 ≤ R) (pM:M ≤ R):
    30 + 4000*(h+2)*(n+1)^3*(M+1) + (230+n*(165+6*n)) ≤ 400000*R^5:=by
  calc
    _ ≤ 30+4000*(2*R)*(2*R)^3*(2*R)+(230+R*(165+6*R)):=by gcongr <;> omega
    _ ≤ _:=by obtain ⟨q,rfl⟩:=Nat.exists_eq_succ_of_ne_zero rn.ne';simp only [Nat.succ_eq_add_one];ring_nf;omega

theorem startup_overhead (n:ℕ) (e:ℚ) (hn:2 ≤ n) (ep:0<e) (el:e<1):
    let h:=budget (e:ℝ)
    let M:=sizes n h
    30 + 4000*(h+2)*(n+1)^3*(M+1) + (230+n*(165+6*n)) ≤ 400000*n^(150*parameterEnvelope (e:ℝ)):=by
  let h:=budget (e:ℝ)
  let t:=min (widthBound (e:ℝ)) n
  let M:=sizes n h
  let E:=parameterEnvelope (e:ℝ)
  let R:=n^(30*E)
  have nn:0<n:=by omega
  have hm:0<M:=by dsimp [M,sizes];positivity
  have me:h+1 ≤ M:=Nat.le_mul_of_pos_right _ (Nat.pow_pos nn)
  have bound:n*((n+1)^t*(n*(M^t*(n*M)))) ≤ R:=Enumeration.mission_trials n e hn ep el
  have nm:n*M ≤ R:=calc
    _ ≤ M^t*(n*M) :=Nat.le_mul_of_pos_left _ (Nat.pow_pos hm)
    _ ≤ n*(M^t*(n*M)):=Nat.le_mul_of_pos_left _ nn
    _ ≤ (n+1)^t*(n*(M^t*(n*M))):=Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
    _ ≤ n*((n+1)^t*(n*(M^t*(n*M)))):=Nat.le_mul_of_pos_left _ nn
    _ ≤ R:=bound
  have mr:M ≤ R:=(Nat.le_mul_of_pos_left M nn).trans nm
  have nr:n ≤ R:=(Nat.le_mul_of_pos_right n hm).trans nm
  have big:R^5=n^(150*E):=by dsimp only [R];rw [←pow_mul];congr 1;omega
  change _ ≤ 400000*n^(150*E)
  rw [←big]
  exact overhead_arith R n h M (by omega) nr (me.trans mr) mr
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open WindowCSP OracleQueries Compiler SingleCircuit
theorem assemble_middle (n r h w K:ℕ) (m:ℤ → ℤ) (s:State) (xs:List Instr) (sz:s.reg 0=(n:ℤ))
    (slot:s.reg 3=(r:ℤ)) (empty:s.output=[]) (opened:s.closed=false)
    (core:∀u,Prepared n r h w u → ∃v k,Executes n m (chain middleList) u v k ∧ k ≤ K ∧ v.output++[.finish]=xs) :
    ∃t z,Executes n m (candidate h w) s t z ∧
      z ≤ K+(30+4000*(h+2)*(n+1)^3*(sizes n h+1)+(230+n*(165+6*n))) ∧ t.closed=true ∧ t.output=xs:=by
  obtain ⟨u,entry,one,zero,base,size,regR,regH,regW,_,uo,uc⟩:=opening_correct n h w m s sz
  obtain ⟨v,k,init,tm,H,rows,M,ordinal,top,ptrs,clean,low⟩:=startup n h m u one zero base size regH
  have init0:v.output=[]:=clean.2.1.trans (uo.trans empty)
  have initFlag:v.closed=false:=clean.2.2.trans (uc.trans opened)
  have one':v.reg 6=1:=(low 6 (by decide) (by decide)).trans one
  have size':v.reg 64=(n:ℤ):=(low 64 (by decide) (by decide)).trans size
  have ready:Prepared n r h w v:=
    ⟨one',(low 7 (by decide) (by decide)).trans zero,size',(low 65 (by decide) (by decide)).trans (regR.trans slot),
      (low 66 (by decide) (by decide)).trans regH,(low 67 (by decide) (by decide)).trans regW,H,rows,M,
      ordinal,top,ptrs,fun i hi=>by simpa [hi] using clean.1 i,init0,initFlag⟩
  obtain ⟨v',c,run,work,records⟩:=core v ready
  have proto:protocol v:=⟨by rw [init0,ordinal];rfl,initFlag⟩
  obtain ⟨safe,z6,z64⟩:=middle_frame run proto
  obtain ⟨t,f,finish,ft,out,flag⟩:=finish_stream n m v' (z6.trans one') (z64.trans size') safe
  obtain ⟨c',x,xc⟩:=splitChain middleList run
  obtain ⟨k',start,xk⟩:=splitChain ((listOf src_generate).take 45) init
  obtain ⟨boot,front,xb⟩:=splitChain ((listOf (candidate h w)).take 7) entry
  have gen:Executes n m src_generate u t (k'+(c'+f)):=
    start.continue _ (x.continue _ finish)
  have all:Executes n m (candidate h w) s t (boot+(1+(k'+(c'+f))+1)):=
    front.continue _ (.seq gen (.skip _))
  exact ⟨t,_,all,by change k ≤ 4000*(h+2)*(n+1)^3*(sizes n h+1) at tm;omega,flag,out.trans records⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open WindowCSP OracleQueries Compiler SingleCircuit TightLanguage
theorem from_initialized_traversal (correct:MiddleCorrect) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes x.n s.imem (candidate (budget (e:ℝ)) (widthBound (e:ℝ))) (initial (banks s)) t z ∧
    z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧ t.closed=true ∧
    t.output=tape Naming.name (integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)):=by
  obtain ⟨c,D,b,core⟩:=correct
  refine ⟨c+400000,D,b+150,?_⟩
  intro e ep el x s hk kn rd bounded r p rr rp live used
  let h:=budget (e:ℝ)
  let w:=widthBound (e:ℝ)
  let E:=parameterEnvelope (e:ℝ)
  let d:=integerData x.n x.mem s.imem r h
  let K:=c*x.cap^D*x.n^(b*E)
  have slot:∀u,Prepared x.n r h w u → ∃v k,Executes x.n s.imem (chain middleList) u v k ∧
      k ≤ K ∧ v.output++[.finish]=tape Naming.name d w:=by
    intro u ok
    obtain ⟨v,k,run,tm,out⟩:=core e ep el x s hk kn rd bounded r p rr rp live used u ok
    refine ⟨v,k,run,tm,?_⟩
    change v.output=middleRecords d w at out
    rw [out];rfl
  obtain ⟨t,z,ex,tm,closed,out⟩:=assemble_middle x.n r h w K s.imem (initial (banks s)) _
    (rd.1 .points) rr rfl rfl slot
  refine ⟨t,z,ex,?_,closed,out⟩
  have extra:=startup_overhead x.n e (by omega) ep el
  have tn:1 ≤ x.n:=by omega
  have hc:1 ≤ x.cap^D:=Nat.pow_pos (by dsimp [World.cap];omega)
  have raw:x.n^(b*E) ≤ x.n^((b+150)*E):=Nat.pow_le_pow_right tn (Nat.mul_le_mul_right E (by omega))
  have oh:x.n^(150*E) ≤ x.n^((b+150)*E):=Nat.pow_le_pow_right tn (Nat.mul_le_mul_right E (by omega))
  have scale:400000 ≤ 400000*x.cap^D:=by simpa using Nat.mul_le_mul_left 400000 hc
  calc
    z ≤ K+400000*x.n^(150*E):=tm.trans (Nat.add_le_add_left extra K)
    _ ≤ c*x.cap^D*x.n^((b+150)*E)+(400000*x.cap^D)*x.n^((b+150)*E):=
      Nat.add_le_add (Nat.mul_le_mul_left _ raw) (Nat.mul_le_mul scale oh)
    _ = _:=by dsimp only [E];ring
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem solution (traversal:Logical.MiddleCorrect) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Logical.Executes x.n s.imem (Logical.candidate (budget (e:ℝ)) (widthBound (e:ℝ)))
       (Logical.initial (CandidateRAM.banks s)) t z ∧ z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
       t.closed=true ∧ t.output=tape CandidateRAM.Naming.name
         (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)) := Logical.from_initialized_traversal traversal
