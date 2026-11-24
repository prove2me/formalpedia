-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.root_key_without_label_reads
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T16:16:55.437216+00:00
-- url     : https://prove2.me/submissions/342dd541-ef17-4c01-9c4a-fc9e81ad716a

import Definitions.Def_StableMSR_LogicalCandidateProgram
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

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Naming
theorem accumulated (xs:List ℕ) : xs.foldl push 0=code xs.reverse := by
  induction xs using List.reverseRecOn with
  | nil=>rfl
  | append_singleton xs a ih=>simp [List.foldl_append,ih,code]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Naming
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
theorem PrefixRun.append {N input ps qs s u t a b} (h:PrefixRun N input ps s u a) (next:PrefixRun N input qs u t b):
    PrefixRun N input (ps++qs) s t (a+b):=by
  induction h with
  | nil=>simpa using next
  | cons run _ ih=>simpa [Nat.add_assoc] using PrefixRun.cons run (ih next)
theorem op_fetch {n input} (s:State) (d a i base j:ℕ) (ptr:s.reg a=(base:ℤ)) (idx:s.reg i=(j:ℤ)):
    Executes n input (.op (.fetch d a i)) s (s.assign d (s.heap (base+j))) 64:=by
  apply Executes.op
  have pos:0 ≤ (base:ℤ)+j:=by positivity
  have val:((base:ℤ)+j).toNat=base+j:=by omega
  simp [Operation.next,ptr,idx,pos,val]
def doubleKey:=chain [.op (.regular (.add 280 128 128)),.op (.regular (.copy 128 280))]
def keyStart:List Program:=[.op (.shift 275 128 1),.op (.regular (.set 277 1)),.op (.regular (.add 274 275 277)),
  .op (.regular (.copy 128 274))]
theorem run_digit (n a d:ℕ) (input:ℤ → ℤ) (s:State) (acc:s.reg 128=(a:ℤ)) (digit:s.reg 129=(d:ℤ)):
    ∃t k,Executes n input src_code_name_push s t k ∧ k ≤ 30+10*d ∧ t.reg 131=(Naming.push a d:ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have head:∃t k,evalLine n input (chain keyStart) s=some (t,k) ∧ k ≤ 15 ∧
      t.reg 128=(Naming.push a 0:ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    simp [keyStart,chain,evalLine,Operation.next,regularNext,State.assign,Naming.push,acc]
  obtain ⟨u,k,head,ht,val,heap,out,flag⟩:=head
  have run0:=evalLine_sound _ _ _ _ head
  obtain ⟨z,beginning,zt⟩:=splitChain _ run0
  let P:=fun i (v:State)=>v.reg 128=(Naming.push a i:ℤ) ∧ v.heap=s.heap ∧ v.output=s.output ∧ v.closed=s.closed
  have init:P 0 (forSetup 130 279 129 u):=⟨val,heap,out,flag⟩
  have step (i:ℕ) (_:i<d) (v:State) (good:P i v) (_:v.reg 130=(i:ℤ)) (_:v.reg 279=(d:ℤ)-1):
      ∃t k,Executes n input doubleKey v t k ∧ k ≤ 5 ∧ t.reg 130=v.reg 130 ∧ t.reg 279=v.reg 279 ∧
        P (i+1) (t.assign 130 (t.reg 130+1)):=by
    let next:=v.assign 280 (v.reg 128+v.reg 128)
    let t:=next.assign 128 (next.reg 280)
    have r1:Executes n input (.op (.regular (.add 280 128 128))) v next 1:=.op rfl
    have r2:Executes n input (.op (.regular (.copy 128 280))) next t 1:=.op rfl
    obtain ⟨mark,h,o,f⟩:=good
    refine ⟨t,_,.seq r1 (.seq r2 (.skip _)),by decide,rfl,rfl,?_,h,o,f⟩
    change v.reg 128+v.reg 128=_;rw [mark,Naming.push];push_cast;ring
  obtain ⟨v,j,body,tm,last,hv,ov,fv⟩:=source_for (N:=n) (input:=input) 130 279 129 d 5 doubleKey P
    (by decide) (by decide) u ((run0.preserves 129 (by decide)).trans digit) init step
  let t:=v.assign 131 (Naming.push a d:ℤ)
  have ret:Executes n input (.op (.regular (.copy 131 128))) v t 1:=op_copy _ _ _ _ last
  have tail:=Executes.seq body (Executes.seq ret (Executes.skip t))
  exact ⟨t,_,beginning.continue _ tail,by omega,by simp [t,State.assign],hv,ov,fv⟩

def callDigit (src tmp:ℕ):List Program:=[.op (.regular (.copy 128 156)),.op (.regular (.copy 129 src)),
  src_code_name_push,.op (.regular (.copy tmp 131)),.op (.regular (.copy 156 tmp))]
theorem call_digit (n a d src tmp:ℕ) (input:ℤ → ℤ) (s:State) (avoid:src≠128)
    (acc:s.reg 156=(a:ℤ)) (digit:s.reg src=(d:ℤ)):
    ∃t k,PrefixRun n input (callDigit src tmp) s t k ∧ k ≤ 40+10*d ∧ t.reg 156=(Naming.push a d:ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let u:=s.assign 128 (a:ℤ)
  let v:=u.assign 129 (d:ℤ)
  have e1:Executes n input (.op (.regular (.copy 128 156))) s u 1:=op_copy _ _ _ _ acc
  have e2:Executes n input (.op (.regular (.copy 129 src))) u v 1:=op_copy _ _ _ _ (by simpa [u,State.assign,avoid] using digit)
  obtain ⟨w,k,ex,tm,val,heap,out,flag⟩:=run_digit n a d input v (by simp [v,u,State.assign]) (by simp [v,State.assign])
  let mid:=w.assign tmp (Naming.push a d:ℤ)
  let t:=mid.assign 156 (Naming.push a d:ℤ)
  have e3:Executes n input (.op (.regular (.copy tmp 131))) w mid 1:=op_copy _ _ _ _ val
  have e4:Executes n input (.op (.regular (.copy 156 tmp))) mid t 1:=op_copy _ _ _ _ (by simp [mid,State.assign])
  exact ⟨t,_,.cons e1 (.cons e2 (.cons ex (.cons e3 (.cons e4 (.nil _))))),by omega,by simp [t,State.assign],heap,out,flag⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def pointCall := [.op (.regular (.set 384 1)),.op (.regular (.add 382 157 384))] ++ callDigit 382 380
def pointStep := chain [.op (.fetch 377 153 157),.cond 6 377 (chain pointCall) .skip]
def pairCall := callDigit 157 393 ++ [.op (.fetch 400 155 157),.op (.fetch 398 76 400)] ++ callDigit 398 396
def pairStep := chain [.op (.fetch 390 154 157),.cond 6 390 (chain pairCall) .skip]
def labelOf (m:ℕ → ℤ) (values labels i:ℕ):ℕ:=(m (labels+(m (values+i)).toNat)).toNat
structure KeyRegs (n point boundary values labels:ℕ) (s:State) : Prop where
  one:s.reg 6=1
  size:s.reg 64=(n:ℤ)
  pts:s.reg 153=(point:ℤ)
  boundaryPtr:s.reg 154=(boundary:ℤ)
  index:s.reg 155=(values:ℤ)
  label:s.reg 76=(labels:ℤ)
theorem point_step (n p i a:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1) (pts:s.reg 153=(p:ℤ))
    (idx:s.reg 157=(i:ℤ)) (acc:s.reg 156=(a:ℤ)):
    ∃t k,Executes n input pointStep s t k ∧ k ≤ 125+10*i ∧
    t.reg 156=((if 1 ≤ s.heap (p+i) then Naming.push a (i+1) else a:ℕ):ℤ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let u:=s.assign 377 (s.heap (p+i))
  have x:Executes n input (.op (.fetch 377 153 157)) s u 64:=op_fetch s 377 153 157 p i pts idx
  let guard:=Program.cond 6 377 (chain pointCall) .skip
  by_cases hit:1 ≤ s.heap (p+i)
  · let v:=u.assign 384 1
    let w:=v.assign 382 ((i+1:ℕ):ℤ)
    have f:Executes n input (.op (.regular (.set 384 1))) u v 1:=.op rfl
    have g:Executes n input (.op (.regular (.add 382 157 384))) v w 1:=op_add v _ _ _ i 1 idx (by simp [v,State.assign])
    obtain ⟨t,k,call,tm,res,heap,out,flag⟩:=call_digit n a (i+1) 382 380 input w (by decide) acc (by simp [w,State.assign])
    have body:Executes n input (chain pointCall) u t (1+1+(1+1+(k+1))):=.seq f (.seq g call.finish)
    have branch:Executes n input guard u t (1+_):=.yes (by change s.reg 6 ≤ s.heap (p+i);rwa [one]) body
    exact ⟨t,_,.seq x (.seq branch (.skip _)),by omega,by simpa [hit] using res,heap,out,flag⟩
  · have branch:Executes n input guard u u 2:=.no (by change ¬ s.reg 6 ≤ s.heap (p+i);rwa [one]) (.skip _)
    exact ⟨u,_,.seq x (.seq branch (.skip _)),by omega,by simpa [u,State.assign,hit] using acc,rfl,rfl,rfl⟩

theorem pair_step (n point boundary values labels i a L:ℕ) (input:ℤ → ℤ) (s:State)
    (regs:KeyRegs n point boundary values labels s) (idx:s.reg 157=(i:ℤ)) (acc:s.reg 156=(a:ℤ))
    (nonneg:0 ≤ s.heap (values+i)) (leg:0 ≤ s.heap (labels+(s.heap (values+i)).toNat))
    (bounded:labelOf s.heap values labels i ≤ L):
    ∃t k,Executes n input pairStep s t k ∧ k ≤ 290+10*(i+L) ∧
    t.reg 156=((if 1 ≤ s.heap (boundary+i) then Naming.push (Naming.push a i) (labelOf s.heap values labels i) else a:ℕ):ℤ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let u:=s.assign 390 (s.heap (boundary+i))
  have x:Executes n input (.op (.fetch 390 154 157)) s u 64:=op_fetch s _ _ _ boundary i regs.boundaryPtr idx
  let guard:=Program.cond 6 390 (chain pairCall) .skip
  by_cases hit:1 ≤ s.heap (boundary+i)
  · obtain ⟨v,k,first,tm,push,vm,vo,vc⟩:=call_digit n a i 157 393 input u (by decide) acc idx
    have rv:=first.finish
    let j:=(s.heap (values+i)).toNat
    let l:=labelOf s.heap values labels i
    let w:=v.assign 400 (s.heap (values+i))
    let y:=w.assign 398 (s.heap (labels+j))
    have r1:Executes n input (.op (.fetch 400 155 157)) v w 64:=by
      have get:=op_fetch (n:=n) (input:=input) v 400 155 157 values i
        ((rv.preserves 155 (by decide)).trans regs.index) ((rv.preserves 157 (by decide)).trans idx)
      simpa [w,show v.heap=s.heap from vm] using get
    have r2:Executes n input (.op (.fetch 398 76 400)) w y 64:=by
      have pos:w.reg 400=(j:ℤ):=by simp [w,State.assign,j,Int.toNat_of_nonneg nonneg]
      have get:=op_fetch (n:=n) (input:=input) w 398 76 400 labels j
        ((rv.preserves 76 (by decide)).trans regs.label) pos
      simpa [y,show w.heap=s.heap from vm] using get
    have digit:y.reg 398=(l:ℤ):=by simp [y,l,labelOf,j,State.assign,Int.toNat_of_nonneg leg]
    obtain ⟨t,z,second,zt,res,heap,out,cl⟩:=call_digit n (Naming.push a i) l 398 396 input y (by decide) push digit
    have mid:PrefixRun n input [.op (.fetch 400 155 157),.op (.fetch 398 76 400)] v y _:=.cons r1 (.cons r2 (.nil _))
    have body:=((first.append mid).append second).finish
    have branch:Executes n input guard u t (1+_):=.yes (by change s.reg 6 ≤ s.heap (boundary+i);rwa [regs.one]) body
    exact ⟨t,_,.seq x (.seq branch (.skip _)),by change l ≤ L at bounded;omega,by simpa [hit] using res,
      heap.trans vm,out.trans vo,cl.trans vc⟩
  · have branch:Executes n input guard u u 2:=.no (by change ¬ s.reg 6 ≤ s.heap (boundary+i);rwa [regs.one]) (.skip _)
    exact ⟨u,_,.seq x (.seq branch (.skip _)),by omega,by simpa [u,State.assign,hit] using acc,rfl,rfl,rfl⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def keepKey (p:Program):Bool:=[6,64,153,154,155,76].all (fun j=>!(writesReg j p))
theorem KeyRegs.kept {N input p s t z n pts sep vals labels} (r:KeyRegs n pts sep vals labels s)
    (ex:Executes N input p s t z) (ok:keepKey p=true):KeyRegs n pts sep vals labels t:=by
  simp [keepKey] at ok;obtain ⟨a,b,c,d,e,f⟩:=ok
  exact ⟨(ex.preserves _ a).trans r.one,(ex.preserves _ b).trans r.size,(ex.preserves _ c).trans r.pts,
    (ex.preserves _ d).trans r.boundaryPtr,(ex.preserves _ e).trans r.index,(ex.preserves _ f).trans r.label⟩

theorem key_loop (n pts sep vals labels a K last:ℕ) (m:ℤ → ℤ) (body:Program) (digits:ℕ → List ℕ)
    (s:State) (regs:KeyRegs n pts sep vals labels s) (acc:s.reg 156=(a:ℤ)) (hi:360 ≤ last)
    (held:keepKey body=true) (it:writesReg 157 body=false) (lim:writesReg last body=false)
    (step:∀i<n,∀v:State,KeyRegs n pts sep vals labels v → v.heap=s.heap → v.reg 157=(i:ℤ) →
      ∀k:ℕ,v.reg 156=(k:ℤ) → ∃t z,Executes n m body v t z ∧ z ≤ K ∧
      t.reg 156=(((digits i).foldl Naming.push k:ℕ):ℤ) ∧ t.heap=v.heap ∧ t.output=v.output ∧ t.closed=v.closed) :
    ∃t z,Executes n m (forCount 157 last 64 body) s t z ∧ z ≤ 9+n*(K+5) ∧
    t.reg 156=((((List.range n).flatMap digits).foldl Naming.push a:ℕ):ℤ) ∧
    KeyRegs n pts sep vals labels t ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let value:=fun i=>((List.range i).flatMap digits).foldl Naming.push a
  let P:=fun i (v:State)=>v.reg 156=(value i:ℤ) ∧ KeyRegs n pts sep vals labels v ∧
    v.heap=s.heap ∧ v.output=s.output ∧ v.closed=s.closed
  have low (j:ℕ) (hj:j<157) : (forSetup 157 last 64 s).reg j=s.reg j:=by
    simp [forSetup,State.assign,Function.update_of_ne (show j≠last by omega),Function.update_of_ne (show j≠157 by omega)]
  have begin':P 0 (forSetup 157 last 64 s):=by
    exact ⟨(low 156 (by decide)).trans acc,⟨(low 6 (by decide)).trans regs.one,(low 64 (by decide)).trans regs.size,
     (low 153 (by decide)).trans regs.pts,(low 154 (by decide)).trans regs.boundaryPtr,(low 155 (by decide)).trans regs.index,
     (low 76 (by decide)).trans regs.label⟩,rfl,rfl,rfl⟩
  have next (i:ℕ) (bound:i<n) (v:State) (good:P i v) (idx:v.reg 157=(i:ℤ)) (_:v.reg last=(n:ℤ)-1):
      ∃t z,Executes n m body v t z ∧ z ≤ K ∧ t.reg 157=v.reg 157 ∧ t.reg last=v.reg last ∧
        P (i+1) (t.assign 157 (t.reg 157+1)):=by
    obtain ⟨mark,r,heap,out,cl⟩:=good
    obtain ⟨t,z,run,tm,val,newHeap,newOut,newCl⟩:=step i bound v r heap idx _ mark
    have ng:=r.kept run held
    refine ⟨t,z,run,tm,run.preserves _ it,run.preserves _ lim,?_,
      ⟨ng.one,ng.size,ng.pts,ng.boundaryPtr,ng.index,ng.label⟩,newHeap.trans heap,newOut.trans out,newCl.trans cl⟩
    change t.reg 156=_
    simpa [value,List.range_succ,List.flatMap_append,List.foldl_append] using val
  obtain ⟨t,z,ex,tm,good⟩:=source_for (N:=n) (input:=m) 157 last 64 n K body P (by omega) (by decide) s regs.size begin' next
  exact ⟨t,z,ex,tm,good⟩
def pointDigits (m:ℕ → ℤ) (p i:ℕ):List ℕ:=if 1 ≤ m (p+i) then [i+1] else []
def pairDigits (m:ℕ → ℤ) (p v l i:ℕ):List ℕ:=if 1 ≤ m (p+i) then [i,labelOf m v l i] else []
def keyPoints (m:ℕ → ℤ) (p n:ℕ):List ℕ:=(List.range n).filter (fun i=>decide (1 ≤ m (p+i)))
def keyPairs (m:ℕ → ℤ) (p v l n:ℕ):List (ℕ×ℕ) := (keyPoints m p n).map (fun i=>(i,labelOf m v l i))
theorem point_digits (m:ℕ → ℤ) (p:ℕ) (xs:List ℕ):
    xs.flatMap (pointDigits m p)=(xs.filter (fun i=>decide (1 ≤ m (p+i)))).map Nat.succ:=by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>by_cases hit:1 ≤ m (p+i) <;> simp [pointDigits,hit,ih]
theorem pair_digits (m:ℕ → ℤ) (p v l:ℕ) (xs:List ℕ):
    xs.flatMap (pairDigits m p v l)=Naming.pairs ((xs.filter (fun i=>decide (1 ≤ m (p+i)))).map (fun i=>(i,labelOf m v l i))):=by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>by_cases hit:1 ≤ m (p+i) <;> simp [pairDigits,hit,Naming.pairs] at ih ⊢ <;> simp_all
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open SingleCircuit
theorem key_scan (n p b v l L:ℕ) (input:ℤ → ℤ) (s:State) (regs:KeyRegs n p b v l s)
    (values:∀i<n,0 ≤ s.heap (v+i)) (labels:∀i<n,0 ≤ s.heap (l+(s.heap (v+i)).toNat))
    (limit:∀i<n,labelOf s.heap v l i ≤ L):
    ∃t k,Executes n input src_name_key s t k ∧ k ≤ 1000*(n+1)*(n+L+1) ∧
      t.reg 158=(Naming.name (keyPoints s.heap p n,keyPairs s.heap b v l n):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let u:=(s.assign 374 0).assign 156 0
  have setZero:Executes n input (.op (.regular (.set 374 0))) s (s.assign 374 0) 1:=.op rfl
  have copyZero:Executes n input (.op (.regular (.copy 156 374))) (s.assign 374 0) u 1:=.op rfl
  have init:PrefixRun n input [.op (.regular (.set 374 0)),.op (.regular (.copy 156 374))] s u 4:=
    .cons setZero (.cons copyZero (.nil u))
  have r0:KeyRegs n p b v l u:=⟨regs.one,regs.size,regs.pts,regs.boundaryPtr,regs.index,regs.label⟩
  let left:=pointDigits s.heap p
  let right:=pairDigits s.heap b v l
  let A:=((List.range n).flatMap left).foldl Naming.push 0
  obtain ⟨t,k,first,tm,ain,r1,tHeap,tOut,tClosed⟩:=key_loop n p b v l 0 (125+10*n) 376 input pointStep left u r0 rfl
    (by decide) (by decide) (by decide) (by decide) (by
      intro i hi w rr hw idx a acc
      obtain ⟨z,tk,ex,ct,ret,heap,out,cl⟩:=point_step n p i a input w rr.one rr.pts idx acc
      refine ⟨z,tk,ex,by omega,?_,heap,out,cl⟩
      have mem:w.heap=s.heap:=hw
      by_cases hit:1 ≤ s.heap (p+i) <;> simpa [left,pointDigits,hit,mem] using ret)
  let mid:=t.assign 387 0
  have st:Executes n input (.op (.regular (.set 387 0))) t mid 1:=.op rfl
  obtain ⟨w,j,delim,dt,digit,wHeap,wOut,wClosed⟩:=call_digit n A 0 387 385 input mid (by decide) ain
    (by simp [mid,State.assign])
  have r2:KeyRegs n p b v l w:=(r1.kept st (by decide)).kept delim.finish (by decide)
  have memw:w.heap=s.heap:=wHeap.trans tHeap
  obtain ⟨z,zc,second,zt,endVal,_,zh,zo,zcl⟩:=key_loop n p b v l (Naming.push A 0) (290+10*(n+L))
    389 input pairStep right w r2 digit (by decide) (by decide) (by decide) (by decide) (by
      intro i hi y ry h idx a acc
      have hy:y.heap=s.heap:=h.trans memw
      obtain ⟨z,tk,ex,ct,ret,heap,out,cl⟩:=pair_step n p b v l i a L input y ry idx acc
        (by rw [hy];exact values i hi) (by rw [hy];exact labels i hi) (by simpa [hy] using limit i hi)
      refine ⟨z,tk,ex,by omega,?_,heap,out,cl⟩
      by_cases hit:1 ≤ s.heap (b+i) <;> simpa [right,pairDigits,hit,hy] using ret)
  let raw:=((List.range n).flatMap right).foldl Naming.push (Naming.push A 0)
  have exactName:raw=Naming.name (keyPoints s.heap p n,keyPairs s.heap b v l n):=by
    unfold Naming.name;rw [←Naming.accumulated]
    simp [Naming.digits,List.foldl_append,raw,A,left,right,point_digits,pair_digits,keyPoints,keyPairs]
  let endState:=z.assign 158 (raw:ℤ)
  have ret:Executes n input (.op (.regular (.copy 158 156))) z endState 1:=op_copy _ _ _ _ endVal
  have suffix:=Executes.seq second (Executes.seq ret (Executes.skip endState))
  have full:Executes n input src_name_key s endState _:=init.continue _ (.seq first (.seq st (delim.continue _ suffix)))
  refine ⟨endState,_,full,?_,by simp [endState,State.assign,exactName],zh.trans memw,
    zo.trans (wOut.trans tOut),zcl.trans (wClosed.trans tClosed)⟩
  ring_nf at tm zt ⊢ <;> omega
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace Logical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 30000
open SingleCircuit TightLanguage
theorem pair_step_supported (n point boundary values labels i a L:ℕ) (input:ℤ → ℤ) (s:State)
    (regs:KeyRegs n point boundary values labels s) (idx:s.reg 157=(i:ℤ)) (acc:s.reg 156=(a:ℤ))
    (nonneg:1 ≤ s.heap (boundary+i) → 0 ≤ s.heap (values+i)) (leg:1 ≤ s.heap (boundary+i) → 0 ≤ s.heap (labels+(s.heap (values+i)).toNat))
    (bounded:1 ≤ s.heap (boundary+i) → labelOf s.heap values labels i ≤ L):
    ∃t k,Executes n input pairStep s t k ∧ k ≤ 290+10*(i+L) ∧
    t.reg 156=((if 1 ≤ s.heap (boundary+i) then Naming.push (Naming.push a i) (labelOf s.heap values labels i) else a:ℕ):ℤ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed :=by
  by_cases hit:1 ≤ s.heap (boundary+i)
  · exact pair_step n point boundary values labels i a L input s regs idx acc (nonneg hit) (leg hit) (bounded hit)
  · let u:=s.assign 390 (s.heap (boundary+i))
    have x:Executes n input (.op (.fetch 390 154 157)) s u 64:=op_fetch s _ _ _ boundary i regs.boundaryPtr idx
    have br:Executes n input (.cond 6 390 (chain pairCall) .skip) u u 2:=
      .no (by change ¬ s.reg 6 ≤ s.heap (boundary+i);rwa [regs.one]) (.skip _)
    exact ⟨u,_,.seq x (.seq br (.skip _)),by omega,by simpa [u,State.assign,hit] using acc,rfl,rfl,rfl⟩
theorem key_scan_supported (n p b v l L:ℕ) (input:ℤ → ℤ) (s:State) (regs:KeyRegs n p b v l s)
    (values:∀i<n,1 ≤ s.heap (b+i) → 0 ≤ s.heap (v+i)) (labels:∀i<n,1 ≤ s.heap (b+i) → 0 ≤ s.heap (l+(s.heap (v+i)).toNat))
    (limit:∀i<n,1 ≤ s.heap (b+i) → labelOf s.heap v l i ≤ L):
    ∃t k,Executes n input src_name_key s t k ∧ k ≤ 1000*(n+1)*(n+L+1) ∧
      t.reg 158=(Naming.name (keyPoints s.heap p n,keyPairs s.heap b v l n):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let u:=(s.assign 374 0).assign 156 0
  have setZero:Executes n input (.op (.regular (.set 374 0))) s (s.assign 374 0) 1:=.op rfl
  have copyZero:Executes n input (.op (.regular (.copy 156 374))) (s.assign 374 0) u 1:=.op rfl
  have init:PrefixRun n input [.op (.regular (.set 374 0)),.op (.regular (.copy 156 374))] s u 4:=
    .cons setZero (.cons copyZero (.nil u))
  have r0:KeyRegs n p b v l u:=⟨regs.one,regs.size,regs.pts,regs.boundaryPtr,regs.index,regs.label⟩
  let left:=pointDigits s.heap p
  let right:=pairDigits s.heap b v l
  let A:=((List.range n).flatMap left).foldl Naming.push 0
  obtain ⟨t,k,first,tm,ain,r1,tHeap,tOut,tClosed⟩:=key_loop n p b v l 0 (125+10*n) 376 input pointStep left u r0 rfl
    (by decide) (by decide) (by decide) (by decide) (by
      intro i hi w rr hw idx a acc
      obtain ⟨z,tk,ex,ct,ret,heap,out,cl⟩:=point_step n p i a input w rr.one rr.pts idx acc
      refine ⟨z,tk,ex,by omega,?_,heap,out,cl⟩
      have mem:w.heap=s.heap:=hw
      by_cases hit:1 ≤ s.heap (p+i) <;> simpa [left,pointDigits,hit,mem] using ret)
  let mid:=t.assign 387 0
  have st:Executes n input (.op (.regular (.set 387 0))) t mid 1:=.op rfl
  obtain ⟨w,j,delim,dt,digit,wHeap,wOut,wClosed⟩:=call_digit n A 0 387 385 input mid (by decide) ain
    (by simp [mid,State.assign])
  have r2:KeyRegs n p b v l w:=(r1.kept st (by decide)).kept delim.finish (by decide)
  have memw:w.heap=s.heap:=wHeap.trans tHeap
  obtain ⟨z,zc,second,zt,endVal,_,zh,zo,zcl⟩:=key_loop n p b v l (Naming.push A 0) (290+10*(n+L))
    389 input pairStep right w r2 digit (by decide) (by decide) (by decide) (by decide) (by
      intro i hi y ry h idx a acc
      have hy:y.heap=s.heap:=h.trans memw
      obtain ⟨z,tk,ex,ct,ret,heap,out,cl⟩:=pair_step_supported n p b v l i a L input y ry idx acc
        (by rw [hy];exact values i hi) (by rw [hy];exact labels i hi) (by simpa [hy] using limit i hi)
      refine ⟨z,tk,ex,by omega,?_,heap,out,cl⟩
      by_cases hit:1 ≤ s.heap (b+i) <;> simpa [right,pairDigits,hit,hy] using ret)
  let raw:=((List.range n).flatMap right).foldl Naming.push (Naming.push A 0)
  have exactName:raw=Naming.name (keyPoints s.heap p n,keyPairs s.heap b v l n):=by
    unfold Naming.name;rw [←Naming.accumulated]
    simp [Naming.digits,List.foldl_append,raw,A,left,right,point_digits,pair_digits,keyPoints,keyPairs]
  let endState:=z.assign 158 (raw:ℤ)
  have ret:Executes n input (.op (.regular (.copy 158 156))) z endState 1:=op_copy _ _ _ _ endVal
  have suffix:=Executes.seq second (Executes.seq ret (Executes.skip endState))
  have full:Executes n input src_name_key s endState _:=init.continue _ (.seq first (.seq st (delim.continue _ suffix)))
  refine ⟨endState,_,full,?_,by simp [endState,State.assign,exactName],zh.trans memw,
    zo.trans (wOut.trans tOut),zcl.trans (wClosed.trans tClosed)⟩
  ring_nf at tm zt ⊢ <;> omega
theorem empty_boundary_key (n p b v l:ℕ) (input:ℤ → ℤ) (s:State) (regs:KeyRegs n p b v l s)
    (empty:∀i<n,¬ 1 ≤ s.heap (b+i)):
    ∃t k,Executes n input src_name_key s t k ∧ k ≤ 1000*(n+1)^2 ∧
      t.reg 158=(Naming.name (keyPoints s.heap p n,[]):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have void:keyPoints s.heap b n=[]:=by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    simpa using empty i (List.mem_range.mp hi)
  have h:=key_scan_supported n p b v l 0 input s regs
    (fun i hi h=>(empty i hi h).elim) (fun i hi h=>(empty i hi h).elim) (fun i hi h=>(empty i hi h).elim)
  simpa [keyPairs,void,pow_two,Nat.mul_assoc] using h
end Logical
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
theorem solution (n p b v l:ℕ) (input:ℤ → ℤ) (s:Logical.State)
    (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (point:s.reg 153=(p:ℤ)) (boundary:s.reg 154=(b:ℤ))
    (index:s.reg 155=(v:ℤ)) (table:s.reg 76=(l:ℤ)) (empty:∀i<n,¬ 1 ≤ s.heap (b+i)):
    let pts:=(List.range n).filter (fun i=>decide (1 ≤ s.heap (p+i)))
    ∃t k,Logical.Executes n input Logical.src_name_key s t k ∧ k ≤ 1000*(n+1)^2 ∧
      t.reg 158=(CandidateRAM.Naming.name (pts,[]):ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := Logical.empty_boundary_key n p b v l input s ⟨one,sz,point,boundary,index,table⟩ empty
