-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.matrix_and_row_scans
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:35:05.578545+00:00
-- url     : https://prove2.me/submissions/5dc7f79b-ae96-47e2-969c-135b4f288a08

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
theorem matrix_word (n i j:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ))
    (ri:s.reg 159=(i:ℤ)) (rj:s.reg 160=(j:ℤ)):
    ∃t k,Executes n input src_imat s t k ∧ k ≤ 50+6*n ∧ t.reg 161=input (cell 6 (i*n+j)) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let q:=cell 6 (i*n+j)
  have aq:q= -87-64*((i:ℤ)*n+j):=by simp [q,cell,word];ring
  have raw:rawInput q=true:=by
    have pos:0 ≤ (i:ℤ)*n:=by positivity
    simp [q,cell,word,rawInput];omega
  have h:∃t k,evalLine n input src_imat s=some (t,k) ∧ k ≤ 50+6*n ∧ t.reg 161=input q ∧
        t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    simp [src_imat,chain,evalLine,Operation.next,regularNext,State.assign,one,size,ri,rj,←aq,raw]
    omega
  obtain ⟨t,k,run,tm,res,mem,out,flag⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ run,tm,res,mem,out,flag⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def leastMarked (n:ℕ) (f:ℕ → Bool) (i:ℕ) := ((List.range i).filter f).headD n
theorem least_step (n i:ℕ) (f:ℕ → Bool) (bound:i<n) :
    leastMarked n f (i+1)=if f i=true ∧ i<leastMarked n f i then i else leastMarked n f i:=by
  unfold leastMarked;rw [List.range_succ,List.filter_append]
  cases rows:(List.range i).filter f with
  | nil=>cases hi:f i <;> simp [hi,bound]
  | cons a rest=>
    have lt:a < i:=by
      have h:a∈(List.range i).filter f:=by rw [rows];simp
      exact List.mem_range.mp (List.mem_filter.mp h).1
    simp [show ¬i<a by omega]
def firstBody:=chain [.op (.fetch 354 144 146),.op (.regular (.copy 353 354)),
  .cond 6 353 (chain [.cond 145 146 (.op (.regular (.set 357 0))) (.op (.regular (.set 357 1))),
    .op (.regular (.copy 353 357))]) .skip,
  .cond 6 353 (.op (.regular (.copy 145 146))) .skip]
theorem first_iteration (n base i low:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1)
    (ptr:s.reg 144=(base:ℤ)) (idx:s.reg 146=(i:ℤ)) (cur:s.reg 145=(low:ℤ)):
    ∃t k,Executes n m firstBody s t k ∧ k ≤ 90 ∧
    t.reg 145=((if 1 ≤ s.heap (base+i) ∧ i<low then i else low:ℕ):ℤ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have h:∃t k,evalLine n m firstBody s=some (t,k) ∧ k ≤ 90 ∧
      t.reg 145=((if 1 ≤ s.heap (base+i) ∧ i<low then i else low:ℕ):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    have cast:((base:ℤ)+i).toNat=base+i:=by omega
    have pos:0 ≤ (base:ℤ)+i:=by omega
    by_cases marked:1 ≤ s.heap (base+i) <;> by_cases before:low ≤ i <;>
      simp [firstBody,chain,evalLine,Operation.next,regularNext,State.assign,one,ptr,idx,cur,
        cast,pos,marked,before,show i<low ↔ ¬low ≤ i by omega]
  obtain ⟨t,k,ex,tm,val,heap,out,flag⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,val,heap,out,flag⟩

theorem first_scan (n base:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ)) (ptr:s.reg 144=(base:ℤ)):
    ∃t k,Executes n m src_first s t k ∧ k ≤ 15+95*n ∧
    t.reg 147=(((List.range n).filter (fun i=>decide (1 ≤ s.heap (base+i)))).headD n:ℕ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let f:=fun i=>decide (1 ≤ s.heap (base+i))
  let u:=s.assign 145 (n:ℤ)
  have head:Executes n m (.op (.regular (.copy 145 64))) s u 1:=op_copy _ _ _ _ size
  let P:=fun i (v:State)=>v.reg 145=(leastMarked n f i:ℤ) ∧ v.reg 6=1 ∧ v.reg 144=(base:ℤ) ∧
    v.heap=s.heap ∧ v.output=s.output ∧ v.closed=s.closed
  have start:P 0 (forSetup 146 352 64 u):=by exact ⟨by simp [forSetup,u,State.assign,leastMarked],one,ptr,rfl,rfl,rfl⟩
  have next (i:ℕ) (hi:i<n) (v:State) (good:P i v) (idx:v.reg 146=(i:ℤ)) (_:v.reg 352=(n:ℤ)-1):
      ∃t k,Executes n m firstBody v t k ∧ k ≤ 90 ∧ t.reg 146=v.reg 146 ∧ t.reg 352=v.reg 352 ∧
        P (i+1) (t.assign 146 (t.reg 146+1)):=by
    obtain ⟨val,v1,vptr,vh,vo,vc⟩:=good
    obtain ⟨t,k,ex,tm,res,heap,out,flag⟩:=first_iteration n base i _ m v v1 vptr idx val
    refine ⟨t,k,ex,tm,ex.preserves 146 (by decide),ex.preserves 352 (by decide),?_,
      (ex.preserves 6 (by decide)).trans v1,(ex.preserves 144 (by decide)).trans vptr,
      heap.trans vh,out.trans vo,flag.trans vc⟩
    change t.reg 145=_
    rw [res,vh,least_step _ _ _ hi];simp [f]
  obtain ⟨t,k,ex,tm,val,_,_,mem,out,flag⟩:=source_for (N:=n) (input:=m) 146 352 64 n 90 firstBody P
    (by decide) (by decide) u size start next
  let z:=t.assign 147 (t.reg 145)
  have tail:Executes n m (.op (.regular (.copy 147 145))) t z 1:=op_copy _ _ _ _ rfl
  exact ⟨z,_,.seq head (.seq ex (.seq tail (.skip _))),by omega,by simpa [z,State.assign,f,leastMarked] using val,mem,out,flag⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def equalBody:=chain [.op (.fetch 366 148 151),.op (.fetch 369 149 151),
  .cond 366 369 (.cond 369 366 (.op (.regular (.set 365 0))) (.op (.regular (.set 365 1))))
    (.op (.regular (.set 365 1))),
  .cond 6 365 (chain [.op (.regular (.set 372 0)),.op (.regular (.copy 150 372))]) .skip]
theorem equal_iteration (n a b i:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1)
    (left:s.reg 148=(a:ℤ)) (right:s.reg 149=(b:ℤ)) (idx:s.reg 151=(i:ℤ)):
    ∃t k,Executes n m equalBody s t k ∧ k ≤ 145 ∧
    t.reg 150=(if s.heap (a+i)=s.heap (b+i) then s.reg 150 else 0) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have h:∃t k,evalLine n m equalBody s=some (t,k) ∧ k ≤ 145 ∧
      t.reg 150=(if s.heap (a+i)=s.heap (b+i) then s.reg 150 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    have ca:((a:ℤ)+i).toNat=a+i:=by omega
    have cb:((b:ℤ)+i).toNat=b+i:=by omega
    have pa:0 ≤ (a:ℤ)+i:=by omega
    have pb:0 ≤ (b:ℤ)+i:=by omega
    rcases lt_trichotomy (s.heap (a+i)) (s.heap (b+i)) with lt|eq|gt
    · simp [equalBody,chain,evalLine,Operation.next,regularNext,State.assign,one,left,right,idx,ca,cb,pa,pb,
        lt.le,not_le_of_gt lt,ne_of_lt lt]
    · simp [equalBody,chain,evalLine,Operation.next,regularNext,State.assign,one,left,right,idx,ca,cb,pa,pb,eq]
    · simp [equalBody,chain,evalLine,Operation.next,regularNext,State.assign,one,left,right,idx,ca,cb,pa,pb,
        gt.le,not_le_of_gt gt,ne_of_gt gt]
  obtain ⟨t,k,ex,tm,val,heap,out,flag⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,val,heap,out,flag⟩

theorem equal_scan (n a b:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ))
    (left:s.reg 148=(a:ℤ)) (right:s.reg 149=(b:ℤ)):
    ∃t k,Executes n m src_equal_rows s t k ∧ k ≤ 17+150*n ∧
    (t.reg 152=1 ↔ ∀i<n,s.heap (a+i)=s.heap (b+i)) ∧
    (t.reg 152=0 ∨ t.reg 152=1) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  classical
  let EqTo:=fun i=>∀j < i,s.heap (a+j)=s.heap (b+j)
  let u:=(s.assign 362 1).assign 150 1
  let P:=fun i (v:State)=>v.reg 150=(if EqTo i then 1 else 0) ∧ v.reg 6=1 ∧
    v.reg 148=(a:ℤ) ∧ v.reg 149=(b:ℤ) ∧ v.heap=s.heap ∧ v.output=s.output ∧ v.closed=s.closed
  have start:P 0 (forSetup 151 364 64 u):=by
    refine ⟨?_,one,left,right,rfl,rfl,rfl⟩;simp [forSetup,u,State.assign,EqTo]
  have next (i:ℕ) (hi:i<n) (v:State) (good:P i v) (idx:v.reg 151=(i:ℤ)) (_:v.reg 364=(n:ℤ)-1):
      ∃t k,Executes n m equalBody v t k ∧ k ≤ 145 ∧ t.reg 151=v.reg 151 ∧ t.reg 364=v.reg 364 ∧
        P (i+1) (t.assign 151 (t.reg 151+1)):=by
    obtain ⟨val,v1,vl,vr,vh,vo,vc⟩:=good
    obtain ⟨t,k,ex,tm,res,heap,out,flag⟩:=equal_iteration n a b i m v v1 vl vr idx
    refine ⟨t,k,ex,tm,ex.preserves 151 (by decide),ex.preserves 364 (by decide),?_,
      (ex.preserves 6 (by decide)).trans v1,(ex.preserves 148 (by decide)).trans vl,
      (ex.preserves 149 (by decide)).trans vr,heap.trans vh,out.trans vo,flag.trans vc⟩
    change t.reg 150=_
    have iff:EqTo (i+1) ↔ EqTo i ∧ s.heap (a+i)=s.heap (b+i):=by
      constructor
      · intro h;exact ⟨fun j hj=>h j (by omega),h i (by omega)⟩
      · rintro ⟨h,eq⟩ j hj;by_cases last:j=i
        · subst j;exact eq
        · exact h j (by omega)
    rw [res,vh,val];by_cases h:EqTo i <;> by_cases d:s.heap (a+i)=s.heap (b+i) <;> simp [iff,h,d]
  obtain ⟨t,k,ex,tm,val,_,_,_,mem,out,flag⟩:=source_for (N:=n) (input:=m) 151 364 64 n 145 equalBody P
    (by decide) (by decide) u size start next
  let z:=t.assign 152 (t.reg 150)
  have tail:Executes n m (.op (.regular (.copy 152 150))) t z 1:=op_copy _ _ _ _ rfl
  have first:Executes n m (.op (.regular (.set 362 1))) s (s.assign 362 1) 1:=.op rfl
  have second:Executes n m (.op (.regular (.copy 150 362))) (s.assign 362 1) u 1:=.op rfl
  refine ⟨z,_,.seq first (.seq second (.seq ex (.seq tail (.skip _)))),by omega,?_,?_,mem,out,flag⟩
  · change t.reg 150=1 ↔ EqTo n;rw [val];split_ifs <;> simp_all
  · change t.reg 150=0 ∨ t.reg 150=1;rw [val];split_ifs <;> simp
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem solution :
    (∀(n i j:ℕ) (input:ℤ → ℤ) (s:Logical.State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ))
    (ri:s.reg 159=(i:ℤ)) (rj:s.reg 160=(j:ℤ)),∃t k,Logical.Executes n input src_imat s t k ∧ k ≤ 50+6*n ∧ t.reg 161=input (cell 6 (i*n+j)) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed) ∧
    (∀(n base:ℕ) (m:ℤ → ℤ) (s:Logical.State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ)) (ptr:s.reg 144=(base:ℤ)),∃t k,Logical.Executes n m src_first s t k ∧ k ≤ 15+95*n ∧
    t.reg 147=(((List.range n).filter (fun i=>decide (1 ≤ s.heap (base+i)))).headD n:ℕ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed) ∧
    (∀(n a b:ℕ) (m:ℤ → ℤ) (s:Logical.State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ))
    (left:s.reg 148=(a:ℤ)) (right:s.reg 149=(b:ℤ)),∃t k,Logical.Executes n m src_equal_rows s t k ∧ k ≤ 17+150*n ∧
    (t.reg 152=1 ↔ ∀i<n,s.heap (a+i)=s.heap (b+i)) ∧
    (t.reg 152=0 ∨ t.reg 152=1) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed) := ⟨Logical.matrix_word,Logical.first_scan,Logical.equal_scan⟩
