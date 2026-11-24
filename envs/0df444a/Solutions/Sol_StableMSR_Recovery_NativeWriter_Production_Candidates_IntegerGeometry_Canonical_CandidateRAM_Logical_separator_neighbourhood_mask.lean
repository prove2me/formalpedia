-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.separator_neighbourhood_mask
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:42:11.856126+00:00
-- url     : https://prove2.me/submissions/70add1dd-3481-47a6-b0bc-f77d46a3e423

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
def rimBit:=chain [.op (.fetch 335 139 142),.op (.regular (.copy 334 335)),
  .cond 6 334 (chain [.op (.multiply 341 142 64),.op (.regular (.add 340 341 141)),
    .op (.fetch 338 75 340),.op (.regular (.copy 334 338))]) .skip,
  .cond 6 334 (chain [.op (.regular (.set 348 1)),.op (.save 140 141 348)]) .skip]
def sees (m:ℕ → ℤ) (p edge n i j:ℕ) : Prop := 1 ≤ m (p+j) ∧ 1 ≤ m (edge+(j*n+i))
def witnessed (m:ℕ → ℤ) (p edge n i k:ℕ) : Prop := ∃j<k,sees m p edge n i j
theorem witness_succ (m:ℕ → ℤ) (p edge n i k:ℕ):
    witnessed m p edge n i (k+1) ↔ witnessed m p edge n i k ∨ sees m p edge n i k:=by
  constructor
  · rintro ⟨j,h,b⟩;by_cases eq:j=k
    · exact .inr (eq ▸ b)
    · exact .inl ⟨j,by omega,b⟩
  · rintro (⟨j,h,b⟩|b)
    · exact ⟨j,by omega,b⟩
    · exact ⟨k,by omega,b⟩
structure RimArgs (n point edge mask i:ℕ) (s:State):Prop where
  one:s.reg 6=1
  size:s.reg 64=(n:ℤ)
  pts:s.reg 139=(point:ℤ)
  ed:s.reg 75=(edge:ℤ)
  dst:s.reg 140=(mask:ℤ)
  row:s.reg 141=(i:ℤ)
theorem rim_bit (n p edge mask i j:ℕ) (m:ℤ → ℤ) (s:State) (arg:RimArgs n p edge mask i s)
    (idx:s.reg 142=(j:ℤ)): ∃t k,Executes n m rimBit s t k ∧ k ≤ 230+6*n ∧
    (∀q,t.heap q=if q=mask+i ∧ sees s.heap p edge n i j then 1 else s.heap q) ∧
    t.output=s.output ∧ t.closed=s.closed:=by
  classical
  obtain ⟨one,size,ptr,ed,dst,row⟩:=arg
  have sumNat (u v:ℕ):((u:ℤ)+v).toNat=u+v:=by omega
  have pos (u v:ℕ):0 ≤ (u:ℤ)+v:=by positivity
  have coord:(edge:ℤ)+((j:ℤ)*n+i)=((edge+(j*n+i):ℕ):ℤ):=by push_cast;rfl
  have coordinate:((edge:ℤ)+((j:ℤ)*n+i)).toNat=edge+(j*n+i):=congrArg Int.toNat coord
  have sign:0 ≤ (edge:ℤ)+((j:ℤ)*n+i):=by positivity
  have h:∃t k,evalLine n m rimBit s=some (t,k) ∧ k ≤ 230+6*n ∧
      (∀q,t.heap q=if q=mask+i ∧ sees s.heap p edge n i j then 1 else s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed:=by
    by_cases point:1 ≤ s.heap (p+j) <;> by_cases hit:1 ≤ s.heap (edge+(j*n+i)) <;>
      simp [rimBit,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,size,ptr,ed,dst,
        row,idx,sees,sumNat,pos,coordinate,sign,point,hit,Function.update_apply] <;> omega
  obtain ⟨t,k,ex,tm,heap,out,flag⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,heap,out,flag⟩

theorem rim_neighbours (n p edge mask i:ℕ) (m:ℤ → ℤ) (s:State) (arg:RimArgs n p edge mask i s)
    (pointsBelow:p+n ≤ mask) (edgeBelow:edge+n*n ≤ mask) (rowLt:i<n):
    ∃t k,Executes n m (forCount 142 333 64 rimBit) s t k ∧ k ≤ 9+n*(235+6*n) ∧
    (∀q,t.heap q=if q=mask+i ∧ witnessed s.heap p edge n i n then 1 else s.heap q) ∧
    t.output=s.output ∧ t.closed=s.closed:=by
  classical
  let P:=fun k (u:State)=>RimArgs n p edge mask i u ∧
    (∀q,u.heap q=if q=mask+i ∧ witnessed s.heap p edge n i k then 1 else s.heap q) ∧
    u.output=s.output ∧ u.closed=s.closed
  have start:P 0 (forSetup 142 333 64 s):=by
    refine ⟨⟨arg.one,arg.size,arg.pts,arg.ed,arg.dst,arg.row⟩,?_,rfl,rfl⟩
    intro q;change s.heap q=_;simp [witnessed]
  have step (j:ℕ) (hj:j<n) (u:State) (good:P j u) (idx:u.reg 142=(j:ℤ)) (_:u.reg 333=(n:ℤ)-1):
      ∃t k,Executes n m rimBit u t k ∧ k ≤ 230+6*n ∧ t.reg 142=u.reg 142 ∧ t.reg 333=u.reg 333 ∧
        P (j+1) (t.assign 142 (t.reg 142+1)):=by
    obtain ⟨args,heap,out,cl⟩:=good
    obtain ⟨t,k,ex,tm,wrote,newout,newcl⟩:=rim_bit n p edge mask i j m u args idx
    have less:j*n+i<n*n:=by
      have le: (j+1)*n ≤ n*n:=Nat.mul_le_mul_right _ hj
      rw [Nat.succ_mul] at le;omega
    have same:sees u.heap p edge n i j ↔ sees s.heap p edge n i j:=by
      unfold sees
      rw [heap (p+j),heap (edge+(j*n+i)),if_neg (by rintro ⟨f,_⟩;omega),if_neg (by rintro ⟨f,_⟩;omega)]
    refine ⟨t,k,ex,tm,ex.preserves 142 (by decide),ex.preserves 333 (by decide),
      ⟨(ex.preserves 6 (by decide)).trans args.one,(ex.preserves 64 (by decide)).trans args.size,
       (ex.preserves 139 (by decide)).trans args.pts,(ex.preserves 75 (by decide)).trans args.ed,
       (ex.preserves 140 (by decide)).trans args.dst,(ex.preserves 141 (by decide)).trans args.row⟩,
       ?_,newout.trans out,newcl.trans cl⟩
    intro q;change t.heap q=_
    rw [wrote,heap q]
    by_cases pos:q=mask+i <;> by_cases hit:sees s.heap p edge n i j <;>
      by_cases prev:witnessed s.heap p edge n i j <;> simp [pos,same,hit,prev,witness_succ]
  obtain ⟨t,k,ex,tm,_,heap,out,cl⟩:=source_for (N:=n) (input:=m) 142 333 64 n (230+6*n) rimBit P
    (by decide) (by decide) s arg.size start step
  exact ⟨t,k,ex,by simpa only [show 230+6*n+5=235+6*n by omega] using tm,heap,out,cl⟩
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
def rimTest : List Program:=[.op (.fetch 325 71 141),.op (.regular (.copy 324 325)),
  .cond 6 324 (chain [.op (.fetch 329 139 141),
    .cond 6 329 (.op (.regular (.set 328 0))) (.op (.regular (.set 328 1))),
    .op (.regular (.copy 324 328))]) .skip]
def rimRow := chain (rimTest++[.cond 6 324 (forCount 142 333 64 rimBit) .skip])
def outsidePiece (m:ℕ → ℤ) (a p i:ℕ):Prop := 1 ≤ m (a+i) ∧ ¬1 ≤ m (p+i)
def onRim (m:ℕ → ℤ) (a p edge n i:ℕ):Prop := outsidePiece m a p i ∧ witnessed m p edge n i n
theorem rim_test (n a p i:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1) (active:s.reg 71=(a:ℤ))
    (point:s.reg 139=(p:ℤ)) (row:s.reg 141=(i:ℤ)):
    ∃t k,Executes n m (chain rimTest) s t k ∧ k ≤ 158 ∧
      (1 ≤ t.reg 324 ↔ outsidePiece s.heap a p i) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have sumNat (u v:ℕ):((u:ℤ)+v).toNat=u+v:=by omega
  have pos (u v:ℕ):0 ≤ (u:ℤ)+v:=by positivity
  have h:∃t k,evalLine n m (chain rimTest) s=some (t,k) ∧ k ≤ 158 ∧
      (1 ≤ t.reg 324 ↔ outsidePiece s.heap a p i) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    by_cases aa:1 ≤ s.heap (a+i) <;> by_cases pp:1 ≤ s.heap (p+i) <;>
      simp [rimTest,chain,evalLine,Operation.next,regularNext,State.assign,one,active,point,row,sumNat,pos,
        aa,pp,outsidePiece] <;> omega
  obtain ⟨t,k,ex,tm,val,heap,out,flag⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,val,heap,out,flag⟩
theorem rim_row (n a p edge mask i:ℕ) (m:ℤ → ℤ) (s:State) (arg:RimArgs n p edge mask i s)
    (active:s.reg 71=(a:ℤ)) (pointsBelow:p+n ≤ mask) (edgeBelow:edge+n*n ≤ mask) (lt:i<n):
    ∃t k,Executes n m rimRow s t k ∧ k ≤ 175+n*(235+6*n) ∧
      (∀q,t.heap q=if q=mask+i ∧ onRim s.heap a p edge n i then 1 else s.heap q) ∧
      t.output=s.output ∧ t.closed=s.closed:=by
  obtain ⟨u,k,test,tm,flag,heap,out,cl⟩:=rim_test n a p i m s arg.one active arg.pts arg.row
  obtain ⟨z,front,time⟩:=splitChain rimTest test
  have args:RimArgs n p edge mask i u:=
    ⟨(test.preserves 6 (by decide)).trans arg.one,(test.preserves 64 (by decide)).trans arg.size,
     (test.preserves 139 (by decide)).trans arg.pts,(test.preserves 75 (by decide)).trans arg.ed,
     (test.preserves 140 (by decide)).trans arg.dst,(test.preserves 141 (by decide)).trans arg.row⟩
  let guard:=Program.cond 6 324 (forCount 142 333 64 rimBit) .skip
  obtain ⟨t,c,branch,cc,memory,output,closed⟩:∃t c,Executes n m guard u t c ∧ c ≤ 10+n*(235+6*n) ∧
      (∀q,t.heap q=if q=mask+i ∧ onRim s.heap a p edge n i then 1 else s.heap q) ∧
      t.output=s.output ∧ t.closed=s.closed:=by
    by_cases hit:outsidePiece s.heap a p i
    · obtain ⟨t,c,run,ct,mem,ot,closed⟩:=rim_neighbours n p edge mask i m u args pointsBelow edgeBelow lt
      exact ⟨t,_,.yes (args.one ▸ flag.mpr hit) run,by omega,by simpa [onRim,hit,heap] using mem,ot.trans out,closed.trans cl⟩
    · exact ⟨u,_,.no (by rw [args.one];exact fun h=>hit (flag.mp h)) (.skip _),by omega,
        by intro q;simp [heap,onRim,hit],out,cl⟩
  have tail:Executes n m (chain [guard]) u t (1+c+1):=.seq branch (.skip _)
  have joined:=front.continue _ tail
  exact ⟨t,_,joined,by omega,memory,output,closed⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open scoped Classical
noncomputable def rimStage (heap:ℕ → ℤ) (a p edge n top k q:ℕ):ℤ:=
  if q<top ∨ top+n ≤ q then heap q else if q<top+k ∧ onRim heap a p edge n (q-top) then 1 else 0
theorem rim_stage_step (heap:ℕ → ℤ) (a p edge n top i q:ℕ) (lt:i<n):
    (if q=top+i ∧ onRim heap a p edge n i then 1 else rimStage heap a p edge n top i q)=
      rimStage heap a p edge n top (i+1) q:=by
  by_cases eq:q=top+i
  · subst q
    have inside:¬(top+i<top ∨ top+n ≤ top+i):=by omega
    by_cases hit:onRim heap a p edge n i <;> simp [rimStage,inside,hit,Nat.add_assoc,lt]
  · have iff:q<top+(i+1) ↔ q<top+i:=by omega
    simp [rimStage,eq,iff]
theorem rim_congr {u v:ℕ → ℤ} {a p edge n top i:ℕ} (same:∀q<top,u q=v q)
    (aa:a+n ≤ top) (pp:p+n ≤ top) (ee:edge+n*n ≤ top) (lt:i<n):
    onRim u a p edge n i ↔ onRim v a p edge n i:=by
  have test (j:ℕ) (hj:j<n):sees u p edge n i j ↔ sees v p edge n i j:=by
    have le: (j+1)*n ≤ n*n:=Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at le
    unfold sees;rw [same (p+j) (by omega),same (edge+(j*n+i)) (by omega)]
  have witness:witnessed u p edge n i n ↔ witnessed v p edge n i n:=by
    constructor <;> rintro ⟨j,hj,old⟩
    · exact ⟨j,hj,(test j hj).1 old⟩
    · exact ⟨j,hj,(test j hj).2 old⟩
  unfold onRim outsidePiece;rw [witness,same (a+i) (by omega),same (p+i) (by omega)]

theorem rim_scan (n a p edge top:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1) (zero:s.reg 7=0)
    (size:s.reg 64=(n:ℤ)) (cursor:s.reg 8=(top:ℤ)) (active:s.reg 71=(a:ℤ))
    (point:s.reg 139=(p:ℤ)) (edges:s.reg 75=(edge:ℤ)) (aa:a+n ≤ top) (pp:p+n ≤ top) (ee:edge+n*n ≤ top):
    ∃t k,Executes n m src_rim s t k ∧ k ≤ 600*(n+1)^3 ∧ t.reg 143=(top:ℤ) ∧
      t.reg 8=((top+n:ℕ):ℤ) ∧ (∀i<n,t.heap (top+i)=if onRim s.heap a p edge n i then 1 else 0) ∧
      (∀q,q<top ∨ top+n ≤ q → t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let u:=((s.clear top n).assign 320 (top:ℤ)).assign 8 ((top+n:ℕ):ℤ)
  let v:=u.assign 140 (top:ℤ)
  have alloc:Executes n m (.op (.alloc 320 64)) s u (64*(1+n)):=op_alloc s _ _ _ _ one zero cursor size
  have copy:Executes n m (.op (.regular (.copy 140 320))) u v 1:=op_copy u _ _ _ (by simp [u,State.assign])
  let P:=fun i (v:State)=>v.reg 6=1 ∧ v.reg 64=(n:ℤ) ∧ v.reg 71=(a:ℤ) ∧ v.reg 139=(p:ℤ) ∧
    v.reg 75=(edge:ℤ) ∧ v.reg 140=(top:ℤ) ∧ v.reg 8=((top+n:ℕ):ℤ) ∧
    (∀q,v.heap q=rimStage s.heap a p edge n top i q) ∧ v.output=s.output ∧ v.closed=s.closed
  have start:P 0 (forSetup 141 323 64 v):=by
    refine ⟨one,size,active,point,edges,by simp [forSetup,v,State.assign],by simp [forSetup,v,u,State.assign],?_,rfl,rfl⟩
    intro q;change (if top ≤ q ∧ q<top+n then 0 else s.heap q)=_
    unfold rimStage;split_ifs <;> omega
  have step (i:ℕ) (hi:i<n) (v:State) (good:P i v) (idx:v.reg 141=(i:ℤ)) (_:v.reg 323=(n:ℤ)-1):
      ∃t k,Executes n m rimRow v t k ∧ k ≤ 175+n*(235+6*n) ∧ t.reg 141=v.reg 141 ∧ t.reg 323=v.reg 323 ∧
        P (i+1) (t.assign 141 (t.reg 141+1)):=by
    obtain ⟨v1,sz,ac,pts,ed,mask,free,heap,out,cl⟩:=good
    obtain ⟨t,k,ex,tm,wrote,ot,flag⟩:=rim_row n a p edge top i m v ⟨v1,sz,pts,ed,mask,idx⟩ ac pp ee hi
    have same:onRim v.heap a p edge n i ↔ onRim s.heap a p edge n i:=
      rim_congr (fun q less=>by rw [heap];simp [rimStage,less]) aa pp ee hi
    refine ⟨t,k,ex,tm,ex.preserves 141 (by decide),ex.preserves 323 (by decide),
      (ex.preserves 6 (by decide)).trans v1,(ex.preserves 64 (by decide)).trans sz,
      (ex.preserves 71 (by decide)).trans ac,(ex.preserves 139 (by decide)).trans pts,
      (ex.preserves 75 (by decide)).trans ed,(ex.preserves 140 (by decide)).trans mask,
      (ex.preserves 8 (by decide)).trans free,?_,ot.trans out,flag.trans cl⟩
    intro q;change t.heap q=_
    rw [wrote,same,heap q];exact rim_stage_step _ _ _ _ _ _ _ _ hi
  obtain ⟨t,k,ex,tm,_,_,_,_,_,mask,free,heap,out,flag⟩:=source_for (N:=n) (input:=m) 141 323 64 n
    (175+n*(235+6*n)) rimRow P (by decide) (by decide) v size start step
  let final:=t.assign 143 (top:ℤ)
  have ret:Executes n m (.op (.regular (.copy 143 140))) t final 1:=op_copy _ _ _ _ mask
  refine ⟨final,_,.seq alloc (.seq copy (.seq ex (.seq ret (.skip _)))),?_,by simp [final,State.assign],free,?_,?_,out,flag⟩
  · ring_nf at tm ⊢ <;> omega
  · intro i lt;change t.heap (top+i)=_
    rw [heap];have ins:¬(top+i<top ∨ top+n ≤ top+i):=by omega
    simp [rimStage,ins,lt]
  · intro q off;change t.heap q=_;rw [heap];simp [rimStage,off]
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem solution (n a p edge top:ℕ) (m:ℤ → ℤ) (s:Logical.State) (one:s.reg 6=1) (zero:s.reg 7=0)
    (size:s.reg 64=(n:ℤ)) (cursor:s.reg 8=(top:ℤ)) (active:s.reg 71=(a:ℤ))
    (point:s.reg 139=(p:ℤ)) (edges:s.reg 75=(edge:ℤ)) (aa:a+n ≤ top) (pp:p+n ≤ top) (ee:edge+n*n ≤ top):
    ∃t k,Logical.Executes n m src_rim s t k ∧ k ≤ 600*(n+1)^3 ∧ t.reg 143=(top:ℤ) ∧
      t.reg 8=((top+n:ℕ):ℤ) ∧ (∀i<n,t.heap (top+i)=if (1 ≤ s.heap (a+i) ∧ ¬1 ≤ s.heap (p+i)) ∧ (∃j<n,1 ≤ s.heap (p+j) ∧ 1 ≤ s.heap (edge+(j*n+i))) then 1 else 0) ∧
      (∀q,q<top ∨ top+n ≤ q → t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed := by
  obtain ⟨t,k,ex,tm,val,free,bits,frame,out,cl⟩:=Logical.rim_scan n a p edge top m s one zero size cursor active point edges aa pp ee
  refine ⟨t,k,ex,tm,val,free,?_,frame,out,cl⟩
  intro i hi;rw [bits i hi]
  by_cases hit:Logical.onRim s.heap a p edge n i
  · have g:((1 ≤ s.heap (a+i) ∧ ¬1 ≤ s.heap (p+i)) ∧ (∃j<n,1 ≤ s.heap (p+j) ∧ 1 ≤ s.heap (edge+(j*n+i)))):=hit
    simp only [if_pos hit,if_pos g]
  · have g:¬((1 ≤ s.heap (a+i) ∧ ¬1 ≤ s.heap (p+i)) ∧ (∃j<n,1 ≤ s.heap (p+j) ∧ 1 ≤ s.heap (edge+(j*n+i)))):=hit
    simp only [if_neg hit,if_neg g]
