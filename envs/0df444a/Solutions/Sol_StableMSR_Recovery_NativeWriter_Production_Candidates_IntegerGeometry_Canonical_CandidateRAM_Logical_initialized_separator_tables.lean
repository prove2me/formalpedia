-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.initialized_separator_tables
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:37:05.217795+00:00
-- url     : https://prove2.me/submissions/935ac362-a3b0-4ee5-be14-ad7895f2f003

import Definitions.Def_StableMSR_SeparatorArenaLayout
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
theorem small_regs (j:Fin 68) : j.val≠8 → writesReg j.val arena=false:=by
  have ok:∀i:Fin 68,i.val≠8 → writesReg i.val arena=false:=by decide
  exact ok j
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
/-- The enumeration tables occupy eleven contiguous, initially zero spans.
The scan that computes the label radix is part of this very prefix. -/
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
      zeroed s t (cursorAt layout 11) ∧ (∀j<68,j≠8 → t.reg j=s.reg j):=by
  let H:=h+1
  let rows:=n^(2*H)
  let M:=H*rows
  let layout:=offsets n M
  change ∃t z,Executes n input arena s t z ∧ z ≤ 4000*(h+2)*(n+1)^3*(M+1) ∧
    t.reg 68=(H:ℤ) ∧ t.reg 69=(rows:ℤ) ∧ t.reg 70=(M:ℤ) ∧ t.reg 82=0 ∧
    t.reg 8=(cursorAt layout 11:ℤ) ∧ (∀j:Fin 11,t.reg (71+j.val)=(cursorAt layout j.val:ℤ)) ∧
    zeroed s t (cursorAt layout 11) ∧ (∀j<68,j≠8 → t.reg j=s.reg j)
  let u1:=s.assign 1235 (1:ℤ)
  have e1:Executes n input (.op (.regular (.set 1235 1))) s u1 1:=
    op_set s 1235 (1:ℤ)
  have r1:u1.reg 1235=((1:ℕ):ℤ):=by simp [u1,State.assign]
  have z1:zeroed s u1 0:=zeroed_init s
  let u2:=u1.assign 1233 ((H:ℕ):ℤ)
  have e2:Executes n input (.op (.regular (.add 1233 66 1235))) u1 u2 1:=
    op_add u1 1233 66 1235 (h) (1) ((e1.preserves 66 (by decide)).trans budget) r1
  have r2:u2.reg 1233=((H:ℕ):ℤ):=by simp [u2,State.assign]
  have z2:zeroed s u2 0:=z1
  let u3:=u2.assign 68 ((H:ℕ):ℤ)
  have e3:Executes n input (.op (.regular (.copy 68 1233))) u2 u3 1:=
    op_copy u2 68 1233 ((H:ℕ):ℤ) r2
  have r3:u3.reg 68=((H:ℕ):ℤ):=by simp [u3,State.assign]
  have z3:zeroed s u3 0:=z2
  let u4:=u3.assign 1236 (1:ℤ)
  have e4:Executes n input (.op (.regular (.set 1236 1))) u3 u4 1:=
    op_set u3 1236 (1:ℤ)
  have r4:u4.reg 1236=((1:ℕ):ℤ):=by simp [u4,State.assign]
  have z4:zeroed s u4 0:=z3
  let u5:=u4.assign 69 ((1:ℕ):ℤ)
  have e5:Executes n input (.op (.regular (.copy 69 1236))) u4 u5 1:=
    op_copy u4 69 1236 ((1:ℕ):ℤ) r4
  have r5:u5.reg 69=((1:ℕ):ℤ):=by simp [u5,State.assign]
  have z5:zeroed s u5 0:=z4
  let u6:=u5.assign 1237 (((2*H):ℕ):ℤ)
  have e6:Executes n input (.op (.shift 1237 68 1)) u5 u6 5:=
    op_shift u5 1237 68 1 (H) ((e5.preserves 68 (by decide)).trans ((e4.preserves 68 (by decide)).trans r3))
  have r6:u6.reg 1237=(((2*H):ℕ):ℤ):=by simp [u6,State.assign]
  have z6:zeroed s u6 0:=z5
  obtain ⟨u7,zp,e7,powerTime,powerValue,powerHeap,powerOut,powerClosed,powerFrame⟩:=
    run_power (input:=input) n n (2*H) u6 ((e6.preserves 6 (by decide)).trans ((e5.preserves 6 (by decide)).trans ((e4.preserves 6 (by decide)).trans ((e3.preserves 6 (by decide)).trans ((e2.preserves 6 (by decide)).trans ((e1.preserves 6 (by decide)).trans one)))))) ((e6.preserves 64 (by decide)).trans ((e5.preserves 64 (by decide)).trans ((e4.preserves 64 (by decide)).trans ((e3.preserves 64 (by decide)).trans ((e2.preserves 64 (by decide)).trans ((e1.preserves 64 (by decide)).trans sz)))))) r6 ((e6.preserves 69 (by decide)).trans r5)

  have afterPower6:u7.reg 6=(1:ℕ):= (powerFrame 6 (by decide) (by decide) (by decide) (by decide)).trans ((e6.preserves 6 (by decide)).trans ((e5.preserves 6 (by decide)).trans ((e4.preserves 6 (by decide)).trans ((e3.preserves 6 (by decide)).trans ((e2.preserves 6 (by decide)).trans ((e1.preserves 6 (by decide)).trans one))))))
  have afterPower7:u7.reg 7=(0:ℕ):= (powerFrame 7 (by decide) (by decide) (by decide) (by decide)).trans ((e6.preserves 7 (by decide)).trans ((e5.preserves 7 (by decide)).trans ((e4.preserves 7 (by decide)).trans ((e3.preserves 7 (by decide)).trans ((e2.preserves 7 (by decide)).trans ((e1.preserves 7 (by decide)).trans zero))))))
  have afterPower8:u7.reg 8=(0:ℕ):= (powerFrame 8 (by decide) (by decide) (by decide) (by decide)).trans ((e6.preserves 8 (by decide)).trans ((e5.preserves 8 (by decide)).trans ((e4.preserves 8 (by decide)).trans ((e3.preserves 8 (by decide)).trans ((e2.preserves 8 (by decide)).trans ((e1.preserves 8 (by decide)).trans start))))))
  have afterPower64:u7.reg 64=(n:ℕ):= (powerFrame 64 (by decide) (by decide) (by decide) (by decide)).trans ((e6.preserves 64 (by decide)).trans ((e5.preserves 64 (by decide)).trans ((e4.preserves 64 (by decide)).trans ((e3.preserves 64 (by decide)).trans ((e2.preserves 64 (by decide)).trans ((e1.preserves 64 (by decide)).trans sz))))))
  have afterPower66:u7.reg 66=(h:ℕ):= (powerFrame 66 (by decide) (by decide) (by decide) (by decide)).trans ((e6.preserves 66 (by decide)).trans ((e5.preserves 66 (by decide)).trans ((e4.preserves 66 (by decide)).trans ((e3.preserves 66 (by decide)).trans ((e2.preserves 66 (by decide)).trans ((e1.preserves 66 (by decide)).trans budget))))))
  have afterPower68:u7.reg 68=(H:ℕ):= (powerFrame 68 (by decide) (by decide) (by decide) (by decide)).trans ((e6.preserves 68 (by decide)).trans ((e5.preserves 68 (by decide)).trans ((e4.preserves 68 (by decide)).trans r3)))
  have z7:zeroed s u7 0:=by
    simpa only [zeroed,powerHeap,powerOut,powerClosed] using (show zeroed s u6 0 from z6)
  let u8:=u7.assign 1243 ((M:ℕ):ℤ)
  have e8:Executes n input (.op (.multiply 1243 68 69)) u7 u8 (8+6*(rows)):=
    op_mul u7 1243 68 69 (H) (rows) afterPower6 afterPower68 powerValue
  have r8:u8.reg 1243=((M:ℕ):ℤ):=by simp [u8,State.assign]
  have z8:zeroed s u8 0:=z7
  let u9:=u8.assign 70 ((M:ℕ):ℤ)
  have e9:Executes n input (.op (.regular (.copy 70 1243))) u8 u9 1:=
    op_copy u8 70 1243 ((M:ℕ):ℤ) r8
  have r9:u9.reg 70=((M:ℕ):ℤ):=by simp [u9,State.assign]
  have z9:zeroed s u9 0:=z8
  let off1:ℕ:=0+(n)
  let u10:=((u9.clear 0 (n)).assign 1246 (0:ℤ)).assign 8 (off1:ℤ)
  have e10:Executes n input (.op (.alloc 1246 64)) u9 u10 (64*(1+(n))):=
    op_alloc u9 1246 64 0 (n) ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)) ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)) ((e9.preserves 8 (by decide)).trans ((e8.preserves 8 (by decide)).trans afterPower8)) ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64))
  have r10:u10.reg 1246=((0:ℕ):ℤ):=by simp [u10,State.assign]
  have top10:u10.reg 8=(off1:ℤ):=by simp [u10,State.assign]
  have z10:zeroed s u10 off1:=zeroed_expand z9 (n)
  let u11:=u10.assign 71 ((0:ℕ):ℤ)
  have e11:Executes n input (.op (.regular (.copy 71 1246))) u10 u11 1:=
    op_copy u10 71 1246 ((0:ℕ):ℤ) r10
  have r11:u11.reg 71=((0:ℕ):ℤ):=by simp [u11,State.assign]
  have z11:zeroed s u11 off1:=z10
  let off2:ℕ:=off1+(n)
  let u12:=((u11.clear off1 (n)).assign 1248 (off1:ℤ)).assign 8 (off2:ℤ)
  have e12:Executes n input (.op (.alloc 1248 64)) u11 u12 (64*(1+(n))):=
    op_alloc u11 1248 64 off1 (n) ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))) ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)))) ((e11.preserves 8 (by decide)).trans top10) ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64))))
  have r12:u12.reg 1248=((off1:ℕ):ℤ):=by simp [u12,State.assign]
  have top12:u12.reg 8=(off2:ℤ):=by simp [u12,State.assign]
  have z12:zeroed s u12 off2:=zeroed_expand z11 (n)
  let u13:=u12.assign 72 ((off1:ℕ):ℤ)
  have e13:Executes n input (.op (.regular (.copy 72 1248))) u12 u13 1:=
    op_copy u12 72 1248 ((off1:ℕ):ℤ) r12
  have r13:u13.reg 72=((off1:ℕ):ℤ):=by simp [u13,State.assign]
  have z13:zeroed s u13 off2:=z12
  let off3:ℕ:=off2+(n)
  let u14:=((u13.clear off2 (n)).assign 1250 (off2:ℤ)).assign 8 (off3:ℤ)
  have e14:Executes n input (.op (.alloc 1250 64)) u13 u14 (64*(1+(n))):=
    op_alloc u13 1250 64 off2 (n) ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))) ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)))))) ((e13.preserves 8 (by decide)).trans top12) ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64))))))
  have r14:u14.reg 1250=((off2:ℕ):ℤ):=by simp [u14,State.assign]
  have top14:u14.reg 8=(off3:ℤ):=by simp [u14,State.assign]
  have z14:zeroed s u14 off3:=zeroed_expand z13 (n)
  let u15:=u14.assign 73 ((off2:ℕ):ℤ)
  have e15:Executes n input (.op (.regular (.copy 73 1250))) u14 u15 1:=
    op_copy u14 73 1250 ((off2:ℕ):ℤ) r14
  have r15:u15.reg 73=((off2:ℕ):ℤ):=by simp [u15,State.assign]
  have z15:zeroed s u15 off3:=z14
  let u16:=u15.assign 1253 (((n*n):ℕ):ℤ)
  have e16:Executes n input (.op (.multiply 1253 64 64)) u15 u16 (8+6*(n)):=
    op_mul u15 1253 64 64 (n) (n) ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))) ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))) ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64))))))))
  have r16:u16.reg 1253=(((n*n):ℕ):ℤ):=by simp [u16,State.assign]
  have z16:zeroed s u16 off3:=z15
  let off4:ℕ:=off3+((n*n))
  let u17:=((u16.clear off3 ((n*n))).assign 1252 (off3:ℤ)).assign 8 (off4:ℤ)
  have e17:Executes n input (.op (.alloc 1252 1253)) u16 u17 (64*(1+((n*n)))):=
    op_alloc u16 1252 1253 off3 ((n*n)) ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6))))))))) ((e16.preserves 7 (by decide)).trans ((e15.preserves 7 (by decide)).trans ((e14.preserves 7 (by decide)).trans ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7))))))))) ((e16.preserves 8 (by decide)).trans ((e15.preserves 8 (by decide)).trans top14)) r16
  have r17:u17.reg 1252=((off3:ℕ):ℤ):=by simp [u17,State.assign]
  have top17:u17.reg 8=(off4:ℤ):=by simp [u17,State.assign]
  have z17:zeroed s u17 off4:=zeroed_expand z16 ((n*n))
  let u18:=u17.assign 74 ((off3:ℕ):ℤ)
  have e18:Executes n input (.op (.regular (.copy 74 1252))) u17 u18 1:=
    op_copy u17 74 1252 ((off3:ℕ):ℤ) r17
  have r18:u18.reg 74=((off3:ℕ):ℤ):=by simp [u18,State.assign]
  have z18:zeroed s u18 off4:=z17
  let u19:=u18.assign 1257 (((n*n):ℕ):ℤ)
  have e19:Executes n input (.op (.multiply 1257 64 64)) u18 u19 (8+6*(n)):=
    op_mul u18 1257 64 64 (n) (n) ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6))))))))))) ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64))))))))))) ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))
  have r19:u19.reg 1257=(((n*n):ℕ):ℤ):=by simp [u19,State.assign]
  have z19:zeroed s u19 off4:=z18
  let off5:ℕ:=off4+((n*n))
  let u20:=((u19.clear off4 ((n*n))).assign 1256 (off4:ℤ)).assign 8 (off5:ℤ)
  have e20:Executes n input (.op (.alloc 1256 1257)) u19 u20 (64*(1+((n*n)))):=
    op_alloc u19 1256 1257 off4 ((n*n)) ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))) ((e19.preserves 7 (by decide)).trans ((e18.preserves 7 (by decide)).trans ((e17.preserves 7 (by decide)).trans ((e16.preserves 7 (by decide)).trans ((e15.preserves 7 (by decide)).trans ((e14.preserves 7 (by decide)).trans ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)))))))))))) ((e19.preserves 8 (by decide)).trans ((e18.preserves 8 (by decide)).trans top17)) r19
  have r20:u20.reg 1256=((off4:ℕ):ℤ):=by simp [u20,State.assign]
  have top20:u20.reg 8=(off5:ℤ):=by simp [u20,State.assign]
  have z20:zeroed s u20 off5:=zeroed_expand z19 ((n*n))
  let u21:=u20.assign 75 ((off4:ℕ):ℤ)
  have e21:Executes n input (.op (.regular (.copy 75 1256))) u20 u21 1:=
    op_copy u20 75 1256 ((off4:ℕ):ℤ) r20
  have r21:u21.reg 75=((off4:ℕ):ℤ):=by simp [u21,State.assign]
  have z21:zeroed s u21 off5:=z20
  let off6:ℕ:=off5+(M)
  let u22:=((u21.clear off5 (M)).assign 1260 (off5:ℤ)).assign 8 (off6:ℤ)
  have e22:Executes n input (.op (.alloc 1260 70)) u21 u22 (64*(1+(M))):=
    op_alloc u21 1260 70 off5 (M) ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))) ((e21.preserves 7 (by decide)).trans ((e20.preserves 7 (by decide)).trans ((e19.preserves 7 (by decide)).trans ((e18.preserves 7 (by decide)).trans ((e17.preserves 7 (by decide)).trans ((e16.preserves 7 (by decide)).trans ((e15.preserves 7 (by decide)).trans ((e14.preserves 7 (by decide)).trans ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)))))))))))))) ((e21.preserves 8 (by decide)).trans top20) ((e21.preserves 70 (by decide)).trans ((e20.preserves 70 (by decide)).trans ((e19.preserves 70 (by decide)).trans ((e18.preserves 70 (by decide)).trans ((e17.preserves 70 (by decide)).trans ((e16.preserves 70 (by decide)).trans ((e15.preserves 70 (by decide)).trans ((e14.preserves 70 (by decide)).trans ((e13.preserves 70 (by decide)).trans ((e12.preserves 70 (by decide)).trans ((e11.preserves 70 (by decide)).trans ((e10.preserves 70 (by decide)).trans r9))))))))))))
  have r22:u22.reg 1260=((off5:ℕ):ℤ):=by simp [u22,State.assign]
  have top22:u22.reg 8=(off6:ℤ):=by simp [u22,State.assign]
  have z22:zeroed s u22 off6:=zeroed_expand z21 (M)
  let u23:=u22.assign 76 ((off5:ℕ):ℤ)
  have e23:Executes n input (.op (.regular (.copy 76 1260))) u22 u23 1:=
    op_copy u22 76 1260 ((off5:ℕ):ℤ) r22
  have r23:u23.reg 76=((off5:ℕ):ℤ):=by simp [u23,State.assign]
  have z23:zeroed s u23 off6:=z22
  let u24:=u23.assign 1264 (((n*M):ℕ):ℤ)
  have e24:Executes n input (.op (.multiply 1264 64 70)) u23 u24 (8+6*(M)):=
    op_mul u23 1264 64 70 (n) (M) ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))) ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))))))) ((e23.preserves 70 (by decide)).trans ((e22.preserves 70 (by decide)).trans ((e21.preserves 70 (by decide)).trans ((e20.preserves 70 (by decide)).trans ((e19.preserves 70 (by decide)).trans ((e18.preserves 70 (by decide)).trans ((e17.preserves 70 (by decide)).trans ((e16.preserves 70 (by decide)).trans ((e15.preserves 70 (by decide)).trans ((e14.preserves 70 (by decide)).trans ((e13.preserves 70 (by decide)).trans ((e12.preserves 70 (by decide)).trans ((e11.preserves 70 (by decide)).trans ((e10.preserves 70 (by decide)).trans r9))))))))))))))
  have r24:u24.reg 1264=(((n*M):ℕ):ℤ):=by simp [u24,State.assign]
  have z24:zeroed s u24 off6:=z23
  let u25:=u24.assign 1263 ((((n*M)*n):ℕ):ℤ)
  have e25:Executes n input (.op (.multiply 1263 1264 64)) u24 u25 (8+6*(n)):=
    op_mul u24 1263 1264 64 ((n*M)) (n) ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6))))))))))))))))) r24 ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))))))))
  have r25:u25.reg 1263=((((n*M)*n):ℕ):ℤ):=by simp [u25,State.assign]
  have z25:zeroed s u25 off6:=z24
  let off7:ℕ:=off6+(((n*M)*n))
  let u26:=((u25.clear off6 (((n*M)*n))).assign 1262 (off6:ℤ)).assign 8 (off7:ℤ)
  have e26:Executes n input (.op (.alloc 1262 1263)) u25 u26 (64*(1+(((n*M)*n)))):=
    op_alloc u25 1262 1263 off6 (((n*M)*n)) ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))))) ((e25.preserves 7 (by decide)).trans ((e24.preserves 7 (by decide)).trans ((e23.preserves 7 (by decide)).trans ((e22.preserves 7 (by decide)).trans ((e21.preserves 7 (by decide)).trans ((e20.preserves 7 (by decide)).trans ((e19.preserves 7 (by decide)).trans ((e18.preserves 7 (by decide)).trans ((e17.preserves 7 (by decide)).trans ((e16.preserves 7 (by decide)).trans ((e15.preserves 7 (by decide)).trans ((e14.preserves 7 (by decide)).trans ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)))))))))))))))))) ((e25.preserves 8 (by decide)).trans ((e24.preserves 8 (by decide)).trans ((e23.preserves 8 (by decide)).trans top22))) r25
  have r26:u26.reg 1262=((off6:ℕ):ℤ):=by simp [u26,State.assign]
  have top26:u26.reg 8=(off7:ℤ):=by simp [u26,State.assign]
  have z26:zeroed s u26 off7:=zeroed_expand z25 (((n*M)*n))
  let u27:=u26.assign 77 ((off6:ℕ):ℤ)
  have e27:Executes n input (.op (.regular (.copy 77 1262))) u26 u27 1:=
    op_copy u26 77 1262 ((off6:ℕ):ℤ) r26
  have r27:u27.reg 77=((off6:ℕ):ℤ):=by simp [u27,State.assign]
  have z27:zeroed s u27 off7:=z26
  let u28:=u27.assign 1270 (((n*M):ℕ):ℤ)
  have e28:Executes n input (.op (.multiply 1270 64 70)) u27 u28 (8+6*(M)):=
    op_mul u27 1270 64 70 (n) (M) ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))))))) ((e27.preserves 64 (by decide)).trans ((e26.preserves 64 (by decide)).trans ((e25.preserves 64 (by decide)).trans ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))))))))))) ((e27.preserves 70 (by decide)).trans ((e26.preserves 70 (by decide)).trans ((e25.preserves 70 (by decide)).trans ((e24.preserves 70 (by decide)).trans ((e23.preserves 70 (by decide)).trans ((e22.preserves 70 (by decide)).trans ((e21.preserves 70 (by decide)).trans ((e20.preserves 70 (by decide)).trans ((e19.preserves 70 (by decide)).trans ((e18.preserves 70 (by decide)).trans ((e17.preserves 70 (by decide)).trans ((e16.preserves 70 (by decide)).trans ((e15.preserves 70 (by decide)).trans ((e14.preserves 70 (by decide)).trans ((e13.preserves 70 (by decide)).trans ((e12.preserves 70 (by decide)).trans ((e11.preserves 70 (by decide)).trans ((e10.preserves 70 (by decide)).trans r9))))))))))))))))))
  have r28:u28.reg 1270=(((n*M):ℕ):ℤ):=by simp [u28,State.assign]
  have z28:zeroed s u28 off7:=z27
  let u29:=u28.assign 1269 ((((n*M)*n):ℕ):ℤ)
  have e29:Executes n input (.op (.multiply 1269 1270 64)) u28 u29 (8+6*(n)):=
    op_mul u28 1269 1270 64 ((n*M)) (n) ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6))))))))))))))))))))) r28 ((e28.preserves 64 (by decide)).trans ((e27.preserves 64 (by decide)).trans ((e26.preserves 64 (by decide)).trans ((e25.preserves 64 (by decide)).trans ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))))))))))))
  have r29:u29.reg 1269=((((n*M)*n):ℕ):ℤ):=by simp [u29,State.assign]
  have z29:zeroed s u29 off7:=z28
  let off8:ℕ:=off7+(((n*M)*n))
  let u30:=((u29.clear off7 (((n*M)*n))).assign 1268 (off7:ℤ)).assign 8 (off8:ℤ)
  have e30:Executes n input (.op (.alloc 1268 1269)) u29 u30 (64*(1+(((n*M)*n)))):=
    op_alloc u29 1268 1269 off7 (((n*M)*n)) ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))))))))) ((e29.preserves 7 (by decide)).trans ((e28.preserves 7 (by decide)).trans ((e27.preserves 7 (by decide)).trans ((e26.preserves 7 (by decide)).trans ((e25.preserves 7 (by decide)).trans ((e24.preserves 7 (by decide)).trans ((e23.preserves 7 (by decide)).trans ((e22.preserves 7 (by decide)).trans ((e21.preserves 7 (by decide)).trans ((e20.preserves 7 (by decide)).trans ((e19.preserves 7 (by decide)).trans ((e18.preserves 7 (by decide)).trans ((e17.preserves 7 (by decide)).trans ((e16.preserves 7 (by decide)).trans ((e15.preserves 7 (by decide)).trans ((e14.preserves 7 (by decide)).trans ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)))))))))))))))))))))) ((e29.preserves 8 (by decide)).trans ((e28.preserves 8 (by decide)).trans ((e27.preserves 8 (by decide)).trans top26))) r29
  have r30:u30.reg 1268=((off7:ℕ):ℤ):=by simp [u30,State.assign]
  have top30:u30.reg 8=(off8:ℤ):=by simp [u30,State.assign]
  have z30:zeroed s u30 off8:=zeroed_expand z29 (((n*M)*n))
  let u31:=u30.assign 78 ((off7:ℕ):ℤ)
  have e31:Executes n input (.op (.regular (.copy 78 1268))) u30 u31 1:=
    op_copy u30 78 1268 ((off7:ℕ):ℤ) r30
  have r31:u31.reg 78=((off7:ℕ):ℤ):=by simp [u31,State.assign]
  have z31:zeroed s u31 off8:=z30
  let u32:=u31.assign 1276 (((n*M):ℕ):ℤ)
  have e32:Executes n input (.op (.multiply 1276 64 70)) u31 u32 (8+6*(M)):=
    op_mul u31 1276 64 70 (n) (M) ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))))))))))) ((e31.preserves 64 (by decide)).trans ((e30.preserves 64 (by decide)).trans ((e29.preserves 64 (by decide)).trans ((e28.preserves 64 (by decide)).trans ((e27.preserves 64 (by decide)).trans ((e26.preserves 64 (by decide)).trans ((e25.preserves 64 (by decide)).trans ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))))))))))))))) ((e31.preserves 70 (by decide)).trans ((e30.preserves 70 (by decide)).trans ((e29.preserves 70 (by decide)).trans ((e28.preserves 70 (by decide)).trans ((e27.preserves 70 (by decide)).trans ((e26.preserves 70 (by decide)).trans ((e25.preserves 70 (by decide)).trans ((e24.preserves 70 (by decide)).trans ((e23.preserves 70 (by decide)).trans ((e22.preserves 70 (by decide)).trans ((e21.preserves 70 (by decide)).trans ((e20.preserves 70 (by decide)).trans ((e19.preserves 70 (by decide)).trans ((e18.preserves 70 (by decide)).trans ((e17.preserves 70 (by decide)).trans ((e16.preserves 70 (by decide)).trans ((e15.preserves 70 (by decide)).trans ((e14.preserves 70 (by decide)).trans ((e13.preserves 70 (by decide)).trans ((e12.preserves 70 (by decide)).trans ((e11.preserves 70 (by decide)).trans ((e10.preserves 70 (by decide)).trans r9))))))))))))))))))))))
  have r32:u32.reg 1276=(((n*M):ℕ):ℤ):=by simp [u32,State.assign]
  have z32:zeroed s u32 off8:=z31
  let u33:=u32.assign 1275 ((((n*M)*n):ℕ):ℤ)
  have e33:Executes n input (.op (.multiply 1275 1276 64)) u32 u33 (8+6*(n)):=
    op_mul u32 1275 1276 64 ((n*M)) (n) ((e32.preserves 6 (by decide)).trans ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6))))))))))))))))))))))))) r32 ((e32.preserves 64 (by decide)).trans ((e31.preserves 64 (by decide)).trans ((e30.preserves 64 (by decide)).trans ((e29.preserves 64 (by decide)).trans ((e28.preserves 64 (by decide)).trans ((e27.preserves 64 (by decide)).trans ((e26.preserves 64 (by decide)).trans ((e25.preserves 64 (by decide)).trans ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))))))))))))))))
  have r33:u33.reg 1275=((((n*M)*n):ℕ):ℤ):=by simp [u33,State.assign]
  have z33:zeroed s u33 off8:=z32
  let off9:ℕ:=off8+(((n*M)*n))
  let u34:=((u33.clear off8 (((n*M)*n))).assign 1274 (off8:ℤ)).assign 8 (off9:ℤ)
  have e34:Executes n input (.op (.alloc 1274 1275)) u33 u34 (64*(1+(((n*M)*n)))):=
    op_alloc u33 1274 1275 off8 (((n*M)*n)) ((e33.preserves 6 (by decide)).trans ((e32.preserves 6 (by decide)).trans ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))))))))))))) ((e33.preserves 7 (by decide)).trans ((e32.preserves 7 (by decide)).trans ((e31.preserves 7 (by decide)).trans ((e30.preserves 7 (by decide)).trans ((e29.preserves 7 (by decide)).trans ((e28.preserves 7 (by decide)).trans ((e27.preserves 7 (by decide)).trans ((e26.preserves 7 (by decide)).trans ((e25.preserves 7 (by decide)).trans ((e24.preserves 7 (by decide)).trans ((e23.preserves 7 (by decide)).trans ((e22.preserves 7 (by decide)).trans ((e21.preserves 7 (by decide)).trans ((e20.preserves 7 (by decide)).trans ((e19.preserves 7 (by decide)).trans ((e18.preserves 7 (by decide)).trans ((e17.preserves 7 (by decide)).trans ((e16.preserves 7 (by decide)).trans ((e15.preserves 7 (by decide)).trans ((e14.preserves 7 (by decide)).trans ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)))))))))))))))))))))))))) ((e33.preserves 8 (by decide)).trans ((e32.preserves 8 (by decide)).trans ((e31.preserves 8 (by decide)).trans top30))) r33
  have r34:u34.reg 1274=((off8:ℕ):ℤ):=by simp [u34,State.assign]
  have top34:u34.reg 8=(off9:ℤ):=by simp [u34,State.assign]
  have z34:zeroed s u34 off9:=zeroed_expand z33 (((n*M)*n))
  let u35:=u34.assign 79 ((off8:ℕ):ℤ)
  have e35:Executes n input (.op (.regular (.copy 79 1274))) u34 u35 1:=
    op_copy u34 79 1274 ((off8:ℕ):ℤ) r34
  have r35:u35.reg 79=((off8:ℕ):ℤ):=by simp [u35,State.assign]
  have z35:zeroed s u35 off9:=z34
  let u36:=u35.assign 1283 (((n*M):ℕ):ℤ)
  have e36:Executes n input (.op (.multiply 1283 64 70)) u35 u36 (8+6*(M)):=
    op_mul u35 1283 64 70 (n) (M) ((e35.preserves 6 (by decide)).trans ((e34.preserves 6 (by decide)).trans ((e33.preserves 6 (by decide)).trans ((e32.preserves 6 (by decide)).trans ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))))))))))))))) ((e35.preserves 64 (by decide)).trans ((e34.preserves 64 (by decide)).trans ((e33.preserves 64 (by decide)).trans ((e32.preserves 64 (by decide)).trans ((e31.preserves 64 (by decide)).trans ((e30.preserves 64 (by decide)).trans ((e29.preserves 64 (by decide)).trans ((e28.preserves 64 (by decide)).trans ((e27.preserves 64 (by decide)).trans ((e26.preserves 64 (by decide)).trans ((e25.preserves 64 (by decide)).trans ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))))))))))))))))))) ((e35.preserves 70 (by decide)).trans ((e34.preserves 70 (by decide)).trans ((e33.preserves 70 (by decide)).trans ((e32.preserves 70 (by decide)).trans ((e31.preserves 70 (by decide)).trans ((e30.preserves 70 (by decide)).trans ((e29.preserves 70 (by decide)).trans ((e28.preserves 70 (by decide)).trans ((e27.preserves 70 (by decide)).trans ((e26.preserves 70 (by decide)).trans ((e25.preserves 70 (by decide)).trans ((e24.preserves 70 (by decide)).trans ((e23.preserves 70 (by decide)).trans ((e22.preserves 70 (by decide)).trans ((e21.preserves 70 (by decide)).trans ((e20.preserves 70 (by decide)).trans ((e19.preserves 70 (by decide)).trans ((e18.preserves 70 (by decide)).trans ((e17.preserves 70 (by decide)).trans ((e16.preserves 70 (by decide)).trans ((e15.preserves 70 (by decide)).trans ((e14.preserves 70 (by decide)).trans ((e13.preserves 70 (by decide)).trans ((e12.preserves 70 (by decide)).trans ((e11.preserves 70 (by decide)).trans ((e10.preserves 70 (by decide)).trans r9))))))))))))))))))))))))))
  have r36:u36.reg 1283=(((n*M):ℕ):ℤ):=by simp [u36,State.assign]
  have z36:zeroed s u36 off9:=z35
  let u37:=u36.assign 1282 ((((n*M)*n):ℕ):ℤ)
  have e37:Executes n input (.op (.multiply 1282 1283 64)) u36 u37 (8+6*(n)):=
    op_mul u36 1282 1283 64 ((n*M)) (n) ((e36.preserves 6 (by decide)).trans ((e35.preserves 6 (by decide)).trans ((e34.preserves 6 (by decide)).trans ((e33.preserves 6 (by decide)).trans ((e32.preserves 6 (by decide)).trans ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6))))))))))))))))))))))))))))) r36 ((e36.preserves 64 (by decide)).trans ((e35.preserves 64 (by decide)).trans ((e34.preserves 64 (by decide)).trans ((e33.preserves 64 (by decide)).trans ((e32.preserves 64 (by decide)).trans ((e31.preserves 64 (by decide)).trans ((e30.preserves 64 (by decide)).trans ((e29.preserves 64 (by decide)).trans ((e28.preserves 64 (by decide)).trans ((e27.preserves 64 (by decide)).trans ((e26.preserves 64 (by decide)).trans ((e25.preserves 64 (by decide)).trans ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64)))))))))))))))))))))))))))))
  have r37:u37.reg 1282=((((n*M)*n):ℕ):ℤ):=by simp [u37,State.assign]
  have z37:zeroed s u37 off9:=z36
  let u38:=u37.assign 1281 (((((n*M)*n)*n):ℕ):ℤ)
  have e38:Executes n input (.op (.multiply 1281 1282 64)) u37 u38 (8+6*(n)):=
    op_mul u37 1281 1282 64 (((n*M)*n)) (n) ((e37.preserves 6 (by decide)).trans ((e36.preserves 6 (by decide)).trans ((e35.preserves 6 (by decide)).trans ((e34.preserves 6 (by decide)).trans ((e33.preserves 6 (by decide)).trans ((e32.preserves 6 (by decide)).trans ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))))))))))))))))) r37 ((e37.preserves 64 (by decide)).trans ((e36.preserves 64 (by decide)).trans ((e35.preserves 64 (by decide)).trans ((e34.preserves 64 (by decide)).trans ((e33.preserves 64 (by decide)).trans ((e32.preserves 64 (by decide)).trans ((e31.preserves 64 (by decide)).trans ((e30.preserves 64 (by decide)).trans ((e29.preserves 64 (by decide)).trans ((e28.preserves 64 (by decide)).trans ((e27.preserves 64 (by decide)).trans ((e26.preserves 64 (by decide)).trans ((e25.preserves 64 (by decide)).trans ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64))))))))))))))))))))))))))))))
  have r38:u38.reg 1281=(((((n*M)*n)*n):ℕ):ℤ):=by simp [u38,State.assign]
  have z38:zeroed s u38 off9:=z37
  let off10:ℕ:=off9+((((n*M)*n)*n))
  let u39:=((u38.clear off9 ((((n*M)*n)*n))).assign 1280 (off9:ℤ)).assign 8 (off10:ℤ)
  have e39:Executes n input (.op (.alloc 1280 1281)) u38 u39 (64*(1+((((n*M)*n)*n)))):=
    op_alloc u38 1280 1281 off9 ((((n*M)*n)*n)) ((e38.preserves 6 (by decide)).trans ((e37.preserves 6 (by decide)).trans ((e36.preserves 6 (by decide)).trans ((e35.preserves 6 (by decide)).trans ((e34.preserves 6 (by decide)).trans ((e33.preserves 6 (by decide)).trans ((e32.preserves 6 (by decide)).trans ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6))))))))))))))))))))))))))))))) ((e38.preserves 7 (by decide)).trans ((e37.preserves 7 (by decide)).trans ((e36.preserves 7 (by decide)).trans ((e35.preserves 7 (by decide)).trans ((e34.preserves 7 (by decide)).trans ((e33.preserves 7 (by decide)).trans ((e32.preserves 7 (by decide)).trans ((e31.preserves 7 (by decide)).trans ((e30.preserves 7 (by decide)).trans ((e29.preserves 7 (by decide)).trans ((e28.preserves 7 (by decide)).trans ((e27.preserves 7 (by decide)).trans ((e26.preserves 7 (by decide)).trans ((e25.preserves 7 (by decide)).trans ((e24.preserves 7 (by decide)).trans ((e23.preserves 7 (by decide)).trans ((e22.preserves 7 (by decide)).trans ((e21.preserves 7 (by decide)).trans ((e20.preserves 7 (by decide)).trans ((e19.preserves 7 (by decide)).trans ((e18.preserves 7 (by decide)).trans ((e17.preserves 7 (by decide)).trans ((e16.preserves 7 (by decide)).trans ((e15.preserves 7 (by decide)).trans ((e14.preserves 7 (by decide)).trans ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7))))))))))))))))))))))))))))))) ((e38.preserves 8 (by decide)).trans ((e37.preserves 8 (by decide)).trans ((e36.preserves 8 (by decide)).trans ((e35.preserves 8 (by decide)).trans top34)))) r38
  have r39:u39.reg 1280=((off9:ℕ):ℤ):=by simp [u39,State.assign]
  have top39:u39.reg 8=(off10:ℤ):=by simp [u39,State.assign]
  have z39:zeroed s u39 off10:=zeroed_expand z38 ((((n*M)*n)*n))
  let u40:=u39.assign 80 ((off9:ℕ):ℤ)
  have e40:Executes n input (.op (.regular (.copy 80 1280))) u39 u40 1:=
    op_copy u39 80 1280 ((off9:ℕ):ℤ) r39
  have r40:u40.reg 80=((off9:ℕ):ℤ):=by simp [u40,State.assign]
  have z40:zeroed s u40 off10:=z39
  let u41:=u40.assign 1289 (((n*M):ℕ):ℤ)
  have e41:Executes n input (.op (.multiply 1289 64 70)) u40 u41 (8+6*(M)):=
    op_mul u40 1289 64 70 (n) (M) ((e40.preserves 6 (by decide)).trans ((e39.preserves 6 (by decide)).trans ((e38.preserves 6 (by decide)).trans ((e37.preserves 6 (by decide)).trans ((e36.preserves 6 (by decide)).trans ((e35.preserves 6 (by decide)).trans ((e34.preserves 6 (by decide)).trans ((e33.preserves 6 (by decide)).trans ((e32.preserves 6 (by decide)).trans ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6))))))))))))))))))))))))))))))))) ((e40.preserves 64 (by decide)).trans ((e39.preserves 64 (by decide)).trans ((e38.preserves 64 (by decide)).trans ((e37.preserves 64 (by decide)).trans ((e36.preserves 64 (by decide)).trans ((e35.preserves 64 (by decide)).trans ((e34.preserves 64 (by decide)).trans ((e33.preserves 64 (by decide)).trans ((e32.preserves 64 (by decide)).trans ((e31.preserves 64 (by decide)).trans ((e30.preserves 64 (by decide)).trans ((e29.preserves 64 (by decide)).trans ((e28.preserves 64 (by decide)).trans ((e27.preserves 64 (by decide)).trans ((e26.preserves 64 (by decide)).trans ((e25.preserves 64 (by decide)).trans ((e24.preserves 64 (by decide)).trans ((e23.preserves 64 (by decide)).trans ((e22.preserves 64 (by decide)).trans ((e21.preserves 64 (by decide)).trans ((e20.preserves 64 (by decide)).trans ((e19.preserves 64 (by decide)).trans ((e18.preserves 64 (by decide)).trans ((e17.preserves 64 (by decide)).trans ((e16.preserves 64 (by decide)).trans ((e15.preserves 64 (by decide)).trans ((e14.preserves 64 (by decide)).trans ((e13.preserves 64 (by decide)).trans ((e12.preserves 64 (by decide)).trans ((e11.preserves 64 (by decide)).trans ((e10.preserves 64 (by decide)).trans ((e9.preserves 64 (by decide)).trans ((e8.preserves 64 (by decide)).trans afterPower64))))))))))))))))))))))))))))))))) ((e40.preserves 70 (by decide)).trans ((e39.preserves 70 (by decide)).trans ((e38.preserves 70 (by decide)).trans ((e37.preserves 70 (by decide)).trans ((e36.preserves 70 (by decide)).trans ((e35.preserves 70 (by decide)).trans ((e34.preserves 70 (by decide)).trans ((e33.preserves 70 (by decide)).trans ((e32.preserves 70 (by decide)).trans ((e31.preserves 70 (by decide)).trans ((e30.preserves 70 (by decide)).trans ((e29.preserves 70 (by decide)).trans ((e28.preserves 70 (by decide)).trans ((e27.preserves 70 (by decide)).trans ((e26.preserves 70 (by decide)).trans ((e25.preserves 70 (by decide)).trans ((e24.preserves 70 (by decide)).trans ((e23.preserves 70 (by decide)).trans ((e22.preserves 70 (by decide)).trans ((e21.preserves 70 (by decide)).trans ((e20.preserves 70 (by decide)).trans ((e19.preserves 70 (by decide)).trans ((e18.preserves 70 (by decide)).trans ((e17.preserves 70 (by decide)).trans ((e16.preserves 70 (by decide)).trans ((e15.preserves 70 (by decide)).trans ((e14.preserves 70 (by decide)).trans ((e13.preserves 70 (by decide)).trans ((e12.preserves 70 (by decide)).trans ((e11.preserves 70 (by decide)).trans ((e10.preserves 70 (by decide)).trans r9)))))))))))))))))))))))))))))))
  have r41:u41.reg 1289=(((n*M):ℕ):ℤ):=by simp [u41,State.assign]
  have z41:zeroed s u41 off10:=z40
  let off11:ℕ:=off10+((n*M))
  let u42:=((u41.clear off10 ((n*M))).assign 1288 (off10:ℤ)).assign 8 (off11:ℤ)
  have e42:Executes n input (.op (.alloc 1288 1289)) u41 u42 (64*(1+((n*M)))):=
    op_alloc u41 1288 1289 off10 ((n*M)) ((e41.preserves 6 (by decide)).trans ((e40.preserves 6 (by decide)).trans ((e39.preserves 6 (by decide)).trans ((e38.preserves 6 (by decide)).trans ((e37.preserves 6 (by decide)).trans ((e36.preserves 6 (by decide)).trans ((e35.preserves 6 (by decide)).trans ((e34.preserves 6 (by decide)).trans ((e33.preserves 6 (by decide)).trans ((e32.preserves 6 (by decide)).trans ((e31.preserves 6 (by decide)).trans ((e30.preserves 6 (by decide)).trans ((e29.preserves 6 (by decide)).trans ((e28.preserves 6 (by decide)).trans ((e27.preserves 6 (by decide)).trans ((e26.preserves 6 (by decide)).trans ((e25.preserves 6 (by decide)).trans ((e24.preserves 6 (by decide)).trans ((e23.preserves 6 (by decide)).trans ((e22.preserves 6 (by decide)).trans ((e21.preserves 6 (by decide)).trans ((e20.preserves 6 (by decide)).trans ((e19.preserves 6 (by decide)).trans ((e18.preserves 6 (by decide)).trans ((e17.preserves 6 (by decide)).trans ((e16.preserves 6 (by decide)).trans ((e15.preserves 6 (by decide)).trans ((e14.preserves 6 (by decide)).trans ((e13.preserves 6 (by decide)).trans ((e12.preserves 6 (by decide)).trans ((e11.preserves 6 (by decide)).trans ((e10.preserves 6 (by decide)).trans ((e9.preserves 6 (by decide)).trans ((e8.preserves 6 (by decide)).trans afterPower6)))))))))))))))))))))))))))))))))) ((e41.preserves 7 (by decide)).trans ((e40.preserves 7 (by decide)).trans ((e39.preserves 7 (by decide)).trans ((e38.preserves 7 (by decide)).trans ((e37.preserves 7 (by decide)).trans ((e36.preserves 7 (by decide)).trans ((e35.preserves 7 (by decide)).trans ((e34.preserves 7 (by decide)).trans ((e33.preserves 7 (by decide)).trans ((e32.preserves 7 (by decide)).trans ((e31.preserves 7 (by decide)).trans ((e30.preserves 7 (by decide)).trans ((e29.preserves 7 (by decide)).trans ((e28.preserves 7 (by decide)).trans ((e27.preserves 7 (by decide)).trans ((e26.preserves 7 (by decide)).trans ((e25.preserves 7 (by decide)).trans ((e24.preserves 7 (by decide)).trans ((e23.preserves 7 (by decide)).trans ((e22.preserves 7 (by decide)).trans ((e21.preserves 7 (by decide)).trans ((e20.preserves 7 (by decide)).trans ((e19.preserves 7 (by decide)).trans ((e18.preserves 7 (by decide)).trans ((e17.preserves 7 (by decide)).trans ((e16.preserves 7 (by decide)).trans ((e15.preserves 7 (by decide)).trans ((e14.preserves 7 (by decide)).trans ((e13.preserves 7 (by decide)).trans ((e12.preserves 7 (by decide)).trans ((e11.preserves 7 (by decide)).trans ((e10.preserves 7 (by decide)).trans ((e9.preserves 7 (by decide)).trans ((e8.preserves 7 (by decide)).trans afterPower7)))))))))))))))))))))))))))))))))) ((e41.preserves 8 (by decide)).trans ((e40.preserves 8 (by decide)).trans top39)) r41
  have r42:u42.reg 1288=((off10:ℕ):ℤ):=by simp [u42,State.assign]
  have top42:u42.reg 8=(off11:ℤ):=by simp [u42,State.assign]
  have z42:zeroed s u42 off11:=zeroed_expand z41 ((n*M))
  let u43:=u42.assign 81 ((off10:ℕ):ℤ)
  have e43:Executes n input (.op (.regular (.copy 81 1288))) u42 u43 1:=
    op_copy u42 81 1288 ((off10:ℕ):ℤ) r42
  have r43:u43.reg 81=((off10:ℕ):ℤ):=by simp [u43,State.assign]
  have z43:zeroed s u43 off11:=z42
  let u44:=u43.assign 1292 (0:ℤ)
  have e44:Executes n input (.op (.regular (.set 1292 0))) u43 u44 1:=
    op_set u43 1292 (0:ℤ)
  have r44:u44.reg 1292=((0:ℕ):ℤ):=by simp [u44,State.assign]
  have z44:zeroed s u44 off11:=z43
  let u45:=u44.assign 82 ((0:ℕ):ℤ)
  have e45:Executes n input (.op (.regular (.copy 82 1292))) u44 u45 1:=
    op_copy u44 82 1292 ((0:ℕ):ℤ) r44
  have r45:u45.reg 82=((0:ℕ):ℤ):=by simp [u45,State.assign]
  have z45:zeroed s u45 off11:=z44
  have seg:PrefixRun n input ((listOf src_generate).take 45) s u45 _:=
    .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9 (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17 (.cons e18 (.cons e19 (.cons e20 (.cons e21 (.cons e22 (.cons e23 (.cons e24 (.cons e25 (.cons e26 (.cons e27 (.cons e28 (.cons e29 (.cons e30 (.cons e31 (.cons e32 (.cons e33 (.cons e34 (.cons e35 (.cons e36 (.cons e37 (.cons e38 (.cons e39 (.cons e40 (.cons e41 (.cons e42 (.cons e43 (.cons e44 (.cons e45 (.nil _)))))))))))))))))))))))))))))))))))))))))))))
  refine ⟨u45,_,seg.finish,?_,((e45.preserves 68 (by decide)).trans ((e44.preserves 68 (by decide)).trans ((e43.preserves 68 (by decide)).trans ((e42.preserves 68 (by decide)).trans ((e41.preserves 68 (by decide)).trans ((e40.preserves 68 (by decide)).trans ((e39.preserves 68 (by decide)).trans ((e38.preserves 68 (by decide)).trans ((e37.preserves 68 (by decide)).trans ((e36.preserves 68 (by decide)).trans ((e35.preserves 68 (by decide)).trans ((e34.preserves 68 (by decide)).trans ((e33.preserves 68 (by decide)).trans ((e32.preserves 68 (by decide)).trans ((e31.preserves 68 (by decide)).trans ((e30.preserves 68 (by decide)).trans ((e29.preserves 68 (by decide)).trans ((e28.preserves 68 (by decide)).trans ((e27.preserves 68 (by decide)).trans ((e26.preserves 68 (by decide)).trans ((e25.preserves 68 (by decide)).trans ((e24.preserves 68 (by decide)).trans ((e23.preserves 68 (by decide)).trans ((e22.preserves 68 (by decide)).trans ((e21.preserves 68 (by decide)).trans ((e20.preserves 68 (by decide)).trans ((e19.preserves 68 (by decide)).trans ((e18.preserves 68 (by decide)).trans ((e17.preserves 68 (by decide)).trans ((e16.preserves 68 (by decide)).trans ((e15.preserves 68 (by decide)).trans ((e14.preserves 68 (by decide)).trans ((e13.preserves 68 (by decide)).trans ((e12.preserves 68 (by decide)).trans ((e11.preserves 68 (by decide)).trans ((e10.preserves 68 (by decide)).trans ((e9.preserves 68 (by decide)).trans ((e8.preserves 68 (by decide)).trans afterPower68)))))))))))))))))))))))))))))))))))))),((e45.preserves 69 (by decide)).trans ((e44.preserves 69 (by decide)).trans ((e43.preserves 69 (by decide)).trans ((e42.preserves 69 (by decide)).trans ((e41.preserves 69 (by decide)).trans ((e40.preserves 69 (by decide)).trans ((e39.preserves 69 (by decide)).trans ((e38.preserves 69 (by decide)).trans ((e37.preserves 69 (by decide)).trans ((e36.preserves 69 (by decide)).trans ((e35.preserves 69 (by decide)).trans ((e34.preserves 69 (by decide)).trans ((e33.preserves 69 (by decide)).trans ((e32.preserves 69 (by decide)).trans ((e31.preserves 69 (by decide)).trans ((e30.preserves 69 (by decide)).trans ((e29.preserves 69 (by decide)).trans ((e28.preserves 69 (by decide)).trans ((e27.preserves 69 (by decide)).trans ((e26.preserves 69 (by decide)).trans ((e25.preserves 69 (by decide)).trans ((e24.preserves 69 (by decide)).trans ((e23.preserves 69 (by decide)).trans ((e22.preserves 69 (by decide)).trans ((e21.preserves 69 (by decide)).trans ((e20.preserves 69 (by decide)).trans ((e19.preserves 69 (by decide)).trans ((e18.preserves 69 (by decide)).trans ((e17.preserves 69 (by decide)).trans ((e16.preserves 69 (by decide)).trans ((e15.preserves 69 (by decide)).trans ((e14.preserves 69 (by decide)).trans ((e13.preserves 69 (by decide)).trans ((e12.preserves 69 (by decide)).trans ((e11.preserves 69 (by decide)).trans ((e10.preserves 69 (by decide)).trans ((e9.preserves 69 (by decide)).trans ((e8.preserves 69 (by decide)).trans powerValue)))))))))))))))))))))))))))))))))))))),((e45.preserves 70 (by decide)).trans ((e44.preserves 70 (by decide)).trans ((e43.preserves 70 (by decide)).trans ((e42.preserves 70 (by decide)).trans ((e41.preserves 70 (by decide)).trans ((e40.preserves 70 (by decide)).trans ((e39.preserves 70 (by decide)).trans ((e38.preserves 70 (by decide)).trans ((e37.preserves 70 (by decide)).trans ((e36.preserves 70 (by decide)).trans ((e35.preserves 70 (by decide)).trans ((e34.preserves 70 (by decide)).trans ((e33.preserves 70 (by decide)).trans ((e32.preserves 70 (by decide)).trans ((e31.preserves 70 (by decide)).trans ((e30.preserves 70 (by decide)).trans ((e29.preserves 70 (by decide)).trans ((e28.preserves 70 (by decide)).trans ((e27.preserves 70 (by decide)).trans ((e26.preserves 70 (by decide)).trans ((e25.preserves 70 (by decide)).trans ((e24.preserves 70 (by decide)).trans ((e23.preserves 70 (by decide)).trans ((e22.preserves 70 (by decide)).trans ((e21.preserves 70 (by decide)).trans ((e20.preserves 70 (by decide)).trans ((e19.preserves 70 (by decide)).trans ((e18.preserves 70 (by decide)).trans ((e17.preserves 70 (by decide)).trans ((e16.preserves 70 (by decide)).trans ((e15.preserves 70 (by decide)).trans ((e14.preserves 70 (by decide)).trans ((e13.preserves 70 (by decide)).trans ((e12.preserves 70 (by decide)).trans ((e11.preserves 70 (by decide)).trans ((e10.preserves 70 (by decide)).trans r9)))))))))))))))))))))))))))))))))))),r45,?_,?_,?_,?_⟩
  · change (1+1+(1+1+(1+1+(1+1+(1+1+(1+5+(1+zp+(1+(8+6*(rows))+(1+1+(1+(64*(1+(n)))+(1+1+(1+(64*(1+(n)))+(1+1+(1+(64*(1+(n)))+(1+1+(1+(8+6*(n))+(1+(64*(1+((n*n))))+(1+1+(1+(8+6*(n))+(1+(64*(1+((n*n))))+(1+1+(1+(64*(1+(M)))+(1+1+(1+(8+6*(M))+(1+(8+6*(n))+(1+(64*(1+(((n*M)*n))))+(1+1+(1+(8+6*(M))+(1+(8+6*(n))+(1+(64*(1+(((n*M)*n))))+(1+1+(1+(8+6*(M))+(1+(8+6*(n))+(1+(64*(1+(((n*M)*n))))+(1+1+(1+(8+6*(M))+(1+(8+6*(n))+(1+(8+6*(n))+(1+(64*(1+((((n*M)*n)*n))))+(1+1+(1+(8+6*(M))+(1+(64*(1+((n*M))))+(1+1+(1+1+(1+1+0)))))))))))))))))))))))))))))))))))))))))))))+1 ≤ _
    dsimp only [M,rows,H] at powerTime ⊢
    ring_nf at powerTime ⊢ <;> omega
  · have atEnd:u45.reg 8=(off11:ℤ):=((e45.preserves 8 (by decide)).trans ((e44.preserves 8 (by decide)).trans ((e43.preserves 8 (by decide)).trans top42)))
    have ofE:cursorAt layout 11=off11:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
    rw [ofE];exact atEnd
  · intro j;fin_cases j
    · change u45.reg 71=(cursorAt layout 0:ℤ)
      have ptr:cursorAt layout 0=0:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 71 (by decide)).trans ((e44.preserves 71 (by decide)).trans ((e43.preserves 71 (by decide)).trans ((e42.preserves 71 (by decide)).trans ((e41.preserves 71 (by decide)).trans ((e40.preserves 71 (by decide)).trans ((e39.preserves 71 (by decide)).trans ((e38.preserves 71 (by decide)).trans ((e37.preserves 71 (by decide)).trans ((e36.preserves 71 (by decide)).trans ((e35.preserves 71 (by decide)).trans ((e34.preserves 71 (by decide)).trans ((e33.preserves 71 (by decide)).trans ((e32.preserves 71 (by decide)).trans ((e31.preserves 71 (by decide)).trans ((e30.preserves 71 (by decide)).trans ((e29.preserves 71 (by decide)).trans ((e28.preserves 71 (by decide)).trans ((e27.preserves 71 (by decide)).trans ((e26.preserves 71 (by decide)).trans ((e25.preserves 71 (by decide)).trans ((e24.preserves 71 (by decide)).trans ((e23.preserves 71 (by decide)).trans ((e22.preserves 71 (by decide)).trans ((e21.preserves 71 (by decide)).trans ((e20.preserves 71 (by decide)).trans ((e19.preserves 71 (by decide)).trans ((e18.preserves 71 (by decide)).trans ((e17.preserves 71 (by decide)).trans ((e16.preserves 71 (by decide)).trans ((e15.preserves 71 (by decide)).trans ((e14.preserves 71 (by decide)).trans ((e13.preserves 71 (by decide)).trans ((e12.preserves 71 (by decide)).trans r11))))))))))))))))))))))))))))))))))
    · change u45.reg 72=(cursorAt layout 1:ℤ)
      have ptr:cursorAt layout 1=off1:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 72 (by decide)).trans ((e44.preserves 72 (by decide)).trans ((e43.preserves 72 (by decide)).trans ((e42.preserves 72 (by decide)).trans ((e41.preserves 72 (by decide)).trans ((e40.preserves 72 (by decide)).trans ((e39.preserves 72 (by decide)).trans ((e38.preserves 72 (by decide)).trans ((e37.preserves 72 (by decide)).trans ((e36.preserves 72 (by decide)).trans ((e35.preserves 72 (by decide)).trans ((e34.preserves 72 (by decide)).trans ((e33.preserves 72 (by decide)).trans ((e32.preserves 72 (by decide)).trans ((e31.preserves 72 (by decide)).trans ((e30.preserves 72 (by decide)).trans ((e29.preserves 72 (by decide)).trans ((e28.preserves 72 (by decide)).trans ((e27.preserves 72 (by decide)).trans ((e26.preserves 72 (by decide)).trans ((e25.preserves 72 (by decide)).trans ((e24.preserves 72 (by decide)).trans ((e23.preserves 72 (by decide)).trans ((e22.preserves 72 (by decide)).trans ((e21.preserves 72 (by decide)).trans ((e20.preserves 72 (by decide)).trans ((e19.preserves 72 (by decide)).trans ((e18.preserves 72 (by decide)).trans ((e17.preserves 72 (by decide)).trans ((e16.preserves 72 (by decide)).trans ((e15.preserves 72 (by decide)).trans ((e14.preserves 72 (by decide)).trans r13))))))))))))))))))))))))))))))))
    · change u45.reg 73=(cursorAt layout 2:ℤ)
      have ptr:cursorAt layout 2=off2:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 73 (by decide)).trans ((e44.preserves 73 (by decide)).trans ((e43.preserves 73 (by decide)).trans ((e42.preserves 73 (by decide)).trans ((e41.preserves 73 (by decide)).trans ((e40.preserves 73 (by decide)).trans ((e39.preserves 73 (by decide)).trans ((e38.preserves 73 (by decide)).trans ((e37.preserves 73 (by decide)).trans ((e36.preserves 73 (by decide)).trans ((e35.preserves 73 (by decide)).trans ((e34.preserves 73 (by decide)).trans ((e33.preserves 73 (by decide)).trans ((e32.preserves 73 (by decide)).trans ((e31.preserves 73 (by decide)).trans ((e30.preserves 73 (by decide)).trans ((e29.preserves 73 (by decide)).trans ((e28.preserves 73 (by decide)).trans ((e27.preserves 73 (by decide)).trans ((e26.preserves 73 (by decide)).trans ((e25.preserves 73 (by decide)).trans ((e24.preserves 73 (by decide)).trans ((e23.preserves 73 (by decide)).trans ((e22.preserves 73 (by decide)).trans ((e21.preserves 73 (by decide)).trans ((e20.preserves 73 (by decide)).trans ((e19.preserves 73 (by decide)).trans ((e18.preserves 73 (by decide)).trans ((e17.preserves 73 (by decide)).trans ((e16.preserves 73 (by decide)).trans r15))))))))))))))))))))))))))))))
    · change u45.reg 74=(cursorAt layout 3:ℤ)
      have ptr:cursorAt layout 3=off3:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 74 (by decide)).trans ((e44.preserves 74 (by decide)).trans ((e43.preserves 74 (by decide)).trans ((e42.preserves 74 (by decide)).trans ((e41.preserves 74 (by decide)).trans ((e40.preserves 74 (by decide)).trans ((e39.preserves 74 (by decide)).trans ((e38.preserves 74 (by decide)).trans ((e37.preserves 74 (by decide)).trans ((e36.preserves 74 (by decide)).trans ((e35.preserves 74 (by decide)).trans ((e34.preserves 74 (by decide)).trans ((e33.preserves 74 (by decide)).trans ((e32.preserves 74 (by decide)).trans ((e31.preserves 74 (by decide)).trans ((e30.preserves 74 (by decide)).trans ((e29.preserves 74 (by decide)).trans ((e28.preserves 74 (by decide)).trans ((e27.preserves 74 (by decide)).trans ((e26.preserves 74 (by decide)).trans ((e25.preserves 74 (by decide)).trans ((e24.preserves 74 (by decide)).trans ((e23.preserves 74 (by decide)).trans ((e22.preserves 74 (by decide)).trans ((e21.preserves 74 (by decide)).trans ((e20.preserves 74 (by decide)).trans ((e19.preserves 74 (by decide)).trans r18)))))))))))))))))))))))))))
    · change u45.reg 75=(cursorAt layout 4:ℤ)
      have ptr:cursorAt layout 4=off4:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 75 (by decide)).trans ((e44.preserves 75 (by decide)).trans ((e43.preserves 75 (by decide)).trans ((e42.preserves 75 (by decide)).trans ((e41.preserves 75 (by decide)).trans ((e40.preserves 75 (by decide)).trans ((e39.preserves 75 (by decide)).trans ((e38.preserves 75 (by decide)).trans ((e37.preserves 75 (by decide)).trans ((e36.preserves 75 (by decide)).trans ((e35.preserves 75 (by decide)).trans ((e34.preserves 75 (by decide)).trans ((e33.preserves 75 (by decide)).trans ((e32.preserves 75 (by decide)).trans ((e31.preserves 75 (by decide)).trans ((e30.preserves 75 (by decide)).trans ((e29.preserves 75 (by decide)).trans ((e28.preserves 75 (by decide)).trans ((e27.preserves 75 (by decide)).trans ((e26.preserves 75 (by decide)).trans ((e25.preserves 75 (by decide)).trans ((e24.preserves 75 (by decide)).trans ((e23.preserves 75 (by decide)).trans ((e22.preserves 75 (by decide)).trans r21))))))))))))))))))))))))
    · change u45.reg 76=(cursorAt layout 5:ℤ)
      have ptr:cursorAt layout 5=off5:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 76 (by decide)).trans ((e44.preserves 76 (by decide)).trans ((e43.preserves 76 (by decide)).trans ((e42.preserves 76 (by decide)).trans ((e41.preserves 76 (by decide)).trans ((e40.preserves 76 (by decide)).trans ((e39.preserves 76 (by decide)).trans ((e38.preserves 76 (by decide)).trans ((e37.preserves 76 (by decide)).trans ((e36.preserves 76 (by decide)).trans ((e35.preserves 76 (by decide)).trans ((e34.preserves 76 (by decide)).trans ((e33.preserves 76 (by decide)).trans ((e32.preserves 76 (by decide)).trans ((e31.preserves 76 (by decide)).trans ((e30.preserves 76 (by decide)).trans ((e29.preserves 76 (by decide)).trans ((e28.preserves 76 (by decide)).trans ((e27.preserves 76 (by decide)).trans ((e26.preserves 76 (by decide)).trans ((e25.preserves 76 (by decide)).trans ((e24.preserves 76 (by decide)).trans r23))))))))))))))))))))))
    · change u45.reg 77=(cursorAt layout 6:ℤ)
      have ptr:cursorAt layout 6=off6:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 77 (by decide)).trans ((e44.preserves 77 (by decide)).trans ((e43.preserves 77 (by decide)).trans ((e42.preserves 77 (by decide)).trans ((e41.preserves 77 (by decide)).trans ((e40.preserves 77 (by decide)).trans ((e39.preserves 77 (by decide)).trans ((e38.preserves 77 (by decide)).trans ((e37.preserves 77 (by decide)).trans ((e36.preserves 77 (by decide)).trans ((e35.preserves 77 (by decide)).trans ((e34.preserves 77 (by decide)).trans ((e33.preserves 77 (by decide)).trans ((e32.preserves 77 (by decide)).trans ((e31.preserves 77 (by decide)).trans ((e30.preserves 77 (by decide)).trans ((e29.preserves 77 (by decide)).trans ((e28.preserves 77 (by decide)).trans r27))))))))))))))))))
    · change u45.reg 78=(cursorAt layout 7:ℤ)
      have ptr:cursorAt layout 7=off7:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 78 (by decide)).trans ((e44.preserves 78 (by decide)).trans ((e43.preserves 78 (by decide)).trans ((e42.preserves 78 (by decide)).trans ((e41.preserves 78 (by decide)).trans ((e40.preserves 78 (by decide)).trans ((e39.preserves 78 (by decide)).trans ((e38.preserves 78 (by decide)).trans ((e37.preserves 78 (by decide)).trans ((e36.preserves 78 (by decide)).trans ((e35.preserves 78 (by decide)).trans ((e34.preserves 78 (by decide)).trans ((e33.preserves 78 (by decide)).trans ((e32.preserves 78 (by decide)).trans r31))))))))))))))
    · change u45.reg 79=(cursorAt layout 8:ℤ)
      have ptr:cursorAt layout 8=off8:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 79 (by decide)).trans ((e44.preserves 79 (by decide)).trans ((e43.preserves 79 (by decide)).trans ((e42.preserves 79 (by decide)).trans ((e41.preserves 79 (by decide)).trans ((e40.preserves 79 (by decide)).trans ((e39.preserves 79 (by decide)).trans ((e38.preserves 79 (by decide)).trans ((e37.preserves 79 (by decide)).trans ((e36.preserves 79 (by decide)).trans r35))))))))))
    · change u45.reg 80=(cursorAt layout 9:ℤ)
      have ptr:cursorAt layout 9=off9:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 80 (by decide)).trans ((e44.preserves 80 (by decide)).trans ((e43.preserves 80 (by decide)).trans ((e42.preserves 80 (by decide)).trans ((e41.preserves 80 (by decide)).trans r40)))))
    · change u45.reg 81=(cursorAt layout 10:ℤ)
      have ptr:cursorAt layout 10=off10:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
      rw [ptr];exact ((e45.preserves 81 (by decide)).trans ((e44.preserves 81 (by decide)).trans r43))
  · have ofE:cursorAt layout 11=off11:=by simp [layout,offsets,cursorAt,off1,off2,off3,off4,off5,off6,off7,off8,off9,off10,off11] <;> ring
    rw [ofE];exact z45
  · intro j hj ne;exact seg.finish.preserves j (small_regs ⟨j,hj⟩ ne)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem solution (n h:ℕ) (input:ℤ → ℤ) (s:Logical.State) (one:s.reg 6=1) (zero:s.reg 7=0)
    (start:s.reg 8=0) (sz:s.reg 64=(n:ℤ)) (budget:s.reg 66=(h:ℤ)) :
    let H:=h+1
    let rows:=n^(2*H)
    let M:=H*rows
    let layout:=offsets n M
    ∃t z,Logical.Executes n input arena s t z ∧ z ≤ 4000*(h+2)*(n+1)^3*(M+1) ∧
      t.reg 68=(H:ℤ) ∧ t.reg 69=(rows:ℤ) ∧ t.reg 70=(M:ℤ) ∧ t.reg 82=0 ∧
      t.reg 8=(cursorAt layout 11:ℤ) ∧
      (∀j:Fin 11,t.reg (71+j.val)=(cursorAt layout j.val:ℤ)) ∧
      ((∀i,t.heap i=if i<cursorAt layout 11 then 0 else s.heap i) ∧ t.output=s.output ∧ t.closed=s.closed) ∧ (∀j<68,j≠8 → t.reg j=s.reg j) := Logical.startup n h input s one zero start sz budget
