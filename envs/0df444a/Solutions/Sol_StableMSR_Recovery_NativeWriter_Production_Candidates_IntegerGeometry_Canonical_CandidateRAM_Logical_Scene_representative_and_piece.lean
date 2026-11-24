-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.representative_and_piece
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T17:05:25.100838+00:00
-- url     : https://prove2.me/submissions/17ead561-2c6f-481a-8619-e4016ccf85d6

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
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


namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem op_fetch {n input} (s:State) (d a i base j:ℕ) (ptr:s.reg a=(base:ℤ)) (idx:s.reg i=(j:ℤ)):
    Executes n input (.op (.fetch d a i)) s (s.assign d (s.heap (base+j))) 64:=by
  apply Executes.op
  have pos:0 ≤ (base:ℤ)+j:=by positivity
  have val:((base:ℤ)+j).toNat=base+j:=by omega
  simp [Operation.next,ptr,idx,pos,val]
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene
open WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3500000
set_option maxRecDepth 32000

def labelBase (n r:ℕ):ℕ:=3+r/n*(n+2)+2
def wordAt (m:ℤ→ℤ) (b j:ℕ):ℤ:=m ((b:ℤ)+(j:ℤ))
def fresh (m:ℤ→ℤ) (b i k:ℕ):Bool:=
  (List.range k).all fun j=>decide (wordAt m b j ≠ wordAt m b i)
theorem fresh_succ (m:ℤ→ℤ) (b i k:ℕ):fresh m b i (k+1)=
    (fresh m b i k && decide (wordAt m b k ≠ wordAt m b i)):=by simp [fresh,List.range_succ]
theorem fresh_iff (m:ℤ→ℤ) (b i k:ℕ):
    fresh m b i k=true ↔ ∀j < k,wordAt m b j≠wordAt m b i:=by simp [fresh]

def setupOps : List Program:=[
  .op (.divide true 621 65 64),.op (.regular (.copy 189 621)),
  .op (.divide false 624 65 64),.op (.regular (.copy 190 624)),
  .op (.regular (.set 629 3)),.op (.regular (.set 634 2)),.op (.regular (.add 632 64 634)),
  .op (.multiply 630 189 632),.op (.regular (.add 628 629 630)),.op (.regular (.set 635 2)),
  .op (.regular (.add 627 628 635)),.op (.regular (.copy 191 627)),.op (.regular (.add 637 191 190)),
  .op (.regular (.load 636 637)),.op (.regular (.copy 192 636)),.op (.regular (.set 640 1)),
  .op (.regular (.copy 193 640))]
def testBody:=chain [.op (.regular (.add 645 191 194)),.op (.regular (.load 644 645)),
  .cond 644 192 (.cond 192 644 (.op (.regular (.set 643 1))) (.op (.regular (.set 643 0))))
    (.op (.regular (.set 643 0))),
  .cond 6 643 (chain [.op (.regular (.set 649 0)),.op (.regular (.copy 193 649))]) .skip]
def unitOps:List Program:=[.op (.multiply 651 64 64),.op (.regular (.set 654 1)),
  .op (.regular (.add 650 651 654)),.op (.regular (.copy 195 650))]
def segment:=chain ((listOf src_build_geometry).take 22)
theorem actual:
    segment=chain (setupOps++[forCount 194 642 190 testBody]++unitOps):=rfl

theorem setup (n r:ℕ) (m:ℤ→ℤ) (s:State) (pos:0 < n) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ))
    (slot:s.reg 65=(r:ℤ)):
    ∃t k,Executes n m (chain setupOps) s t k ∧ k ≤ 120+6*n+16*(r/n) ∧
      t.reg 189=((r/n:ℕ):ℤ) ∧ t.reg 190=((r%n:ℕ):ℤ) ∧ t.reg 191=(labelBase n r:ℤ) ∧
      t.reg 192=wordAt m (labelBase n r) (r%n) ∧ t.reg 193=1 ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have base:(3:ℤ)+(r/n:ℕ)*((n:ℤ)+2)+2=(labelBase n r:ℤ):=by simp [labelBase]
  have positive:0 < (n:ℤ):=by exact_mod_cast pos
  have addr:0≤(labelBase n r:ℤ)+(r%n:ℕ):=by omega
  have raw:rawInput ((labelBase n r:ℤ)+(r%n:ℕ))=true:=by unfold rawInput;rw [decide_eq_true addr];rfl
  have rowNN:0≤(r:ℤ)/(n:ℤ):=Int.ediv_nonneg (by omega) (by omega)
  have widthNN:0≤(n:ℤ)+2:=by omega
  have width:((n:ℤ)+2).toNat=n+2:=by omega
  have computed:(3:ℤ)+((r:ℤ)/(n:ℤ))*((n:ℤ)+2)+2=(labelBase n r:ℤ):=by simpa using base
  have legal:rawInput ((labelBase n r:ℤ)+(r:ℤ)%(n:ℤ))=true:=by simpa using raw
  have h:∃t k,evalLine n m (chain setupOps) s=some (t,k) ∧ k ≤ 120+6*n+16*(r/n) ∧
      t.reg 189=((r/n:ℕ):ℤ) ∧ t.reg 190=((r%n:ℕ):ℤ) ∧ t.reg 191=(labelBase n r:ℤ) ∧
      t.reg 192=wordAt m (labelBase n r) (r%n) ∧ t.reg 193=1 ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    simp [setupOps,chain,evalLine,Operation.next,regularNext,State.assign,wordAt,one,size,slot,computed,positive,pos,legal,rowNN,widthNN,width] <;> omega
  obtain ⟨t,k,ex,c,h⟩:=h;exact ⟨t,k,evalLine_sound _ _ _ _ ex,c,h⟩

theorem test (n b i j:ℕ) (m:ℤ→ℤ) (s:State) (one:s.reg 6=1)
    (base:s.reg 191=(b:ℤ)) (key:s.reg 192=wordAt m b i) (idx:s.reg 194=(j:ℤ))
    (flag:s.reg 193=if fresh m b i j then 1 else 0):
    ∃t k,Executes n m testBody s t k ∧ k ≤ 22 ∧
      t.reg 193=(if fresh m b i (j+1) then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have ad:0≤(b:ℤ)+(j:ℤ):=by omega
  have raw:rawInput ((b:ℤ)+(j:ℤ))=true:=by simp [rawInput,ad]
  have h:∃t k,evalLine n m testBody s=some (t,k) ∧ k ≤ 22 ∧
      t.reg 193=(if fresh m b i (j+1) then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    have loaded:m ((b:ℤ)+(j:ℤ))=wordAt m b j:=rfl
    rcases lt_trichotomy (wordAt m b j) (wordAt m b i) with e|e|e
    · have le:=le_of_lt e;have rev:=not_le.mpr e;have ne:=ne_of_lt e
      simp [testBody,chain,evalLine,Operation.next,regularNext,State.assign,one,base,key,idx,raw,loaded,le,rev,ne,fresh_succ,flag]
    · simp [testBody,chain,evalLine,Operation.next,regularNext,State.assign,one,base,key,idx,raw,loaded,e,fresh_succ]
    · have le:=le_of_lt e;have rev:=not_le.mpr e;have ne:=ne_of_gt e
      simp [testBody,chain,evalLine,Operation.next,regularNext,State.assign,one,base,key,idx,raw,loaded,le,rev,ne,fresh_succ,flag]
  obtain ⟨t,k,ex,c,h⟩:=h;exact ⟨t,k,evalLine_sound _ _ _ _ ex,c,h⟩

theorem threshold (n:ℕ) (m:ℤ→ℤ) (s:State) (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)):
    ∃t k,Executes n m (chain unitOps) s t k ∧ k ≤ 20+6*n ∧ t.reg 195=(IntegerGeometry.unit n:ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have h:∃t k,evalLine n m (chain unitOps) s=some (t,k) ∧ k ≤ 20+6*n ∧ t.reg 195=(IntegerGeometry.unit n:ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    simp [unitOps,chain,evalLine,Operation.next,regularNext,State.assign,one,sz,IntegerGeometry.unit] <;> omega
  obtain ⟨t,k,ex,c,h⟩:=h;exact ⟨t,k,evalLine_sound _ _ _ _ ex,c,h⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene
open WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3600000
set_option maxRecDepth 32000

theorem run (n r:ℕ) (m:ℤ→ℤ) (s:State) (hn:0 < n) (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (slot:s.reg 65=(r:ℤ)):
    ∃t k,Executes n m segment s t k ∧ k ≤ 350*(n+1)+20*(r/n) ∧
      t.reg 189=((r/n:ℕ):ℤ) ∧ t.reg 190=((r%n:ℕ):ℤ) ∧ t.reg 191=(labelBase n r:ℤ) ∧
      t.reg 192=wordAt m (labelBase n r) (r%n) ∧ t.reg 193=(if fresh m (labelBase n r) (r%n) (r%n) then 1 else 0) ∧
      t.reg 195=(IntegerGeometry.unit n:ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let i:=r%n
  let b:=labelBase n r
  obtain ⟨v,j,setupRun,jt,row,idx,base,label,initial,mem,out,cl⟩:=setup n r m s hn one sz slot
  obtain ⟨c,pre,cost⟩:=splitChain setupOps setupRun
  have one':v.reg 6=1:=(setupRun.preserves 6 (by decide)).trans one
  let P:=fun a (w:State)=>w.reg 193=(if fresh m b i a then 1 else 0) ∧ w.reg 6=1 ∧
    w.reg 191=(b:ℤ) ∧ w.reg 192=wordAt m b i ∧ w.heap=s.heap ∧ w.output=s.output ∧ w.closed=s.closed
  have begin':P 0 (forSetup 194 642 190 v):=by
    exact ⟨by simpa [forSetup,State.assign,fresh] using initial,one',base,label,mem,out,cl⟩
  have adv (a:ℕ) (_:a < i) (w:State) (good:P a w) (ix:w.reg 194=(a:ℤ)) (_:w.reg 642=(i:ℤ)-1):
      ∃t k,Executes n m testBody w t k ∧ k ≤ 22 ∧ t.reg 194=w.reg 194 ∧ t.reg 642=w.reg 642 ∧ P (a+1) (t.assign 194 (t.reg 194+1)):=by
    obtain ⟨flag,unit',tab,lab,mm,oo,cc⟩:=good
    obtain ⟨t,k,ex,le,f,fr,o,c⟩:=test n b i a m w unit' tab lab ix flag
    exact ⟨t,k,ex,le,ex.preserves _ (by decide),ex.preserves _ (by decide),f,(ex.preserves 6 (by decide)).trans unit',
      (ex.preserves 191 (by decide)).trans tab,(ex.preserves 192 (by decide)).trans lab,fr.trans mm,o.trans oo,c.trans cc⟩
  obtain ⟨u,h,loop,ht,flag,one'',tab,lab,fr,o,c'⟩:=source_for (N:=n) (input:=m) 194 642 190 i 22 testBody P (by decide) (by decide) v idx begin' adv
  obtain ⟨t,k,units,kt,unit',tm,tOut,tc⟩:=threshold n m u one'' ((loop.preserves 64 (by decide)).trans ((setupRun.preserves 64 (by decide)).trans sz))
  have full:Executes n m segment s t (c+(1+h+k)):=by rw [actual];exact pre.continue _ (.seq loop units)
  have bound:i < n:=Nat.mod_lt _ hn
  exact ⟨t,_,full,by omega,(units.preserves 189 (by decide)).trans ((loop.preserves 189 (by decide)).trans row),
    (units.preserves 190 (by decide)).trans ((loop.preserves 190 (by decide)).trans idx),
    (units.preserves 191 (by decide)).trans tab,(units.preserves 192 (by decide)).trans lab,
    (units.preserves 193 (by decide)).trans flag,unit',tm.trans fr,tOut.trans o,tc.trans c'⟩

theorem piece_criterion (n u:ℕ) (scene:ℕ→ℤ) (p i:Fin n):
    p∈Bits.piece n scene u i.val ↔
    (let b:=3+u*(n+2)+2
     scene (b+p.val)=scene (b+i.val) ∧ ∀j:Fin n,j < i → scene (b+j.val)≠scene (b+i.val)):=by
  let key:=fun q:Fin n=>scene (3+u*(n+2)+2+q.val)
  let fibre:=Finset.univ.filter fun q:Fin n=>key q=key p
  have belongs (q:Fin n):q∈fibre ↔ key q=key p:=by simp [fibre]
  have ne:fibre.Nonempty:=⟨p,(belongs p).mpr rfl⟩
  let m:=fibre.min' ne
  have entry:key m=key p:=(belongs _).mp (Finset.min'_mem _ _)
  have least (q:Fin n) (h:key q=key p):m ≤ q:=Finset.min'_le _ q ((belongs q).mpr h)
  unfold Bits.piece
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change m.val=i.val ↔ key p=key i ∧ ∀j:Fin n,j < i → key j≠key i
  constructor
  · intro eq
    have e:m=i:=Fin.ext eq
    have pi:key p=key i:=entry.symm.trans (congrArg key e)
    refine ⟨pi,?_⟩;intro j hj same
    have le:=least j (same.trans pi.symm);rw [e] at le;exact (not_le_of_gt hj) le
  · rintro ⟨pi,first⟩
    have le:m ≤ i:=least i pi.symm
    have ge:i ≤ m:=by
      by_contra! h
      exact first m h (entry.trans pi)
    exact congrArg Fin.val (le_antisymm le ge)

theorem piece_from_flag (n r:ℕ) (hn:0 < n) (m:ℤ→ℤ) (scene:ℕ→ℤ) (agree:∀j:ℕ,m (j:ℤ)=scene j) (p:Fin n):
    p∈Bits.piece n scene (r/n) (r%n) ↔
      fresh m (labelBase n r) (r%n) (r%n)=true ∧ wordAt m (labelBase n r) p.val=wordAt m (labelBase n r) (r%n):=by
  let i:Fin n:=⟨r%n,Nat.mod_lt _ hn⟩
  let b:=labelBase n r
  have reads (j:ℕ):wordAt m b j=scene (b+j):=by simpa [wordAt] using agree (b+j)
  rw [piece_criterion n (r/n) scene p i,fresh_iff]
  change (_ ∧ ∀j:Fin n,j < i → scene (b+j.val)≠scene (b+i.val)) ↔
      (∀j < i.val,wordAt m b j≠wordAt m b i.val) ∧ wordAt m b p.val=wordAt m b i.val
  simp only [reads]
  constructor
  · rintro ⟨h,first⟩;exact ⟨fun j hj=>first ⟨j,lt_trans hj i.isLt⟩ hj,h⟩
  · rintro ⟨first,h⟩;exact ⟨h,fun j hj=>first j.val hj⟩

/-- On every point, the two comparisons made by the following net sweep select
exactly the reference piece, including scene labels with negative values. -/
theorem geometry_start (n r:ℕ) (m:ℤ→ℤ) (scene:ℕ→ℤ) (s:State)
    (hn:0 < n) (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (slot:s.reg 65=(r:ℤ)) (agree:∀j:ℕ,m (j:ℤ)=scene j):
    ∃t k,Executes n m (chain ((listOf src_build_geometry).take 22)) s t k ∧ k ≤ 350*(n+1)+20*(r/n) ∧
      t.reg 189=((r/n:ℕ):ℤ) ∧ t.reg 190=((r%n:ℕ):ℤ) ∧ t.reg 191=(labelBase n r:ℤ) ∧
      t.reg 192=wordAt m (labelBase n r) (r%n) ∧ t.reg 195=(IntegerGeometry.unit n:ℤ) ∧
      (∀p:Fin n, p∈Bits.piece n scene (r/n) (r%n) ↔ 1≤t.reg 193 ∧ m (t.reg 191+p.val)=t.reg 192) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  obtain ⟨t,k,ex,tm,row,ix,base,lab,flag,unit',mem,out,cl⟩:=run n r m s hn one sz slot
  refine ⟨t,k,ex,tm,row,ix,base,lab,unit',?_,mem,out,cl⟩
  intro p;rw [piece_from_flag n r hn m scene agree p,flag,base,lab]
  cases f:fresh m (labelBase n r) (r%n) (r%n) <;> simp [wordAt,f]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene

set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem solution (n r:ℕ) (m:ℤ→ℤ) (scene:ℕ→ℤ) (s:Logical.State)
    (hn:0<n) (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (slot:s.reg 65=(r:ℤ)) (agree:∀j:ℕ,m (j:ℤ)=scene j):
    ∃t k,Logical.Executes n m (Logical.chain ((Logical.listOf Logical.src_build_geometry).take 22)) s t k ∧
      k ≤ 350*(n+1)+20*(r/n) ∧ t.reg 189=((r/n:ℕ):ℤ) ∧ t.reg 190=((r%n:ℕ):ℤ) ∧
      t.reg 191=((3+r/n*(n+2)+2:ℕ):ℤ) ∧
      t.reg 192=m (((3+r/n*(n+2)+2:ℕ):ℤ)+(r%n:ℕ)) ∧ t.reg 195=(IntegerGeometry.unit n:ℤ) ∧
      (∀p:Fin n, p∈IntegerGeometry.Bits.piece n scene (r/n) (r%n) ↔ 1≤t.reg 193 ∧ m (t.reg 191+p.val)=t.reg 192) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := Logical.Scene.geometry_start n r m scene s hn one sz slot agree
