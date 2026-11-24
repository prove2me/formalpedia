-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM.greedy_net_bitmap
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T17:27:19.351974+00:00
-- url     : https://prove2.me/submissions/27d1550c-9a70-4d9b-987d-1007045d416e

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_representative_and_piece
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
def labelBase (n r:ℕ):ℕ:=3+r/n*(n+2)+2
def wordAt (m:ℤ→ℤ) (b j:ℕ):ℤ:=m ((b:ℤ)+(j:ℤ))
abbrev geometry_start := @StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.representative_and_piece
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene
open WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1600000

/-- The specification of the next net sweep, expressed with the same all-point order as the source. -/
def earlier (n k:ℕ) := (List.finRange n).filter fun q=>decide (q.val < k)
theorem earlier_sorted (n k:ℕ):(earlier n k).SortedLT:=
  ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
theorem earlier_succ {n:ℕ} (i:Fin n):earlier n (i.val+1)=earlier n i.val++[i]:=by
  have sorted:(earlier n i.val++[i]).SortedLT:=by
    apply List.Pairwise.sortedLT;apply List.pairwise_append.mpr
    refine ⟨(earlier_sorted ..).pairwise,by simp,?_⟩
    intro p hp q hq
    have h:p.val < i.val:=by simpa [earlier] using hp
    simp only [List.mem_singleton] at hq
    simpa [hq] using h
  apply (earlier_sorted ..).eq_of_mem_iff sorted
  intro p;simp [earlier,Fin.ext_iff] <;> omega

def keepAt {n:ℕ} (m:ℤ→ℤ) (A:Finset (Fin n)) (p:Fin n):Finset (Fin n):=
  if ∀z∈A,2*(IntegerGeometry.unit n:ℤ) < m (IntegerGeometry.address p z) then insert p A else A
def netStep {n:ℕ} (m:ℤ→ℤ) (W A:Finset (Fin n)) (p:Fin n):Finset (Fin n):=
  if p∈W then keepAt m A p else A
def retained {n:ℕ} (m:ℤ→ℤ) (W:Finset (Fin n)) (k:ℕ) :=
  (earlier n k).foldl (netStep m W) ∅
theorem retained_succ {n:ℕ} (m:ℤ→ℤ) (W:Finset (Fin n)) (i:Fin n):
    retained m W (i.val+1)=netStep m W (retained m W i.val) i:=by
  simp [retained,earlier_succ,List.foldl_append]
theorem retained_from_prefix {n:ℕ} (m:ℤ→ℤ) (W:Finset (Fin n)) (k:ℕ) (p:Fin n)
    (mem:p∈retained m W k):p∈W ∧ p.val < k:=by
  have fold (xs:List (Fin n)) (A:Finset (Fin n)) (h:p∈xs.foldl (netStep m W) A):
      p∈A ∨ (p∈W ∧ p∈xs):=by
    induction xs generalizing A with
    | nil=>exact Or.inl h
    | cons q qs ih=>
      rcases ih _ h with hstep|⟨inW,inQ⟩
      · by_cases w:q∈W
        · simp only [netStep,if_pos w,keepAt] at hstep
          split at hstep
          · rcases Finset.mem_insert.mp hstep with e|ha
            · subst q;exact Or.inr ⟨w,by simp⟩
            · exact Or.inl ha
          · exact Or.inl hstep
        · exact Or.inl (by simpa [netStep,w] using hstep)
      · exact Or.inr ⟨inW,List.mem_cons_of_mem _ inQ⟩
  rcases fold (earlier n k) ∅ mem with h|⟨hw,hp⟩
  · exact False.elim (by simpa using h)
  · exact ⟨hw,by simpa [earlier] using hp⟩

theorem retained_all {n:ℕ} (m:ℤ→ℤ) (W:Finset (Fin n)):retained m W n=Bits.net m W:=by
  have full:earlier n n=List.finRange n:=by
    apply List.filter_eq_self.mpr;intro i _;simp [i.isLt]
  have ordered:W.sort (·≤·)=(List.finRange n).filter (fun p=>decide (p∈W)):=
    W.sortedLT_sort.eq_of_mem_iff ((List.sortedLT_finRange n).pairwise.filter _).sortedLT (by simp)
  have skip (xs:List (Fin n)) (A:Finset (Fin n)):xs.foldl (netStep m W) A=
      (xs.filter (fun p=>decide (p∈W))).foldl (keepAt m) A:=by
    induction xs generalizing A with
    | nil=>rfl
    | cons p ps ih=>by_cases h:p∈W <;> simp [h,netStep,ih]
  unfold retained Bits.net;rw [full,ordered];exact skip _ _

/-- At index i the inner scan only needs marked indices smaller than i. -/
theorem net_decision {n:ℕ} (m:ℤ→ℤ) (W:Finset (Fin n)) (i:Fin n):
    let A:=retained m W i.val
    retained m W (i.val+1)=
      (if i∈W ∧ ∀z:Fin n,z.val < i.val → z∈A → ¬m (IntegerGeometry.address i z)≤2*(IntegerGeometry.unit n:ℤ)
       then insert i A else A):=by
  dsimp only
  have same:(∀z∈retained m W i.val,2*(IntegerGeometry.unit n:ℤ) < m (IntegerGeometry.address i z)) ↔
      ∀z:Fin n,z.val < i.val → z∈retained m W i.val → ¬m (IntegerGeometry.address i z)≤2*(IntegerGeometry.unit n:ℤ):=by
    constructor
    · intro h z _ hz;exact not_le.mpr (h _ hz)
    · intro h z hz;exact lt_of_not_ge (h z (retained_from_prefix m W _ _ hz).2 hz)
  rw [retained_succ];by_cases w:i∈W <;> simp [netStep,keepAt,w,same]
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3600000
set_option maxRecDepth 32000

def rowBody := chain [.op (.fetch 673 71 198), .op (.regular (.copy 672 673)),
  .cond 6 672 (chain [.op (.regular (.copy 159 194)), .op (.regular (.copy 160 198)), src_imat,
    .op (.regular (.copy 677 161)), .op (.shift 680 195 1),
    .cond 677 680 (.op (.regular (.set 676 1))) (.op (.regular (.set 676 0))),
    .op (.regular (.copy 672 676))]) .skip,
  .cond 6 672 (chain [.op (.regular (.set 682 0)), .op (.regular (.copy 201 682))]) .skip]
def collision (m:ℤ→ℤ) (heap:ℕ→ℤ) (n a i j U:ℕ):Bool:=
  decide (1 ≤ heap (a+j) ∧ m (cell 6 (i*n+j)) ≤ 2*(U:ℤ))
def clearPrefix (m:ℤ→ℤ) (heap:ℕ→ℤ) (n a i k U:ℕ):Bool:=
  (List.range k).all fun j=>!(collision m heap n a i j U)

theorem row (n a i j U:ℕ) (m:ℤ→ℤ) (s:State) (keep:Bool) (one:s.reg 6=1)
    (sz:s.reg 64=(n:ℤ)) (ptr:s.reg 71=(a:ℤ)) (p:s.reg 194=(i:ℤ)) (ix:s.reg 198=(j:ℤ))
    (unit':s.reg 195=(U:ℤ)) (flag:s.reg 201=if keep then 1 else 0):
    ∃t k,Executes n m rowBody s t k ∧ k ≤ 160+6*n ∧
      t.reg 201=(if (keep && !(collision m s.heap n a i j U)) then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let q:=cell 6 (i*n+j)
  have aq:q= -87-64*((i:ℤ)*n+j):=by simp [q,cell,word];ring
  have raw:rawInput q=true:=by
    have pos:0 ≤ (i:ℤ)*n:=by positivity
    simp [q,cell,word,rawInput];omega
  have ad:0 ≤ (a:ℤ)+(j:ℤ):=by omega
  have aj:((a:ℤ)+(j:ℤ)).toNat=a+j:=by omega
  have h:∃t k,evalLine n m rowBody s=some (t,k) ∧ k ≤ 160+6*n ∧
      t.reg 201=(if (keep && !(collision m s.heap n a i j U)) then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    by_cases active:1 ≤ s.heap (a+j) <;> by_cases near:m q ≤ 2*(U:ℤ) <;> cases keep <;>
      simp [rowBody,src_imat,chain,evalLine,Operation.next,regularNext,State.assign,one,sz,ptr,p,ix,unit',flag,
        ad,aj,←aq,raw,active,near,collision,show cell 6 (i*n+j)=q from rfl] <;> omega
  obtain ⟨t,k,ex,tm,v⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,v⟩

theorem scan (n a i U:ℕ) (m:ℤ→ℤ) (s:State) (one:s.reg 6=1)
    (sz:s.reg 64=(n:ℤ)) (ptr:s.reg 71=(a:ℤ)) (p:s.reg 194=(i:ℤ)) (unit':s.reg 195=(U:ℤ)) (flag:s.reg 201=1):
    ∃t k,Executes n m (forCount 198 671 194 rowBody) s t k ∧ k ≤ 9+i*(165+6*n) ∧
      t.reg 201=(if clearPrefix m s.heap n a i i U then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let P:=fun j (w:State)=> w.reg 201=(if clearPrefix m s.heap n a i j U then 1 else 0) ∧
    w.reg 6=1 ∧ w.reg 64=(n:ℤ) ∧ w.reg 71=(a:ℤ) ∧ w.reg 194=(i:ℤ) ∧ w.reg 195=(U:ℤ) ∧
    w.heap=s.heap ∧ w.output=s.output ∧ w.closed=s.closed
  have base:P 0 (forSetup 198 671 194 s):=by
    exact ⟨by simpa [forSetup,State.assign,clearPrefix] using flag,one,sz,ptr,p,unit',rfl,rfl,rfl⟩
  have adv (j:ℕ) (_:j < i) (w:State) (ok:P j w) (idx:w.reg 198=(j:ℤ)) (_:w.reg 671=(i:ℤ)-1):
      ∃t k,Executes n m rowBody w t k ∧ k ≤ 160+6*n ∧ t.reg 198=w.reg 198 ∧ t.reg 671=w.reg 671 ∧
        P (j+1) (t.assign 198 (t.reg 198+1)):=by
    obtain ⟨prev,u,size,pt,p',scale,mem,out,cl⟩:=ok
    obtain ⟨t,k,run,tm,r,th,to',tc⟩:=row n a i j U m w _ u size pt p' idx scale prev
    refine ⟨t,k,run,tm,run.preserves _ (by decide),run.preserves _ (by decide),?_,
      (run.preserves 6 (by decide)).trans u,(run.preserves 64 (by decide)).trans size,
      (run.preserves 71 (by decide)).trans pt,(run.preserves 194 (by decide)).trans p',
      (run.preserves 195 (by decide)).trans scale,th.trans mem,to'.trans out,tc.trans cl⟩
    change t.reg 201=_;simpa [clearPrefix,List.range_succ,mem] using r
  obtain ⟨t,k,run,tm,r,_,_,_,_,_,mem,out,cl⟩:=source_for (N:=n) (input:=m) 198 671 194 i
    (160+6*n) rowBody P (by decide) (by decide) s p base adv
  exact ⟨t,k,run,by simpa only [show 160+6*n+5=165+6*n by omega] using tm,r,mem,out,cl⟩

theorem scan_test {n:ℕ} (m:ℤ→ℤ) (heap:ℕ→ℤ) (a:ℕ) (W:Finset (Fin n)) (i:Fin n)
    (bits:∀z:Fin n,z.val < i.val → (1 ≤ heap (a+z.val) ↔ z∈retained m W i.val)):
    clearPrefix m heap n a i.val i.val (IntegerGeometry.unit n)=true ↔
    ∀z∈retained m W i.val,2*(IntegerGeometry.unit n:ℤ) < m (IntegerGeometry.address i z):=by
  simp only [clearPrefix,List.all_eq_true,List.mem_range,Bool.not_eq_true',collision,decide_eq_false_iff_not]
  constructor
  · intro h z hz
    have prior: z.val < i.val :=(retained_from_prefix m W i.val z hz).2
    exact lt_of_not_ge (fun small=>h z.val prior ⟨(bits z prior).mpr hz,small⟩)
  · intro h j hj both
    let z:Fin n:=⟨j,lt_trans hj i.isLt⟩
    exact (not_le_of_gt (h z ((bits z hj).mp both.1))) both.2

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3600000
set_option maxRecDepth 32000

def labelOps:List Program:=[.op (.regular (.copy 657 193)),
  .cond 6 657 (chain [.op (.regular (.add 661 191 194)),.op (.regular (.load 660 661)),
    .cond 660 192 (.cond 192 660 (.op (.regular (.set 659 1))) (.op (.regular (.set 659 0)))) (.op (.regular (.set 659 0))),
    .op (.regular (.copy 657 659))]) .skip]
def markOps:List Program:=[.op (.regular (.set 668 1)),.op (.save 73 194 668),
  .op (.regular (.set 669 1)),.op (.regular (.copy 201 669))]
def hitOps:List Program:=markOps++[forCount 198 671 194 rowBody,.op (.save 71 194 201)]
def pointCode:=chain (labelOps++[.cond 6 657 (chain hitOps) .skip])
def netLoop:=forCount 194 656 64 pointCode
theorem actual_net_loop: (listOf src_build_geometry)[22]?=some netLoop:=rfl

theorem classify (n b i:ℕ) (m:ℤ→ℤ) (s:State) (one:s.reg 6=1) (ptr:s.reg 191=(b:ℤ)) (idx:s.reg 194=(i:ℤ)):
    ∃t k,Executes n m (chain labelOps) s t k ∧ k ≤ 20 ∧
      (1 ≤ t.reg 657 ↔ 1 ≤ s.reg 193 ∧ wordAt m b i=s.reg 192) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have nn:0 ≤ (b:ℤ)+(i:ℤ):=by omega
  have raw:rawInput ((b:ℤ)+(i:ℤ))=true:=by simp [rawInput,nn]
  have h:∃t k,evalLine n m (chain labelOps) s=some (t,k) ∧ k ≤ 20 ∧
      (1 ≤ t.reg 657 ↔ 1 ≤ s.reg 193 ∧ wordAt m b i=s.reg 192) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    by_cases live:1 ≤ s.reg 193
    · rcases lt_trichotomy (m ((b:ℤ)+(i:ℤ))) (s.reg 192) with e|e|e
      · simp [labelOps,chain,evalLine,Operation.next,regularNext,State.assign,one,ptr,idx,wordAt,raw,live,e.le,
          not_le.mpr e,ne_of_lt e]
      · simp [labelOps,chain,evalLine,Operation.next,regularNext,State.assign,one,ptr,idx,wordAt,raw,live,e]
      · simp [labelOps,chain,evalLine,Operation.next,regularNext,State.assign,one,ptr,idx,wordAt,raw,live,e.le,
          not_le.mpr e,ne_of_gt e]
    · simp [labelOps,chain,evalLine,Operation.next,regularNext,State.assign,one,live] <;> omega
  obtain ⟨t,k,ex,le,res⟩:=h;exact ⟨t,k,evalLine_sound _ _ _ _ ex,le,res⟩

theorem mark (n B i:ℕ) (m:ℤ→ℤ) (s:State) (ptr:s.reg 73=(B:ℤ)) (idx:s.reg 194=(i:ℤ)):
    ∃t k,Executes n m (chain markOps) s t k ∧ k ≤ 80 ∧ t.reg 201=1 ∧
      t.heap=Function.update s.heap (B+i) 1 ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have nn:0 ≤ (B:ℤ)+(i:ℤ):=by omega
  have ad:((B:ℤ)+(i:ℤ)).toNat=B+i:=by omega
  have h:∃t k,evalLine n m (chain markOps) s=some (t,k) ∧ k ≤ 80 ∧ t.reg 201=1 ∧
      t.heap=Function.update s.heap (B+i) 1 ∧ t.output=s.output ∧ t.closed=s.closed:=by
    simp [markOps,chain,evalLine,Operation.next,regularNext,State.assign,State.save,ptr,idx,nn,ad]
  obtain ⟨t,k,ex,le,res⟩:=h;exact ⟨t,k,evalLine_sound _ _ _ _ ex,le,res⟩

theorem clear_frame (m:ℤ→ℤ) (h g:ℕ→ℤ) (n a i z U:ℕ) (frame:∀j < z,g (a+j)=h (a+j)):
    clearPrefix m g n a i z U=clearPrefix m h n a i z U:=by
  have eq:clearPrefix m g n a i z U=true ↔ clearPrefix m h n a i z U=true:=by
    simp only [clearPrefix,List.all_eq_true,List.mem_range]
    apply forall_congr';intro j;apply forall_congr';intro hj;simp [collision,frame j hj]
  cases x:clearPrefix m g n a i z U <;> cases y:clearPrefix m h n a i z U <;> simp_all

theorem hit (n a B i U:ℕ) (m:ℤ→ℤ) (s:State) (hi:i < n) (noalias:a+n ≤ B)
    (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (net:s.reg 71=(a:ℤ)) (piece:s.reg 73=(B:ℤ))
    (p:s.reg 194=(i:ℤ)) (unit':s.reg 195=(U:ℤ)):
    ∃t k,Executes n m (chain hitOps) s t k ∧ k ≤ 450*(n+1)^2 ∧
      t.heap=Function.update (Function.update s.heap (B+i) 1) (a+i) (if clearPrefix m s.heap n a i i U then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed:=by
  obtain ⟨v,j,first,jt,on,arr,out,cl⟩:=mark n B i m s piece p
  obtain ⟨c,pre,cost⟩:=splitChain markOps first
  obtain ⟨u,k,loop,tm,flag,h,o,f⟩:=scan n a i U m v ((first.preserves 6 (by decide)).trans one)
    ((first.preserves 64 (by decide)).trans sz) ((first.preserves 71 (by decide)).trans net)
    ((first.preserves 194 (by decide)).trans p) ((first.preserves 195 (by decide)).trans unit') on
  have same:clearPrefix m v.heap n a i i U=clearPrefix m s.heap n a i i U:=by
    apply clear_frame;intro j hj;rw [arr,Function.update_of_ne (by omega)]
  let val:ℤ:=if clearPrefix m s.heap n a i i U then 1 else 0
  have vflag:u.reg 201=val:=by rw [flag,same]
  have aa:u.reg 71=(a:ℤ):=(loop.preserves 71 (by decide)).trans ((first.preserves 71 (by decide)).trans net)
  have ii:u.reg 194=(i:ℤ):=(loop.preserves 194 (by decide)).trans ((first.preserves 194 (by decide)).trans p)
  have nn:0 ≤ (a:ℤ)+(i:ℤ):=by omega
  have ad:((a:ℤ)+(i:ℤ)).toNat=a+i:=by omega
  have save:Executes n m (.op (.save 71 194 201)) u (u.save (a+i) val) 64:=by
    apply Executes.op;simp [Operation.next,aa,ii,vflag,nn,ad]
  have ex:Executes n m (chain hitOps) s (u.save (a+i) val) _:=pre.continue _ (.seq loop (.seq save (.skip _)))
  refine ⟨_,_,ex,?_,?_,o.trans out,f.trans cl⟩
  · have bound:=Nat.mul_le_mul_right (165+6*n) (Nat.le_of_lt hi)
    ring_nf at tm bound ⊢ <;> omega
  · change Function.update u.heap _ _=_;rw [h,arr]

theorem point (n a B b i U:ℕ) (m:ℤ→ℤ) (s:State) (hi:i < n) (noalias:a+n ≤ B)
    (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (net:s.reg 71=(a:ℤ)) (piece:s.reg 73=(B:ℤ))
    (base:s.reg 191=(b:ℤ)) (p:s.reg 194=(i:ℤ)) (unit':s.reg 195=(U:ℤ)):
    ∃t k,Executes n m pointCode s t k ∧ k ≤ 500*(n+1)^2 ∧
      t.heap=(if 1 ≤ s.reg 193 ∧ wordAt m b i=s.reg 192 then
        Function.update (Function.update s.heap (B+i) 1) (a+i) (if clearPrefix m s.heap n a i i U then 1 else 0)
        else s.heap) ∧ t.output=s.output ∧ t.closed=s.closed:=by
  obtain ⟨v,j,head,jt,cond',mem,out,cl⟩:=classify n b i m s one base p
  obtain ⟨c,pre,cost⟩:=splitChain labelOps head
  have unit1:v.reg 6=1:=(head.preserves _ (by decide)).trans one
  by_cases yes:1 ≤ s.reg 193 ∧ wordAt m b i=s.reg 192
  · obtain ⟨t,k,run,tm,h,o,f⟩:=hit n a B i U m v hi noalias unit1 ((head.preserves 64 (by decide)).trans sz)
      ((head.preserves 71 (by decide)).trans net) ((head.preserves 73 (by decide)).trans piece)
      ((head.preserves 194 (by decide)).trans p) ((head.preserves 195 (by decide)).trans unit')
    have br:Executes n m (.cond 6 657 (chain hitOps) .skip) v t (1+k):=.yes (by rw [unit1];exact cond'.mpr yes) run
    have ex: Executes n m pointCode s t _:=pre.continue _ (.seq br (.skip _))
    exact ⟨t,_,ex,by ring_nf at tm ⊢ <;> omega,by simpa [yes,mem] using h,o.trans out,f.trans cl⟩
  · have br:Executes n m (.cond 6 657 (chain hitOps) .skip) v v 2:=.no
      (by rw [unit1];exact fun h => yes (cond'.mp h)) (.skip _)
    have ex:Executes n m pointCode s v _:=pre.continue _ (.seq br (.skip _))
    exact ⟨v,_,ex,by ring_nf <;> omega,by simpa [yes] using mem,out,cl⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32000

theorem kept_bit {n:ℕ} (m:ℤ→ℤ) (h:ℕ→ℤ) (a:ℕ) (W:Finset (Fin n)) (i z:Fin n)
    (bits:∀p:Fin n,p.val < i.val → (1 ≤ h (a+p.val) ↔ p∈retained m W i.val)):
    (if z∈retained m W (i.val+1) then (1:ℤ) else 0)=
      (if z=i then (if i∈W ∧ clearPrefix m h n a i.val i.val (IntegerGeometry.unit n)=true then 1 else 0)
       else (if z∈retained m W i.val then 1 else 0)):=by
  have prior:i∉retained m W i.val:=fun e=>Nat.lt_irrefl _ (retained_from_prefix m W _ _ e).2
  simp only [retained_succ,scan_test m h a W i bits]
  by_cases good:(∀v∈retained m W i.val,2*(IntegerGeometry.unit n:ℤ) < m (IntegerGeometry.address i v))
  · by_cases wi:i∈W <;> by_cases same:z=i <;> simp [netStep,keepAt,wi,if_pos good,same,prior]
  · by_cases wi:i∈W <;> by_cases same:z=i <;> simp [netStep,keepAt,wi,if_neg good,same,prior]


/-- The full source sweep writes the reference greedy net and the selected piece to their two arrays. -/
theorem complete {n:ℕ} (a B b:ℕ) (W:Finset (Fin n)) (m:ℤ→ℤ) (s:State) (space:a+n ≤ B)
    (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (net:s.reg 71=(a:ℤ)) (piece:s.reg 73=(B:ℤ))
    (base:s.reg 191=(b:ℤ)) (scale:s.reg 195=(IntegerGeometry.unit n:ℤ))
    (label:∀p:Fin n,p∈W ↔ 1 ≤ s.reg 193 ∧ wordAt m b p.val=s.reg 192)
    (az:∀j < n,s.heap (a+j)=0) (bz:∀j < n,s.heap (B+j)=0):
    ∃t k,Executes n m netLoop s t k ∧ k ≤ 600*(n+1)^3 ∧
      (∀p:Fin n,t.heap (a+p.val)=if p∈Bits.net m W then 1 else 0) ∧
      (∀p:Fin n,t.heap (B+p.val)=if p∈W then 1 else 0) ∧
      (∀q,(q<a ∨ a+n ≤ q) → (q<B ∨ B+n ≤ q) → t.heap q=s.heap q) ∧
      t.output=s.output ∧ t.closed=s.closed:=by
  let P:=fun j (v:State)=>v.reg 6=1 ∧ v.reg 64=(n:ℤ) ∧ v.reg 71=(a:ℤ) ∧ v.reg 73=(B:ℤ) ∧
    v.reg 191=(b:ℤ) ∧ v.reg 192=s.reg 192 ∧ v.reg 193=s.reg 193 ∧ v.reg 195=(IntegerGeometry.unit n:ℤ) ∧
    (∀p:Fin n,v.heap (a+p.val)=if p∈retained m W j then 1 else 0) ∧
    (∀p:Fin n,v.heap (B+p.val)=if p.val < j ∧ p∈W then 1 else 0) ∧
    (∀q,(q<a ∨ a+n ≤ q) → (q<B ∨ B+n ≤ q) → v.heap q=s.heap q) ∧
    v.output=s.output ∧ v.closed=s.closed
  have zero:retained m W 0=∅:=by simp [retained,earlier]
  have start:P 0 (forSetup 194 656 64 s):=by
    refine ⟨one,sz,net,piece,base,rfl,rfl,scale,?_,?_,fun _ _ _=>rfl,rfl,rfl⟩
    · intro p;change s.heap _=_;simp [zero,az p.val p.isLt]
    · intro p;change s.heap _=_;simp [bz p.val p.isLt]
  have adv (i:ℕ) (hi:i < n) (v:State) (before:P i v) (idx:v.reg 194=(i:ℤ)) (_:v.reg 656=(n:ℤ)-1):
      ∃t k,Executes n m pointCode v t k ∧ k ≤ 500*(n+1)^2 ∧ t.reg 194=v.reg 194 ∧ t.reg 656=v.reg 656 ∧
        P (i+1) (t.assign 194 (t.reg 194+1)):=by
    let p:Fin n:=⟨i,hi⟩
    obtain ⟨u,sz',nt,pc,b',lab,live,unit',aa,bb,fr,out,cl⟩:=before
    obtain ⟨t,k,ex,tm,heap,o,f⟩:=point n a B b i (IntegerGeometry.unit n) m v hi space u sz' nt pc b' idx unit'
    have sel:(1 ≤ v.reg 193 ∧ wordAt m b i=v.reg 192) ↔ p∈W:=by rw [live,lab];exact (label p).symm
    simp only [sel] at heap
    have bits (z:Fin n) (_:z.val < p.val):1 ≤ v.heap (a+z.val) ↔ z∈retained m W p.val:=by
      rw [aa];by_cases e:z∈retained m W i <;> simp [p,e]
    have prior:p∉retained m W i:=fun e=>Nat.lt_irrefl _ (retained_from_prefix m W i p e).2
    refine ⟨t,k,ex,tm,ex.preserves _ (by decide),ex.preserves _ (by decide),
      (ex.preserves 6 (by decide)).trans u,(ex.preserves 64 (by decide)).trans sz',
      (ex.preserves 71 (by decide)).trans nt,(ex.preserves 73 (by decide)).trans pc,
      (ex.preserves 191 (by decide)).trans b',(ex.preserves 192 (by decide)).trans lab,
      (ex.preserves 193 (by decide)).trans live,(ex.preserves 195 (by decide)).trans unit',?_,?_,?_,o.trans out,f.trans cl⟩
    · intro z
      change t.heap (a+z.val)=(if z∈retained m W (p.val+1) then _ else _)
      rw [kept_bit m v.heap a W p z bits,heap]
      have off:a+z.val≠B+i:=by have hz:=z.isLt;omega
      by_cases wi:p∈W
      · rw [if_pos wi];by_cases eq:z=p
        · subst z;simp [p,wi]
        · have f:z.val≠i:=fun h=>eq (Fin.ext h)
          rw [Function.update_of_ne (show a+z.val≠a+i by omega),Function.update_of_ne off,aa z]
          simp [eq,p]
      · rw [if_neg wi,aa z];by_cases eq:z=p
        · subst z;simp [wi,prior]
        · simp [eq,p]
    · intro z
      change t.heap (B+z.val)=_
      rw [heap]
      have off:B+z.val≠a+i:=by omega
      by_cases wi:p∈W
      · rw [if_pos wi,Function.update_of_ne off]
        by_cases eq:z=p
        · subst z;have e:p.val=i:=rfl;simp [e,wi]
        · have ne:z.val≠i:=fun e=>eq (Fin.ext e)
          have same:z.val < i+1 ↔ z.val < i:=by omega
          rw [Function.update_of_ne (show B+z.val≠B+i by omega),bb z];simp [same]
      · rw [if_neg wi,bb z]
        by_cases eq:z=p
        · subst z;simp [wi]
        · have ne:z.val≠i:=fun e=>eq (Fin.ext e)
          have same:z.val < i+1 ↔ z.val < i:=by omega
          simp [same]
    · intro q ha hb;change t.heap q=s.heap q
      rw [heap];split
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)];exact fr q ha hb
      · exact fr q ha hb
  obtain ⟨t,k,ex,tm,_,_,_,_,_,_,_,_,aa,bb,frame,o,c⟩:=source_for (N:=n) (input:=m) 194 656 64 n
    (500*(n+1)^2) pointCode P (by decide) (by decide) s sz start adv
  refine ⟨t,k,ex,by ring_nf at tm ⊢ <;> omega,?_,?_,frame,o,c⟩
  · intro p;simpa only [retained_all] using aa p
  · intro p;simpa [p.isLt] using bb p
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM
open WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32000

/-- From the eleven initialized arrays, the first 23 commands build the active-vertex bitmap. -/
theorem initialized_net (x:World) (m:Store) (r h w:ℕ) (s:State)
    (hn:0 < x.n) (hr:r < x.rows*x.n) (ready:Ready x m) (prepared:Prepared x.n r h w s):
    let o:=offsets x.n (sizes x.n h)
    let W:=WindowProfiles.piece x (r/x.n) (r%x.n)
    ∃t k,Executes x.n m.imem (chain ((listOf src_build_geometry).take 23)) s t k ∧
      k ≤ 350*x.cap+601*(x.n+1)^3 ∧
      (∀p:Fin x.n,t.heap (cursorAt o 0+p.val)=if p∈Bits.net m.imem W then 1 else 0) ∧
      (∀p:Fin x.n,t.heap (cursorAt o 2+p.val)=if p∈W then 1 else 0) ∧
      (∀q,(q < cursorAt o 0 ∨ cursorAt o 0+x.n ≤ q) → (q < cursorAt o 2 ∨ cursorAt o 2+x.n ≤ q) →
        t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let o:=offsets x.n (sizes x.n h)
  let a:=cursorAt o 0
  let B:=cursorAt o 2
  let W:=WindowProfiles.piece x (r/x.n) (r%x.n)
  obtain ⟨one,_,sz,slot,_,_,_,_,_,_,_,ptrs,fresh',_,_⟩:=prepared
  obtain ⟨v,j,setup,jt,_,_,base,_,scale,member,heap,out,cl⟩:=geometry_start x.n r m.imem x.mem s hn one sz slot ready.2
  have row:r/x.n < x.rows:=(Nat.div_lt_iff_lt_mul hn).mpr hr
  have time:j ≤ 350*x.cap:=by dsimp [World.cap];omega
  have space:a+x.n ≤ B:=by simp [a,B,o,offsets,cursorAt] <;> omega
  have endB:B+x.n ≤ cursorAt o 11:=by simp [B,o,offsets,cursorAt] <;> omega
  have valid (p:Fin x.n):p∈W ↔ 1 ≤ v.reg 193 ∧ wordAt m.imem (labelBase x.n r) p.val=v.reg 192:=by
    have e:=member p;rw [base] at e;exact e
  have zero (q:ℕ) (small:q < cursorAt o 11):v.heap q=0:=by rw [heap];exact fresh' q small
  have ap:s.reg 71=(a:ℤ):=ptrs ⟨0,by decide⟩
  have bp:s.reg 73=(B:ℤ):=ptrs ⟨2,by decide⟩
  obtain ⟨t,k,net,kt,aa,bb,frame,output,closed⟩:=complete a B (labelBase x.n r) W m.imem v space
    ((setup.preserves 6 (by decide)).trans one) ((setup.preserves 64 (by decide)).trans sz)
    ((setup.preserves 71 (by decide)).trans ap) ((setup.preserves 73 (by decide)).trans bp) base scale valid
    (fun j hj=>zero _ (by omega)) (fun j hj=>zero _ (by omega))
  obtain ⟨c,pre,ce⟩:=splitChain ((listOf src_build_geometry).take 22) setup
  have full:Executes x.n m.imem (chain ((listOf src_build_geometry).take 23)) s t _:=pre.continue _ (.seq net (.skip _))
  refine ⟨t,_,full,by ring_nf at kt ⊢ <;> omega,aa,bb,?_,output.trans out,closed.trans cl⟩
  intro q ha hb;rw [frame q ha hb,heap]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM
open OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false

/-- At the end of the net sweep, the array already meets the precise active-bit
postcondition used by the row and root theorems. -/
theorem initialized_active (x : World) (m : Store) (r h w : ℕ) (s : State)
    (hn : 0 < x.n) (hr : r < x.rows*x.n) (ready : Ready x m) (prepared : Prepared x.n r h w s) :
    let d := integerData x.n x.mem m.imem r h
    let layout := offsets d.n (sizes d.n h)
    ∃ t k, Executes x.n m.imem (chain ((listOf src_build_geometry).take 23)) s t k ∧
      k ≤ 350*x.cap + 601*(x.n+1)^3 ∧
      (∀ j < d.n, 1 ≤ t.heap (cursorAt layout 0 + j) ↔ d.active j = true) ∧
      t.output = s.output ∧ t.closed = s.closed := by
  dsimp only
  obtain ⟨t,k,ex,time,net,_,_,out,closed⟩ := initialized_net x m r h w s hn hr ready prepared
  refine ⟨t,k,ex,time,?_,out,closed⟩
  intro j hj
  let p : Fin x.n := ⟨j,hj⟩
  change (1 ≤ t.heap (cursorAt (offsets x.n (sizes x.n h)) 0 + p.val)) ↔
    Bits.lookup (fun v : Fin x.n => decide (v ∈ Bits.net m.imem (Bits.piece x.n x.mem (r/x.n) (r%x.n)))) p.val false = true
  rw [net p]
  change (1 ≤ (if p ∈ Bits.net m.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) then (1:ℤ) else 0)) ↔ _
  by_cases hmem : p ∈ Bits.net m.imem (WindowProfiles.piece x (r/x.n) (r%x.n))
  · have same : p ∈ Bits.net m.imem (Bits.piece x.n x.mem (r/x.n) (r%x.n)) := hmem
    simp [Bits.lookup,p.isLt,hmem,same]
  · have same : p ∉ Bits.net m.imem (Bits.piece x.n x.mem (r/x.n) (r%x.n)) := hmem
    simp [Bits.lookup,p.isLt,hmem,same]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM

set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem solution (x:World) (m:Store) (r h w:ℕ) (s:Logical.State)
    (hn:0 < x.n) (hr:r < x.rows*x.n) (ready:Ready x m) (prepared:Logical.Prepared x.n r h w s):
    let o:=Logical.offsets x.n (Logical.sizes x.n h)
    let W:=WindowProfiles.piece x (r/x.n) (r%x.n)
    ∃t k,Logical.Executes x.n m.imem (Logical.chain ((Logical.listOf Logical.src_build_geometry).take 23)) s t k ∧
      k ≤ 350*x.cap+601*(x.n+1)^3 ∧
      (∀p:Fin x.n,t.heap (Logical.cursorAt o 0+p.val)=if p∈IntegerGeometry.Bits.net m.imem W then 1 else 0) ∧
      (∀p:Fin x.n,t.heap (Logical.cursorAt o 2+p.val)=if p∈W then 1 else 0) ∧
      (∀q,(q < Logical.cursorAt o 0 ∨ Logical.cursorAt o 0+x.n ≤ q) →
        (q < Logical.cursorAt o 2 ∨ Logical.cursorAt o 2+x.n ≤ q) → t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed := Logical.Scene.NetRAM.initialized_net x m r h w s hn hr ready prepared
