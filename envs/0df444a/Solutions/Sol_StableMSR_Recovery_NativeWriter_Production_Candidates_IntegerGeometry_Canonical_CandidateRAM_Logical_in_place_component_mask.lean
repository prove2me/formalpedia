-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.in_place_component_mask
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:42:08.368801+00:00
-- url     : https://prove2.me/submissions/4a224150-ded7-494c-8ef4-82c362e8d3f3

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

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open SingleCircuit TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 2000000
abbrev Seen := Finset ℕ
def rounds {A:Type} (f:A→A) (s:A) : ℕ→A
  | 0=>s | k+1=>f (rounds f s k)
theorem rounds_shift {A:Type} (f:A→A) (s:A) (k:ℕ) : rounds f s (k+1)=rounds f (f s) k:=by
  induction k with | zero=>rfl | succ k ih=>change f (rounds f s (k+1))=f (rounds f (f s) k);rw [ih]
theorem constant_rounds {A:Type} {f:A→A} {s:A} (h:f s=s) (k:ℕ) : rounds f s k=s:=by
  induction k with | zero=>rfl | succ k ih=>simp [rounds,ih,h]

theorem fixed_after (f:Seen→Seen) (U:Seen) (ext:∀s,s⊆U → s⊆f s) (cap:∀s,s⊆U → f s⊆U)
    (k:ℕ) (s:Seen) (hs:s⊆U) (enough:U.card ≤ s.card+k) : f (rounds f s k)=rounds f s k:=by
  induction k generalizing s with
  | zero=>
    have eq:s=U:=Finset.eq_of_subset_of_card_le hs (by omega)
    exact Finset.Subset.antisymm ((cap s hs).trans eq.symm.subset) (ext s hs)
  | succ k ih=>
    by_cases fix:f s=s
    · rw [constant_rounds fix];exact fix
    have lt:s.card<(f s).card:=by
      by_contra! le
      exact fix (Finset.eq_of_subset_of_card_le (ext s hs) le).symm
    rw [rounds_shift]
    exact ih (f s) (cap s hs) (by omega)

def advance (e:ℕ→ℕ→Bool) (U s:Seen) : Seen:=
  U.filter (fun u=>u∈s ∨ ∃z∈s,e z u=true)
@[simp] theorem mem_advance (e:ℕ→ℕ→Bool) (U s:Seen) (u:ℕ) :
  u∈advance e U s ↔ u∈U ∧ (u∈s ∨ ∃z∈s,e z u=true):=by classical simp [advance]

def mark (e:ℕ→ℕ→Bool) (s:Seen) (u:ℕ) : Seen:=
  if ∃z∈s,e z u=true then insert u s else s
def propagate (e:ℕ→ℕ→Bool) (us:List ℕ) (s:Seen):=us.foldl (mark e) s

theorem mark_ext (e:ℕ→ℕ→Bool) (s:Seen) (u:ℕ) : s⊆mark e s u:=by
  classical unfold mark;split <;> simp_all
theorem swept_ext (e:ℕ→ℕ→Bool) (us:List ℕ) (s:Seen) : s⊆propagate e us s:=by
  induction us generalizing s with
  | nil=>rfl
  | cons u us ih=>exact (mark_ext e s u).trans (ih _)

theorem swept_hits (e:ℕ→ℕ→Bool) (us:List ℕ) {u z:ℕ} (hu:u∈us) (s:Seen) (hz:z∈s) (edge:e z u=true) :
    u∈propagate e us s:=by
  classical
  induction us generalizing s with
  | nil=>simp at hu
  | cons a us ih=>
    rcases List.mem_cons.mp hu with eq|mem
    · subst a
      have put:u∈mark e s u:=by simp [mark,show ∃j∈s,e j u=true from ⟨z,hz,edge⟩]
      exact swept_ext e us _ put
    · exact ih mem _ (mark_ext e s a hz)

theorem swept_within (e:ℕ→ℕ→Bool) (U C:Seen) (closed:advance e U C⊆C)
    (us:List ℕ) (allow:∀u∈us,u∈U) (s:Seen) (start:s⊆C) : propagate e us s⊆C:=by
  classical
  induction us generalizing s with
  | nil=>exact start
  | cons u us ih=>
    apply ih (fun a ha=>allow a (by simp [ha]))
    unfold mark
    split
    · next yes=>
        obtain ⟨z,hz,edge⟩:=yes
        exact Finset.insert_subset (closed ((mem_advance ..).2 ⟨allow u (by simp),Or.inr ⟨z,start hz,edge⟩⟩)) start
    · exact start

theorem synchronous_asynchronous (e:ℕ→ℕ→Bool) (us:List ℕ) (s:Seen) (k:ℕ)
    (hs:s⊆us.toFinset) (enough:us.toFinset.card ≤ s.card+k) :
    rounds (propagate e us) s k=rounds (advance e us.toFinset) s k:=by
  classical
  let U:=us.toFinset
  let f:=advance e U
  have ex:∀a:Seen,a⊆U → a⊆f a:=by
    intro a sub i hi;exact (mem_advance ..).2 ⟨sub hi,Or.inl hi⟩
  have cap:∀a:Seen,a⊆U → f a⊆U:=by intro a _ i hi;exact ((mem_advance ..).1 hi).1
  have grows (j:ℕ) : s⊆rounds f s j ∧ rounds f s j⊆U:=by
    induction j with
    | zero=>exact ⟨Finset.Subset.rfl,hs⟩
    | succ j ih=>exact ⟨ih.1.trans (ex _ ih.2),cap _ ih.2⟩
  let C:=rounds f s k
  have stable:f C=C:=fixed_after f U ex cap k s hs enough
  have within (j:ℕ) : rounds (propagate e us) s j⊆C:=by
    induction j with
    | zero=>exact (grows k).1
    | succ j ih=>exact swept_within e U C stable.subset us (by simp [U]) _ ih
  have faster (j:ℕ) : rounds f s j⊆rounds (propagate e us) s j:=by
    induction j with
    | zero=>rfl
    | succ j ih=>
      intro u hu
      obtain ⟨allowed,h⟩:=(mem_advance ..).1 hu
      rcases h with seed|⟨z,hz,edge⟩
      · exact swept_ext e us _ (ih seed)
      · exact swept_hits e us (by simpa [U] using allowed) _ (ih hz) edge
  exact Finset.Subset.antisymm (within k) (faster k)

def passList (e:ℕ→ℕ→Bool) (us seen:List ℕ):=us.filter fun u=>seen.contains u || seen.any (fun z=>e z u)
theorem list_advance (e:ℕ→ℕ→Bool) (us seen:List ℕ) :
    (passList e us seen).toFinset=advance e us.toFinset seen.toFinset:=by
  classical ext u;simp [passList]
theorem ref_rounds (d:Instance) (us:List ℕ) (v k:ℕ) :
    ((List.range k).foldl (fun seen _=>passList d.edge us seen) [v]).toFinset =
      rounds (advance d.edge us.toFinset) {v} k:=by
  induction k with
  | zero=>simp [rounds]
  | succ k ih=>rw [List.range_succ,List.foldl_append];simp [rounds,list_advance,ih]
theorem restore_order (us:List ℕ) (p:ℕ→Bool) :
    us.filter (fun u=>decide (u∈(us.filter p).toFinset))=us.filter p:=by
  apply List.filter_congr
  intro u mem
  cases h:p u <;> simp [h,mem]

theorem ordered_component (d:Instance) (us:List ℕ) (v:ℕ) (hu:us.toFinset.card≤d.n) (hv:v∈us) (hn:0<d.n) :
    us.filter (fun u=>decide (u∈rounds (propagate d.edge us) {v} d.n))=TightLanguage.pieceAt d us v:=by
  classical
  have h:=synchronous_asynchronous d.edge us ({v}:Seen) d.n (by simpa using hv) (by simpa using (show us.toFinset.card≤1+d.n by omega))
  rw [h,←ref_rounds]
  obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d.n≠0)
  unfold TightLanguage.pieceAt
  rw [hk,List.range_succ,List.foldl_append]
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  change us.filter (fun u=>decide (u∈(passList d.edge us _).toFinset))=passList d.edge us _
  exact restore_order _ _
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open scoped Classical
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
def outsidePiece (m:ℕ → ℤ) (a p i:ℕ):Prop := 1 ≤ m (a+i) ∧ ¬1 ≤ m (p+i)
def onRim (m:ℕ → ℤ) (a p edge n i:ℕ):Prop := outsidePiece m a p i ∧ witnessed m p edge n i n
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
open scoped Classical
def reachBit:=chain [.op (.fetch 305 134 137),.op (.regular (.copy 304 305)),
  .cond 6 304 (chain [.op (.multiply 311 137 64),.op (.regular (.add 310 311 136)),
    .op (.fetch 308 75 310),.op (.regular (.copy 304 308))]) .skip,
  .cond 6 304 (chain [.op (.regular (.set 318 1)),.op (.save 134 136 318)]) .skip]
structure ReachArgs (n edge mask i:ℕ) (s:State):Prop where
  one:s.reg 6=1
  size:s.reg 64=(n:ℤ)
  ed:s.reg 75=(edge:ℤ)
  dst:s.reg 134=(mask:ℤ)
  row:s.reg 136=(i:ℤ)
theorem reach_bit (n edge mask i j:ℕ) (m:ℤ → ℤ) (s:State) (arg:ReachArgs n edge mask i s)
    (idx:s.reg 137=(j:ℤ)): ∃t k,Executes n m reachBit s t k ∧ k ≤ 230+6*n ∧
    (∀q,t.heap q=if q=mask+i ∧ sees s.heap mask edge n i j then 1 else s.heap q) ∧
    t.output=s.output ∧ t.closed=s.closed:=by
  classical
  obtain ⟨one,size,ed,dst,row⟩:=arg
  have sumNat (u v:ℕ):((u:ℤ)+v).toNat=u+v:=by omega
  have pos (u v:ℕ):0 ≤ (u:ℤ)+v:=by positivity
  have coord:(edge:ℤ)+((j:ℤ)*n+i)=((edge+(j*n+i):ℕ):ℤ):=by push_cast;rfl
  have coordinate:((edge:ℤ)+((j:ℤ)*n+i)).toNat=edge+(j*n+i):=congrArg Int.toNat coord
  have sign:0 ≤ (edge:ℤ)+((j:ℤ)*n+i):=by positivity
  have h:∃t k,evalLine n m reachBit s=some (t,k) ∧ k ≤ 230+6*n ∧
      (∀q,t.heap q=if q=mask+i ∧ sees s.heap mask edge n i j then 1 else s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed:=by
    by_cases point:1 ≤ s.heap (mask+j) <;> by_cases hit:1 ≤ s.heap (edge+(j*n+i)) <;>
      simp [reachBit,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,size,ed,dst,
        row,idx,sees,sumNat,pos,coordinate,sign,point,hit,Function.update_apply] <;> omega
  obtain ⟨t,k,ex,tm,heap,out,flag⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,heap,out,flag⟩

theorem reach_neighbours (n edge mask i:ℕ) (m:ℤ → ℤ) (s:State) (arg:ReachArgs n edge mask i s)
    :
    ∃t k,Executes n m (forCount 137 303 64 reachBit) s t k ∧ k ≤ 9+n*(235+6*n) ∧
    (∀q,t.heap q=if q=mask+i ∧ witnessed s.heap mask edge n i n then 1 else s.heap q) ∧
    t.output=s.output ∧ t.closed=s.closed:=by
  classical
  let P:=fun k (u:State)=>ReachArgs n edge mask i u ∧
    (∀q,u.heap q=if q=mask+i ∧ witnessed s.heap mask edge n i k then 1 else s.heap q) ∧
    u.output=s.output ∧ u.closed=s.closed
  have start:P 0 (forSetup 137 303 64 s):=by
    refine ⟨⟨arg.one,arg.size,arg.ed,arg.dst,arg.row⟩,?_,rfl,rfl⟩
    intro q;change s.heap q=_;simp [witnessed]
  have step (j:ℕ) (hj:j<n) (u:State) (good:P j u) (idx:u.reg 137=(j:ℤ)) (_:u.reg 303=(n:ℤ)-1):
      ∃t k,Executes n m reachBit u t k ∧ k ≤ 230+6*n ∧ t.reg 137=u.reg 137 ∧ t.reg 303=u.reg 303 ∧
        P (j+1) (t.assign 137 (t.reg 137+1)):=by
    obtain ⟨args,heap,out,cl⟩:=good
    obtain ⟨t,k,ex,tm,wrote,newout,newcl⟩:=reach_bit n edge mask i j m u args idx
    refine ⟨t,k,ex,tm,ex.preserves 137 (by decide),ex.preserves 303 (by decide),
      ⟨(ex.preserves 6 (by decide)).trans args.one,(ex.preserves 64 (by decide)).trans args.size,
       (ex.preserves 75 (by decide)).trans args.ed,
       (ex.preserves 134 (by decide)).trans args.dst,(ex.preserves 136 (by decide)).trans args.row⟩,
       ?_,newout.trans out,newcl.trans cl⟩
    intro q;change t.heap q=_
    rw [wrote]
    by_cases prev:witnessed s.heap mask edge n i j
    · by_cases atRow:q=mask+i <;> by_cases hit:sees u.heap mask edge n i j <;> simp [atRow,hit,heap,prev,witness_succ]
    · have noChange:u.heap=s.heap:=funext (fun w=>by simpa [prev] using heap w)
      rw [noChange];simp [prev,witness_succ]
  obtain ⟨t,k,ex,tm,_,heap,out,cl⟩:=source_for (N:=n) (input:=m) 137 303 64 n (230+6*n) reachBit P
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
def reachTest : List Program:=[.op (.fetch 295 132 136),.op (.regular (.copy 294 295)),
  .cond 6 294 (chain [.op (.fetch 299 134 136),
    .cond 6 299 (.op (.regular (.set 298 0))) (.op (.regular (.set 298 1))),
    .op (.regular (.copy 294 298))]) .skip]
def reachRow := chain (reachTest++[.cond 6 294 (forCount 137 303 64 reachBit) .skip])
theorem reach_test (n a p i:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1) (active:s.reg 132=(a:ℤ))
    (point:s.reg 134=(p:ℤ)) (row:s.reg 136=(i:ℤ)):
    ∃t k,Executes n m (chain reachTest) s t k ∧ k ≤ 158 ∧
      (1 ≤ t.reg 294 ↔ outsidePiece s.heap a p i) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
  have sumNat (u v:ℕ):((u:ℤ)+v).toNat=u+v:=by omega
  have pos (u v:ℕ):0 ≤ (u:ℤ)+v:=by positivity
  have h:∃t k,evalLine n m (chain reachTest) s=some (t,k) ∧ k ≤ 158 ∧
      (1 ≤ t.reg 294 ↔ outsidePiece s.heap a p i) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=by
    by_cases aa:1 ≤ s.heap (a+i) <;> by_cases pp:1 ≤ s.heap (p+i) <;>
      simp [reachTest,chain,evalLine,Operation.next,regularNext,State.assign,one,active,point,row,sumNat,pos,
        aa,pp,outsidePiece] <;> omega
  obtain ⟨t,k,ex,tm,val,heap,out,flag⟩:=h
  exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,val,heap,out,flag⟩
theorem reach_row (n a edge mask i:ℕ) (m:ℤ → ℤ) (s:State) (arg:ReachArgs n edge mask i s)
    (active:s.reg 132=(a:ℤ)):
    ∃t k,Executes n m reachRow s t k ∧ k ≤ 175+n*(235+6*n) ∧
      (∀q,t.heap q=if q=mask+i ∧ onRim s.heap a mask edge n i then 1 else s.heap q) ∧
      t.output=s.output ∧ t.closed=s.closed:=by
  obtain ⟨u,k,test,tm,flag,heap,out,cl⟩:=reach_test n a mask i m s arg.one active arg.dst arg.row
  obtain ⟨z,front,time⟩:=splitChain reachTest test
  have args:ReachArgs n edge mask i u:=
    ⟨(test.preserves 6 (by decide)).trans arg.one,(test.preserves 64 (by decide)).trans arg.size,
     (test.preserves 75 (by decide)).trans arg.ed,
     (test.preserves 134 (by decide)).trans arg.dst,(test.preserves 136 (by decide)).trans arg.row⟩
  let guard:=Program.cond 6 294 (forCount 137 303 64 reachBit) .skip
  obtain ⟨t,c,branch,cc,memory,output,closed⟩:∃t c,Executes n m guard u t c ∧ c ≤ 10+n*(235+6*n) ∧
      (∀q,t.heap q=if q=mask+i ∧ onRim s.heap a mask edge n i then 1 else s.heap q) ∧
      t.output=s.output ∧ t.closed=s.closed:=by
    by_cases hit:outsidePiece s.heap a mask i
    · obtain ⟨t,c,run,ct,mem,ot,closed⟩:=reach_neighbours n edge mask i m u args
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
open SingleCircuit TightLanguage
abbrev VertexSet:=Finset ℕ
structure Painted (m:ℕ → ℤ) (n top:ℕ) (S:VertexSet) (u:State) : Prop where
  small : ∀j∈S,j<n
  bits : ∀j<n,u.heap (top+j)=(if j∈S then 1 else 0)
  frame : ∀q,q<top ∨ top+n ≤ q → u.heap q=m q
def selected (m:ℕ → ℤ) (a i:ℕ):Bool:=decide (1 ≤ m (a+i))
noncomputable def stepSet (m:ℕ → ℤ) (a:ℕ) (edge:ℕ → ℕ → Bool) (i:ℕ) (S:VertexSet):VertexSet:=
  if selected m a i then Enumeration.mark edge S i else S
def sweepSet (m:ℕ → ℤ) (a:ℕ) (edge:ℕ → ℕ → Bool) (i:ℕ) (S:VertexSet):VertexSet:=
  ((List.range i).filter (selected m a)).foldl (Enumeration.mark edge) S
theorem sweep_next (m:ℕ → ℤ) (a:ℕ) (edge:ℕ → ℕ → Bool) (i:ℕ) (S:VertexSet):
    sweepSet m a edge (i+1) S=stepSet m a edge i (sweepSet m a edge i S):=by
  unfold sweepSet stepSet;rw [List.range_succ,List.filter_append,List.foldl_append];cases h:selected m a i <;> simp [h]

theorem Painted.positive {m n top S u} (p:Painted m n top S u) (j:ℕ) (lt:j<n):
    1 ≤ u.heap (top+j) ↔ j∈S:=by rw [p.bits j lt];split_ifs <;> simp_all
theorem paint_step {n a ed top i:ℕ} (m:ℕ → ℤ) (edge:ℕ → ℕ → Bool) (u t:State) (S:VertexSet)
    (old:Painted m n top S u) (aa:a+n ≤ top) (ee:ed+n*n ≤ top) (hi:i<n)
    (arcs:∀j<n,∀v<n,1 ≤ m (ed+(j*n+v)) ↔ edge j v=true)
    (wrote:∀q,t.heap q=if q=top+i ∧ onRim u.heap a top ed n i then 1 else u.heap q):
    Painted m n top (stepSet m a edge i S) t:=by
  classical
  have agrees (j:ℕ) (hj:j<n):sees u.heap top ed n i j ↔ j∈S ∧ edge j i=true:=by
    have le: (j+1)*n ≤ n*n:=Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at le
    unfold sees;rw [old.positive _ hj,old.frame _ (.inl (by omega)),arcs _ hj _ hi]
  have wit:witnessed u.heap top ed n i n ↔ ∃j∈S,edge j i=true:=by
    constructor
    · rintro ⟨j,lt,hit⟩;exact ⟨j,(agrees j lt).mp hit⟩
    · rintro ⟨j,inS,forward⟩;have lt:=old.small j inS;exact ⟨j,lt,(agrees j lt).mpr ⟨inS,forward⟩⟩
  have gate:onRim u.heap a top ed n i ↔ ((1 ≤ m (a+i)) ∧ i∉S) ∧ ∃j∈S,edge j i=true:=by
    unfold onRim outsidePiece;rw [wit,old.positive i hi,old.frame _ (.inl (by omega))]
  refine ⟨?_,?_,?_⟩
  · intro j hj;unfold stepSet Enumeration.mark at hj
    split_ifs at hj
    · rcases Finset.mem_insert.mp hj with eq|oldj
      · exact eq ▸ hi
      · exact old.small j oldj
    all_goals exact old.small j hj
  · intro j lt
    rw [wrote,gate,old.bits j lt]
    by_cases sel:1 ≤ m (a+i) <;> by_cases marked:i∈S <;> by_cases hit:(∃v∈S,edge v i=true) <;>
      by_cases eq:j=i <;> simp [stepSet,selected,Enumeration.mark,sel,marked,hit,eq]
  · intro q off;rw [wrote,if_neg (by rintro ⟨eq,_⟩;omega),old.frame q off]
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open scoped Classical
open SingleCircuit TightLanguage
structure GraphRegs (n allow edge top:ℕ) (s:State):Prop where
  unit : s.reg 6=1
  size : s.reg 64=(n:ℤ)
  allowed : s.reg 132=(allow:ℤ)
  matrix : s.reg 75=(edge:ℤ)
  seen : s.reg 134=(top:ℤ)
  free : s.reg 8=((top+n:ℕ):ℤ)
def holdsGraph (p:Program):Bool:=[6,64,132,75,134,8].all (fun j=>!(writesReg j p))
theorem GraphRegs.kept {N input p s t z n a ed top} (args:GraphRegs n a ed top s) (run:Executes N input p s t z)
    (ok:holdsGraph p=true):GraphRegs n a ed top t:=by
  simp [holdsGraph] at ok
  obtain ⟨a6,a64,a132,a75,a134,a8⟩:=ok
  exact ⟨(run.preserves _ a6).trans args.unit,(run.preserves _ a64).trans args.size,
    (run.preserves _ a132).trans args.allowed,(run.preserves _ a75).trans args.matrix,
    (run.preserves _ a134).trans args.seen,(run.preserves _ a8).trans args.free⟩
theorem sweep_run (n a ed top:ℕ) (input:ℤ → ℤ) (m:ℕ → ℤ) (edge:ℕ → ℕ → Bool)
    (u:State) (S:VertexSet) (regs:GraphRegs n a ed top u) (paint:Painted m n top S u)
    (aa:a+n ≤ top) (ee:ed+n*n ≤ top) (graph:∀j<n,∀v<n,1 ≤ m (ed+(j*n+v)) ↔ edge j v=true):
    ∃t k,Executes n input (forCount 136 293 64 reachRow) u t k ∧
      k ≤ 9+n*(180+n*(235+6*n)) ∧ GraphRegs n a ed top t ∧
      Painted m n top (sweepSet m a edge n S) t ∧ t.output=u.output ∧ t.closed=u.closed:=by
  let P:=fun i (v:State)=>GraphRegs n a ed top v ∧ Painted m n top (sweepSet m a edge i S) v ∧
    v.output=u.output ∧ v.closed=u.closed
  have start:P 0 (forSetup 136 293 64 u):=by
    refine ⟨⟨regs.unit,regs.size,regs.allowed,regs.matrix,regs.seen,regs.free⟩,⟨paint.small,paint.bits,paint.frame⟩,rfl,rfl⟩
  have step (i:ℕ) (hi:i<n) (v:State) (good:P i v) (idx:v.reg 136=(i:ℤ)) (_:v.reg 293=(n:ℤ)-1):
      ∃t k,Executes n input reachRow v t k ∧ k ≤ 175+n*(235+6*n) ∧ t.reg 136=v.reg 136 ∧ t.reg 293=v.reg 293 ∧
        P (i+1) (t.assign 136 (t.reg 136+1)):=by
    obtain ⟨rr,old,out,closed⟩:=good
    obtain ⟨t,k,ex,tm,wrote,ot,flag⟩:=reach_row n a ed top i input v
      ⟨rr.unit,rr.size,rr.matrix,rr.seen,idx⟩ rr.allowed
    have ng:=rr.kept ex (by decide)
    have np:=paint_step m edge v t _ old aa ee hi graph wrote
    rw [←sweep_next] at np
    exact ⟨t,k,ex,tm,ex.preserves 136 (by decide),ex.preserves 293 (by decide),
      ⟨ng.unit,ng.size,ng.allowed,ng.matrix,ng.seen,ng.free⟩,⟨np.small,np.bits,np.frame⟩,ot.trans out,flag.trans closed⟩
  obtain ⟨t,k,ex,tm,good⟩:=source_for (N:=n) (input:=input) 136 293 64 n (175+n*(235+6*n)) reachRow P
    (by decide) (by decide) u regs.size start step
  exact ⟨t,k,ex,by simpa only [show 175+n*(235+6*n)+5=180+n*(235+6*n) by omega] using tm,good⟩

theorem rounds_run (n a ed top:ℕ) (input:ℤ → ℤ) (m:ℕ → ℤ) (edge:ℕ → ℕ → Bool)
    (s:State) (S:VertexSet) (regs:GraphRegs n a ed top s) (paint:Painted m n top S s)
    (aa:a+n ≤ top) (ee:ed+n*n ≤ top) (graph:∀j<n,∀v<n,1 ≤ m (ed+(j*n+v)) ↔ edge j v=true):
    ∃t k,Executes n input (forCount 135 291 64 (forCount 136 293 64 reachRow)) s t k ∧
      k ≤ 9+n*(14+n*(180+n*(235+6*n))) ∧ GraphRegs n a ed top t ∧
      Painted m n top (Enumeration.rounds (sweepSet m a edge n) S n) t ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let P:=fun i (v:State)=>GraphRegs n a ed top v ∧ Painted m n top (Enumeration.rounds (sweepSet m a edge n) S i) v ∧
    v.output=s.output ∧ v.closed=s.closed
  have start:P 0 (forSetup 135 291 64 s):=
    ⟨⟨regs.unit,regs.size,regs.allowed,regs.matrix,regs.seen,regs.free⟩,⟨paint.small,paint.bits,paint.frame⟩,rfl,rfl⟩
  have step (i:ℕ) (_:i<n) (v:State) (good:P i v) (_:v.reg 135=(i:ℤ)) (_:v.reg 291=(n:ℤ)-1):
      ∃t k,Executes n input (forCount 136 293 64 reachRow) v t k ∧ k ≤ 9+n*(180+n*(235+6*n)) ∧
        t.reg 135=v.reg 135 ∧ t.reg 291=v.reg 291 ∧ P (i+1) (t.assign 135 (t.reg 135+1)):=by
    obtain ⟨rr,pp,out,closed⟩:=good
    obtain ⟨t,k,ex,tm,ng,np,ot,flag⟩:=sweep_run n a ed top input m edge v _ rr pp aa ee graph
    exact ⟨t,k,ex,tm,ex.preserves 135 (by decide),ex.preserves 291 (by decide),
      ⟨ng.unit,ng.size,ng.allowed,ng.matrix,ng.seen,ng.free⟩,⟨np.small,np.bits,np.frame⟩,ot.trans out,flag.trans closed⟩
  obtain ⟨t,k,ex,tm,good⟩:=source_for (N:=n) (input:=input) 135 291 64 n (9+n*(180+n*(235+6*n)))
    (forCount 136 293 64 reachRow) P (by decide) (by decide) s regs.size start step
  exact ⟨t,k,ex,by simpa only [show 9+n*(180+n*(235+6*n))+5=14+n*(180+n*(235+6*n)) by omega] using tm,good⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open scoped Classical
open SingleCircuit TightLanguage
theorem selected_component (d:Instance) (m:ℕ → ℤ) (a seed:ℕ) (hs:seed<d.n) (mark:1 ≤ m (a+seed)) :
    let vs:=(List.range d.n).filter (selected m a)
    let S:=Enumeration.rounds (sweepSet m a d.edge d.n) {seed} d.n
    ∀j,j∈S ↔ j∈pieceAt d vs seed:=by
  classical
  let vs:=(List.range d.n).filter (selected m a)
  have inside:seed∈vs:=by simp [vs,selected,hs,mark]
  have cap:vs.toFinset.card ≤ d.n:=calc
    _ ≤ (Finset.range d.n).card:=Finset.card_le_card (by intro j hj;exact Finset.mem_range.mpr (List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hj)).1))
    _ = _:=Finset.card_range _
  have sub (k:ℕ):Enumeration.rounds (Enumeration.propagate d.edge vs) {seed} k ⊆ vs.toFinset:=by
    induction k with
    | zero=>simpa [Enumeration.rounds] using inside
    | succ k ih=>
      exact Enumeration.swept_within d.edge vs.toFinset vs.toFinset (fun j h=>(Enumeration.mem_advance ..).1 h |>.1)
        vs (fun _ h=>List.mem_toFinset.mpr h) _ ih
  have out:=Enumeration.ordered_component d vs seed cap inside (by omega)
  change ∀j:ℕ,j∈Enumeration.rounds (Enumeration.propagate d.edge vs) {seed} d.n ↔ j∈pieceAt d vs seed
  intro j
  rw [←out];simp only [List.mem_filter,decide_eq_true_eq]
  exact ⟨fun h=>⟨List.mem_toFinset.mp (sub d.n h),h⟩,And.right⟩

theorem component_scan (d:Instance) (a ed top seed:ℕ) (input:ℤ → ℤ) (s:State)
    (one:s.reg 6=1) (zero:s.reg 7=0) (size:s.reg 64=(d.n:ℤ)) (cursor:s.reg 8=(top:ℤ))
    (allow:s.reg 132=(a:ℤ)) (entry:s.reg 133=(seed:ℤ)) (edges:s.reg 75=(ed:ℤ))
    (aa:a+d.n ≤ top) (ee:ed+d.n*d.n ≤ top) (hs:seed<d.n) (mark:1 ≤ s.heap (a+seed))
    (graph:∀j<d.n,∀v<d.n,1 ≤ s.heap (ed+(j*d.n+v)) ↔ d.edge j v=true):
    let vs:=(List.range d.n).filter (fun j=>decide (1 ≤ s.heap (a+j)))
    ∃t k,Executes d.n input src_component s t k ∧ k ≤ 640*(d.n+1)^4 ∧ t.reg 138=(top:ℤ) ∧
      t.reg 8=((top+d.n:ℕ):ℤ) ∧ (∀j<d.n,t.heap (top+j)=if j∈pieceAt d vs seed then 1 else 0) ∧
      (∀q,q<top ∨ top+d.n ≤ q → t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed:=by
  let n:=d.n
  let u:=((s.clear top n).assign 284 (top:ℤ)).assign 8 ((top+n:ℕ):ℤ)
  let v:=u.assign 134 (top:ℤ)
  let w:=v.assign 289 1
  let x:=w.save (top+seed) 1
  have al:Executes n input (.op (.alloc 284 64)) s u (64*(1+n)):=op_alloc s _ _ _ _ one zero cursor size
  have ptr:Executes n input (.op (.regular (.copy 134 284))) u v 1:=op_copy u _ _ _ (by simp [u,State.assign])
  have set:Executes n input (.op (.regular (.set 289 1))) v w 1:=.op rfl
  have write:Executes n input (.op (.save 134 133 289)) w x 64:=by
    apply Executes.op
    have adr:((top:ℤ)+seed).toNat=top+seed:=by omega
    have pos:0 ≤ (top:ℤ)+seed:=by positivity
    simp [Operation.next,w,v,u,x,State.assign,State.clear,entry,adr,pos]
  have ng:GraphRegs n a ed top x:=⟨one,size,allow,edges,rfl,rfl⟩
  have seedPaint:Painted s.heap n top {seed} x:=by
    refine ⟨by simpa using hs,?_,?_⟩
    · intro j hj
      change Function.update (fun q=>if top ≤ q ∧ q<top+n then 0 else s.heap q) (top+seed) 1 (top+j)=_
      by_cases eq:j=seed <;> simp [Function.update_apply,eq,hj]
    · intro q off
      change Function.update (fun q=>if top ≤ q ∧ q<top+n then 0 else s.heap q) (top+seed) 1 q=_
      have hn:seed<n:=hs
      rw [Function.update_of_ne (by intro eq;omega),if_neg (by omega)]
  obtain ⟨t,k,run,tm,regs,paint,out,flag⟩:=rounds_run n a ed top input s.heap d.edge x {seed} ng seedPaint aa ee graph
  let z:=t.assign 138 (top:ℤ)
  have ret:Executes n input (.op (.regular (.copy 138 134))) t z 1:=op_copy _ _ _ _ regs.seen
  refine ⟨z,_,.seq al (.seq ptr (.seq set (.seq write (.seq run (.seq ret (.skip _)))))),?_,
    by simp [z,State.assign],regs.free,?_,paint.frame,out,flag⟩
  · change _ ≤ 640*(n+1)^4;ring_nf at tm ⊢ <;> omega
  · intro j hj;change t.heap (top+j)=_
    change t.heap (top+j)=(if j∈pieceAt d ((List.range d.n).filter (selected s.heap a)) seed then 1 else 0)
    have eq:=selected_component d s.heap a seed hs mark j
    have value:=paint.bits j hj
    change t.heap (top+j)=(if j∈Enumeration.rounds (sweepSet s.heap a d.edge d.n) {seed} d.n then 1 else 0) at value
    by_cases h:j∈Enumeration.rounds (sweepSet s.heap a d.edge d.n) {seed} d.n
    · simpa only [if_pos h,if_pos (eq.mp h)] using value
    · simpa only [if_neg h,if_neg (fun bad=>h (eq.mpr bad))] using value
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem solution (d:Instance) (a ed top seed:ℕ) (input:ℤ → ℤ) (s:Logical.State)
    (one:s.reg 6=1) (zero:s.reg 7=0) (size:s.reg 64=(d.n:ℤ)) (cursor:s.reg 8=(top:ℤ))
    (allow:s.reg 132=(a:ℤ)) (entry:s.reg 133=(seed:ℤ)) (edges:s.reg 75=(ed:ℤ))
    (aa:a+d.n ≤ top) (ee:ed+d.n*d.n ≤ top) (hs:seed<d.n) (mark:1 ≤ s.heap (a+seed))
    (graph:∀j<d.n,∀v<d.n,1 ≤ s.heap (ed+(j*d.n+v)) ↔ d.edge j v=true):
    let vs:=(List.range d.n).filter (fun j=>decide (1 ≤ s.heap (a+j)))
    ∃t k,Logical.Executes d.n input src_component s t k ∧ k ≤ 640*(d.n+1)^4 ∧ t.reg 138=(top:ℤ) ∧
      t.reg 8=((top+d.n:ℕ):ℤ) ∧ (∀j<d.n,t.heap (top+j)=if j∈TightLanguage.pieceAt d vs seed then 1 else 0) ∧
      (∀q,q<top ∨ top+d.n ≤ q → t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed := Logical.component_scan d a ed top seed input s one zero size cursor allow entry edges aa ee hs mark graph
